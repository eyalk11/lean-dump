/-
lean-dump audit exporter (template). Copy to `scripts/lean_audit_exporter.lean`
in your project and fill in the three `EDIT` points. Run through
`scripts/run_lean_audit.py` (templates/run_lean_audit.py), or directly:

    LEAN_DUMP_AUDIT_EMIT=1 lake env lean scripts/lean_audit_exporter.lean

Two checks, both of which a green `lake build` gives you nothing on:

1. SORRY CONFINEMENT.  `sorry` may only be *written* in the declared
   placeholder files -- anything matching `*_deps`, plus the modules listed in
   `allowedSorryModules`.  This is a semantic check, not a grep: it looks for
   `sorryAx` occurring directly in a declaration's own type or value.  A
   theorem that cites a lemma from a `_deps` file inherits `sorryAx`
   *transitively*; that is not a finding here (it shows up in the footprint).

2. AXIOM CLEANLINESS.  Declarations named in `lean/axiom_clean.txt` must
   depend on nothing beyond `propext`, `Classical.choice`, `Quot.sound`.
   A missing or empty list makes the check a no-op.

LEAN_DUMP_AUDIT_REPORT=1 prints every project declaration that is currently
axiom-clean (how you populate `axiom_clean.txt`).

LEAN_DUMP_AUDIT_EMIT=1 writes, into $LEAN_DUMP_AUDIT_DIR (default `lean`):

  axiom_footprint.json     per declaration:
     "axioms"   the non-benign axioms the *proof* rests on (`sorryAx` reached
                through a `_deps` module, or a project axiom);
     "assumes"  the provenance-prefixed names (CONJ_ / UNPROVED / EXT_) the
                *statement* is conditional on.
  declaration_details.json per declaration: pretty type, expanded type,
     binders, compiled dependencies.

Both fields must be empty for a declaration to be unconditional.
-/

-- EDIT 1: import every root of your Lean library (keep in sync with `roots`
-- in lakefile.toml; a root not imported here is silently unaudited).
import MyProject

import Lean

open Lean Meta

namespace LeanDumpAudit

/-- Modules whose declarations are allowed to contain `sorry`. Anything whose
name ends in `_deps` is allowed implicitly; these are the named exceptions. -/
-- EDIT 2: modules allowed to contain `sorry` besides `*_deps`
-- (e.g. a conjectures module, an external-theorems module).
def allowedSorryModules : Array Name :=
  #[]

/-- The axioms every ordinary Mathlib proof rests on. Anything else in a
declaration's footprint is a finding. -/
def benignAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

-- EDIT 3: which modules are yours. Match every root of the library -- a root
-- this misses is silently outside both checks and the footprint.
def projectModulePrefixes : Array String := #["MyProject", "my_project_"]

/-- Is this module one of ours? -/
def isProjectModule (m : Name) : Bool :=
  let s := m.toString
  projectModulePrefixes.any fun p => s == p || s.startsWith p

def sorryAllowed (m : Name) : Bool :=
  allowedSorryModules.contains m || m.toString.endsWith "_deps"

/-- The declaration's body. `ConstantInfo.value?` returns `none` for theorems --
proof terms are not handed out through it -- so `.thmInfo` has to be matched
explicitly. Getting this wrong makes the sorry check silently vacuous on every
theorem in the library, which is most of it. -/
def declValue? : ConstantInfo → Option Expr
  | .thmInfo tv => some tv.value
  | ci          => ci.value?

/-- Does this declaration *itself* contain a hole, as opposed to inheriting one
from something it cites? -/
def hasDirectSorry (ci : ConstantInfo) : Bool :=
  let hit (e : Expr) : Bool := e.isConstOf ``sorryAx
  (ci.type.find? hit).isSome || ((declValue? ci).bind (·.find? hit)).isSome

/-- Declarations Lean generates for you (`_proof_1`, match equations, ...).
Reporting them just duplicates the parent declaration. -/
def isNoise (n : Name) : Bool :=
  n.isInternal || n.hasMacroScopes

/-- Every declaration defined in a project module, paired with that module. -/
def projectDecls (env : Environment) : Array (Name × Name) := Id.run do
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut out := #[]
  for i in [0 : mods.size] do
    let m := mods[i]!
    if isProjectModule m then
      for n in data[i]!.constNames do
        unless isNoise n do
          out := out.push (n, m)
  return out

def readAxiomCleanList : IO (Array Name) := do
  let path : System.FilePath := "lean" / "axiom_clean.txt"
  if !(← path.pathExists) then return #[]
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return lines.foldl (init := #[]) fun acc raw =>
    let l := raw.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then acc else acc.push l.toName

/-- The provenance prefixes required on anything unproved: `CONJ_` for a
live conjecture, `UNPROVED` for an unproved internal claim, `EXT_` for a
theorem imported from a verified external package. -/
def provenancePrefixes : Array String := #["CONJ_", "UNPROVED", "EXT_"]

def isProvenanceName (n : Name) : Bool :=
  (n.toString.splitOn ".").any fun part => provenancePrefixes.any (fun p : String => part.startsWith p)

/-- The provenance-prefixed constants occurring in a declaration's
**hypotheses**.

This is conditionality, and it is a different question from the axiom
footprint. `theorem foo (h : CONJ_x f) : P f` is proved, has a perfectly
clean axiom footprint, and establishes nothing until someone proves CONJ_x.
That is the *preferred* shape for an unproved dependency -- "an explicit
theorem hypothesis by default, not a new axiom, global declaration, or `by
sorry`" -- and therefore exactly the shape an axiom check is blindest to.
Scanning the hypotheses is what sees it.

**Only the binder domains are scanned, never the conclusion**, and that
distinction is the whole point rather than an optimisation.  A theorem whose
conclusion names a provenance-prefixed `Prop` is the theorem that *discharges*
it:

    theorem readone_terminal : UNPROVED_readone_terminal := ...

Counting that as an assumption inverts the reading.  An earlier version scanned
the entire type, so every discharged `UNPROVED_` Prop in the library was listed
as conditional on the very Prop it proves -- which would mark every discharged
proposition as conditional on itself.

Walking the binders needs no `MetaM`: a `∀`/`→` is `Expr.forallE`, its domain
is the hypothesis and its body the rest, so the recursion below collects
domains and drops whatever the chain ends in.  A hypothesis buried inside
another hypothesis's type is still seen, because `getUsedConstants` on a domain
is not itself restricted.

It inherits the limit of the convention it reads: a hypothesis whose type is
named `Conjecture` rather than `CONJ_conjecture` is invisible here.  The
prefixes are a convention, not something the compiler enforces. -/
partial def hypothesisConstants : Expr → Array Name
  | .forallE _ d b _ => (d.getUsedConstants ++ hypothesisConstants b)
  | .letE _ t v b _  => (t.getUsedConstants ++ v.getUsedConstants
                          ++ hypothesisConstants b)
  | .mdata _ e       => hypothesisConstants e
  | _                => #[]

def assumedNames (ci : ConstantInfo) : Array Name :=
  (hypothesisConstants ci.type).foldl (init := #[]) fun acc n =>
    if isProvenanceName n && !acc.contains n then acc.push n else acc

/-- Direct compiled references, expanding compiler-generated helper declarations.
Ordinary public helpers remain separate rows in the exported project graph.
Both types and proof bodies count; this is not a source-text approximation. -/
def compiledDependencies (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let constants (info : ConstantInfo) :=
    info.type.getUsedConstants ++ ((declValue? info).map Expr.getUsedConstants).getD #[]
  let mut pending := constants ci
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    if isNoise n then
      if let some helper := env.find? n then
        pending := pending ++ constants helper
    else
      out := out.push n
  return out.qsort Name.lt

/-- Elaborated binder types, including anonymous arrows, section variables,
implicit hypotheses and proposition-valued instances. Normal parameters are
retained too, so the display never has to guess from a variable's spelling.
Reducing the telescope also exposes hypotheses inside a named proposition. -/
def declarationDetails (n : Name) : MetaM Json := do
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown declaration {n}"
  let typeText ← withOptions (·.setBool `pp.fullNames true) do
    return (← ppExpr ci.type).pretty
  let (binders, expandedTypeText) ← forallTelescopeReducing ci.type fun xs body => do
    let expanded ← mkForallFVars xs body
    let expandedText ← withOptions (·.setBool `pp.fullNames true) do
      return (← ppExpr expanded).pretty
    let binders ← xs.mapM fun x => do
      let localDecl ← x.fvarId!.getDecl
      let text ← withOptions (·.setBool `pp.fullNames true) do
        return (← ppExpr localDecl.type).pretty
      let kind := match localDecl.binderInfo with
        | .default => "explicit"
        | .implicit => "implicit"
        | .strictImplicit => "strict implicit"
        | .instImplicit => "instance"
      return Json.mkObj [
        ("name", Json.str localDecl.userName.toString),
        ("type", Json.str text),
        ("binder", Json.str kind),
        ("is_proposition", Json.bool (← isProp localDecl.type))]
    return (binders, expandedText)
  return Json.mkObj [
    ("type", Json.str typeText),
    ("expanded_type", Json.str expandedTypeText),
    ("binders", Json.arr binders),
    ("dependencies", Json.arr ((compiledDependencies env ci).map (Json.str ∘ Name.toString)))]

def auditDirectory : IO System.FilePath := do
  return (← IO.getEnv "LEAN_DUMP_AUDIT_DIR").getD "lean"

/-- Write the exhaustive per-declaration footprint.

Two fields, because two different things go wrong. `axioms` is what the
*proof* rests on: `sorryAx` from a `_deps` hole, or a project axiom. `assumes`
is what the *statement* is conditional on. A declaration is unconditional only
when both are empty, and neither field implies the other -- a conditional
theorem is usually axiom-clean, and a `_deps` consumer usually assumes nothing
in its own statement.

One line per declaration so the checked-in file diffs readably; sorted so the
order does not depend on module-loading order. Names are Lean identifiers, so
they need no JSON escaping. -/
def writeFootprint (rows : Array (Name × Array Name × Array Name)) : IO Unit := do
  let sorted := rows.qsort (fun a b => a.1.lt b.1)
  let quoted := fun (n : Name) => "\"" ++ toString n ++ "\""
  let list := fun (ns : Array Name) =>
    "[" ++ String.intercalate ", " ((ns.map quoted).toList) ++ "]"
  let entry := fun (n : Name) (ax : Array Name) (asm : Array Name) =>
    "  " ++ quoted n ++ ": {\"axioms\": " ++ list ax ++ ", \"assumes\": " ++ list asm ++ "}"
  let body := String.intercalate ",\n"
    ((sorted.map (fun (n, ax, asm) => entry n ax asm)).toList)
  let path := (← auditDirectory) / "axiom_footprint.json"
  IO.FS.writeFile path ("{\n" ++ body ++ "\n}\n")
  IO.println s!"wrote {path} ({sorted.size} declarations)"

end LeanDumpAudit

open LeanDumpAudit in
#eval show MetaM Unit from do
  let env ← getEnv
  let decls := projectDecls env
  let report := (← IO.getEnv "LEAN_DUMP_AUDIT_REPORT").isSome

  -- 1. sorry confinement
  let mut stray : Array (Name × Name) := #[]
  for (n, m) in decls do
    unless sorryAllowed m do
      if let some ci := env.find? n then
        if hasDirectSorry ci then
          stray := stray.push (n, m)

  -- 2. axiom cleanliness of the declared-unconditional results
  let claimed ← readAxiomCleanList
  let mut missing : Array Name := #[]
  let mut dirty : Array (Name × Array Name) := #[]
  for n in claimed do
    if !env.contains n then
      missing := missing.push n
    else
      let ax ← collectAxioms n
      let bad := ax.filter (!benignAxioms.contains ·)
      unless bad.isEmpty do
        dirty := dirty.push (n, bad)

  -- The report and the footprint both need every declaration's axiom set, so
  -- collect it once when either is asked for: `collectAxioms` over the whole
  -- library is the expensive part of this script.
  let emit := (← IO.getEnv "LEAN_DUMP_AUDIT_EMIT").isSome
  let mut footprint : Array (Name × Array Name × Array Name) := #[]
  let mut details : List (String × Json) := []
  if report || emit then
    if report then
      IO.println s!"-- {decls.size} declarations in project modules"
    for (n, _) in decls do
      let ax ← collectAxioms n
      let bad := ax.filter (!benignAxioms.contains ·)
      if report && bad.isEmpty then
        IO.println n
      let asm := match env.find? n with
        | some ci => assumedNames ci
        | none    => #[]
      footprint := footprint.push (n, bad, asm)
      if emit then
        details := (n.toString, ← declarationDetails n) :: details

  let mut errs : Array String := #[]
  unless stray.isEmpty do
    let body := String.intercalate "\n" <|
      (stray.map fun (n, m) => s!"  {n}    (in {m})").toList
    errs := errs.push
      s!"`sorry` outside the declared placeholder files ({stray.size}):\n{body}\n\
         Move the hole into a `*_deps` module, or add the module to \
         allowedSorryModules if it is genuinely a declared exception."
  unless missing.isEmpty do
    let body := String.intercalate "\n" ((missing.map (s!"  {·}")).toList)
    errs := errs.push
      s!"lean/axiom_clean.txt names declarations that do not exist ({missing.size}):\n{body}\n\
         They were renamed or removed; fix the list."
  unless dirty.isEmpty do
    let body := String.intercalate "\n" <|
      (dirty.map fun (n, bad) => s!"  {n}  depends on  {bad}").toList
    errs := errs.push
      s!"declarations claimed unconditional but are not ({dirty.size}):\n{body}\n\
         Either the proof regressed, or the claim in axiom_clean.txt was wrong."

  if errs.isEmpty then
    if emit then
      writeFootprint footprint
      IO.FS.writeFile ((← auditDirectory) / "declaration_details.json")
        ((Json.mkObj details).pretty ++ "\n")
    IO.println s!"audit ok: {decls.size} project declarations, \
      {claimed.size} claimed unconditional, no stray sorry"
  else
    throwError (String.intercalate "\n\n" errs.toList)
