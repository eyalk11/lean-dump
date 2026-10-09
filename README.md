# lean-dump

**Every Blueprint statement beside its Lean proof, and what that proof rests on.**

lean-dump turns a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
`.tex` into one HTML page. Each node's typeset statement and proof sits beside
the Lean declaration that formalises it. The page states which claims are proved
unconditionally, which rest on `sorry`, an axiom or an unproved hypothesis, and
where the Blueprint and Lean disagree.

📖 **Documentation: <https://eyalk11.github.io/lean-dump/>**
🔎 **How to read a page: <https://eyalk11.github.io/lean-dump/checks.html>**

![A generated page: the Blueprint node typeset on the left, its Lean counterpart on the right](docs/screenshot.png)

## How it works

```
 lake build + exporter ──► lean/axiom_footprint.json        (saved once, with source hashes)
                           lean/declaration_details.json
                           lean/axiom_footprint.meta.json
                                     │
 blueprint.tex (+ ledger.json) ──────┤
 lean/**/*.lean (read as text) ──────┤
                                     ▼
              dump_theorems_with_lean.py  ──►  page.html  (KaTeX typesets it in the browser)
```

1. **Audit Lean.** `run_lean_audit.py` builds the project and runs the
   exporter. For every project declaration it records the transitive axioms,
   the provenance-prefixed hypotheses, the elaborated binders and the compiled
   dependencies. It saves them together with the SHA-256 of every input.
2. **Read the Blueprint.** The generator reads every labelled environment,
   with its `\lean`, `\leanok`/`\notready` (statement and proof), `\uses` and
   `\literature`. An optional ledger JSON can override or annotate any node.
3. **Resolve and check.** Lean sources are scanned as text, so every name is
   resolved without compiling. The static checks run, and the nodes are put in
   dependency order. The saved audit is then matched against the current
   hashes.
4. **Write the page.** The output is one HTML file. Lean is never run here, so
   regenerating takes seconds. When the saved audit is out of date, the page
   says so instead of claiming the proofs are clean.

## What a page shows

- **Side-by-side cards.** The typeset Blueprint statement and proof (with a
  LaTeX-source toggle) sit beside the Lean declaration's source, both with file
  and line.
- **Proof order.** Sections run External inputs → Final theorem → Definitions →
  Middle statements → Not used by the final theorem. Statements appear
  bottom-up along `\uses`.
- **Named propositions unfolded.** A theorem stated as `thm : UNPROVED_x` gets
  a *Statement definition* block and a *Full elaborated type* inspector.
- **Explicit hypotheses.** Every binder of the elaborated type is listed: unnamed
  arrows, implicit and instance arguments, section variables.
- **External inputs found in Lean.** Every `EXT_` declaration the page's Lean
  code reaches is listed, even when the Blueprint has no node for it.
- **Lean-only definitions and lemmas.** Declarations the page reaches but the
  Blueprint never mentions can be shown or hidden with header checkboxes, or
  left out with `--no-lean-defs` / `--no-lean-lemmas`.
- **Links both ways.** Blueprint *Uses*/*Used by* and Lean *Uses in Lean*/*Used
  in Lean by*, with labels and Lean names in remarks linked to their cards.
- **Status at a glance.** A header summary of counts, unresolved names,
  conditional statements and missing references. A one-line proof summary for
  the final theorem appears only when every check behind it passes.

## Verifications

| | Check | Result |
|---|---|---|
| static | Every `\lean{}`/ledger name is one identifier declared under `--lean-dir` | fatal if `\leanok`, else ERROR |
| static | At most one `\lean{}` per node | fatal |
| static | No `\leanok` (or ledger `"full"`) without a Lean counterpart | fatal |
| static | Statement and proof markers: `\notready` or missing `\leanok` | ERROR / INCOMPLETE |
| static | The final theorem is resolved, statement `\leanok` and proof `\leanok` | ERROR, nonzero exit |
| static | External inputs carry `\literature{ref}{locator}` | flagged |
| static | `\uses` has no cycle; `--final` names a real label | fatal |
| audit | Freshness: hashes of Lean sources, toolchain, lakefile, manifest and audit code, plus pinned dependency checkouts | current / stale / unknown |
| audit | The proof reaches `sorryAx` or a project axiom (transitively) | CONDITIONAL |
| audit | A hypothesis mentions a `CONJ_` / `UNPROVED` / `EXT_` name (the conclusion is not scanned) | CONDITIONAL |
| audit | The footprint is missing or older than a declaration | NOT CHECKED, never "clean" |
| audit | `\uses` paths compared with Lean's compiled dependencies, in both directions | Dependency difference |
| exporter | A `sorry` written outside `*_deps` modules and declared exceptions | audit fails |
| exporter | `lean/axiom_clean.txt` claims that no longer hold | audit fails |

"Static" checks run on every generation without Lean. "Audit" checks use the
saved Lean audit. "Exporter" checks run while the audit is produced. The full
table, with what each banner means, is on the
[documentation site](https://eyalk11.github.io/lean-dump/#verifications).

## Usage

```bash
git submodule add https://github.com/eyalk11/lean-dump.git scripts/lean-dump
git submodule update --init --recursive    # gh-tex-viewer comes with it
```

**One closed case.** No config file is needed, and the output goes beside the
`.tex` by default:

```bash
python scripts/lean-dump/dump_theorems_with_lean.py --blueprint blueprint/src/my_case.tex
python scripts/lean-dump/dump_theorems_with_lean.py --blueprint blueprint/src/my_case.tex --ledger my_case.json --final thm:main --output site/my_case.html
```

**Several pages at once:**

```bash
python scripts/lean-dump/dump_theorems_with_lean.py --closed-case-pages pages.json
```

| Option | Meaning |
|---|---|
| `--blueprint TEX` | Blueprint to render |
| `--ledger JSON` | optional correspondence ledger keyed by label |
| `--final LABEL` | final theorem (repeatable; omit if unknown) |
| `--output HTML` | default `<blueprint>_with_lean.html` beside the `.tex` |
| `--closed-case-pages JSON` | render every page listed in a config |
| `--lean-dir DIR` | Lean sources and saved audit (default `lean`) |
| `--no-lean-defs` | leave out Lean-only definitions the page reaches |
| `--no-lean-lemmas` | leave out Lean-only theorems and lemmas the page reaches |
| `--allow-page-errors` | exit 0 despite reported page errors |

Python 3.9+, standard library only. Run it from the project root.

## Setting up a project

1. Copy the two templates into `scripts/`:
   - `templates/lean_audit_exporter.lean`
   - `templates/run_lean_audit.py`
2. Fill in the exporter's three `EDIT` points:
   - the imports of every library root;
   - your module prefixes;
   - the modules allowed to contain `sorry` besides `*_deps`.
3. Run `python scripts/run_lean_audit.py`, and commit the three `lean/*.json`
   files it writes.
4. Mark up the Blueprint (`\lean`, `\leanok`, `\notready`, `\uses`,
   `\literature`) and generate.

The exporter template was checked against the project it came from: filled in
for that project, it reproduces the original exporter's output byte for byte.

Two **Claude Code skills** in [`.claude/skills/`](.claude/skills) guide an
agent through this:

- [`lean-dump-audit`](.claude/skills/lean-dump-audit/SKILL.md) sets up and
  refreshes the audit files.
- [`lean-dump-pages`](.claude/skills/lean-dump-pages/SKILL.md) covers the
  markers, the ledger and the config, then generates the page and fixes what
  it reports.

## Conventions

| Name | Meaning | On the page |
|---|---|---|
| `EXT_…` | external input (published theorem, used without proof) | External inputs; needs `\literature` |
| `CONJ_…` | live conjecture | as a hypothesis, makes a theorem CONDITIONAL |
| `UNPROVED…` | unproved internal claim | as a hypothesis CONDITIONAL; as a conclusion, the claim being proved |
| `*_deps` module | the only place `sorry` may be written | everything reaching it is CONDITIONAL |

Write an unproved dependency as an explicit hypothesis,
`theorem t (h : CONJ_x …) : …`, not as `sorry` or a new axiom.

## Repository

| Path | |
|---|---|
| `dump_theorems_with_lean.py` | the page generator |
| `lean_audit_report.py` | reads the saved audit and renders the freshness, hypothesis and consistency panels |
| `templates/` | exporter and runner to copy into a project |
| `.claude/skills/` | `lean-dump-audit`, `lean-dump-pages` |
| `docs/` | the GitHub Pages site |
| `vendor/gh-tex-viewer` | submodule; its `render.js` typesets the statements |

## What it does not claim

A matching dependency set does not show that the TeX and Lean statements mean
the same thing; the page lays them side by side so a reviewer can check that.
`\leanok` is the author's claim, which the page cross-checks. Audit-backed
results describe the audited source version only.
