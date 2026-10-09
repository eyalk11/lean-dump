---
name: lean-dump-audit
description: Set up or refresh the Lean audit files lean-dump pages read (lean/axiom_footprint.json, lean/declaration_details.json, lean/axiom_footprint.meta.json). Use when a page says "NOT CHECKED", "Audit freshness: stale/unknown" or "Explicit hypotheses: not checked", when adding lean-dump to a new Lean project, or after Lean sources, the toolchain or the audit code changed.
---

# Generate the Lean audit files

The pages never run Lean. Everything they say about what a proof rests on
(axioms, `sorry`, CONJ_/UNPROVED/EXT_ hypotheses, binders, compiled
dependencies) comes from three files that a Lean exporter writes into `lean/`:

| file | content |
|---|---|
| `axiom_footprint.json` | `{"Name": {"axioms": [...], "assumes": [...]}}` for every project declaration. `axioms` lists the non-benign axioms the proof reaches (`sorryAx`, project axioms). `assumes` lists the provenance-prefixed constants in the statement's hypotheses (conclusions are not scanned). |
| `declaration_details.json` | `{"Name": {"type", "expanded_type", "binders": [{"name","type","binder","is_proposition"}], "dependencies": [...]}}` |
| `axiom_footprint.meta.json` | `schema_version`, `generated_at`, `source_commit`, `lean_version`, `source_sha256` (Lean sources, `scripts/*.lean`, toolchain, lakefile, manifest, `lean/axiom_clean.txt`, `scripts/run_lean_audit.py` and `lean_audit_report.py`), `output_sha256` |

The page marks the audit **current** only when `source_sha256` matches the
working tree. Any edit to those inputs makes the audit stale, and that is by
design.

## Refresh (project already set up)

```bash
python scripts/run_lean_audit.py
```

This runs `lake build`, then the exporter, then writes the three files. It
writes the meta file last, so an interrupted run never looks current. Then
regenerate the pages (see the `lean-dump-pages` skill).

The exporter fails the run, and writes nothing, when either of these holds:

- **Stray `sorry`:** a `sorry` sits outside `*_deps` modules and
  `allowedSorryModules`. Move the hole into a `_deps` module, or make the
  dependency an explicit `CONJ_`/`UNPROVED` hypothesis.
- **Broken `axiom_clean.txt`:** `lean/axiom_clean.txt` names a missing
  declaration, or one that is not axiom-clean. Fix the list or the proof.

Do not weaken a statement, or add an exception, just to make the audit pass.

## First-time setup in a new Lean project

Layout the hashes assume: Lean sources in `lean/`, scripts in `scripts/`, and
lean-dump at `scripts/lean-dump`.

1. **Add lean-dump:**
   `git submodule add https://github.com/eyalk11/lean-dump.git scripts/lean-dump`,
   then `git submodule update --init --recursive`.
2. **Copy the two templates:**
   - `templates/lean_audit_exporter.lean` to `scripts/lean_audit_exporter.lean`
   - `templates/run_lean_audit.py` to `scripts/run_lean_audit.py`
3. **Fill in the exporter's three `EDIT` points:**
   - **EDIT 1:** `import` every root of the `lean_lib`. Read `roots` in
     `lakefile.toml`; a root you don't import is silently unaudited.
   - **EDIT 2:** `allowedSorryModules`, the modules allowed to contain `sorry`
     besides `*_deps` (a conjectures module, an external-theorems module).
   - **EDIT 3:** `projectModulePrefixes`, which must match every root module's
     name. A prefix `p` matches a module named `p` or starting with `p`.
     Check that no root falls outside it.
4. **Optional:** create `lean/axiom_clean.txt`, one fully qualified name per
   line, listing results claimed unconditional. To print the current clean set:
   `LEAN_DUMP_AUDIT_REPORT=1 lake env lean scripts/lean_audit_exporter.lean`.
5. **Run** `python scripts/run_lean_audit.py` and confirm it prints
   `audit ok: N project declarations` and writes the three files.
6. **Commit the three files**, so pages can be regenerated without Lean.

## Conventions the audit enforces or reads

- **`CONJ_`, `UNPROVED`, `EXT_` prefixes** (any dotted component) mark a live
  conjecture, an unproved internal claim and an external input. A theorem
  `(h : CONJ_x …) → …` lists `CONJ_x` under `assumes`. A theorem whose
  *conclusion* is `UNPROVED_x` discharges it and does not list it.
- **An unproved dependency** should be an explicit hypothesis, not `sorry` or
  a new axiom. `sorry` lives only in `*_deps` and the declared exception
  modules.
- **A name without a prefix is invisible.** A hypothesis typed by a
  proposition named `Conjecture`, without `CONJ_`, is not caught.
