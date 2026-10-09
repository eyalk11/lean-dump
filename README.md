# lean-dump

Side-by-side LaTeX/Lean pages: This is a modern replacement to standard blueprint with dependency graph.

- Verifies much more things! 
- Displays much more things!

a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) `.tex`, shown
beside the Lean declaration that formalises it, with what that declaration
actually rests on.

- `dump_theorems_with_lean.py` — the page generator.
- 
- `vendor/gh-tex-viewer` — submodule; its `render.js` typesets statements in
  the browser (KaTeX). Clone with `--recursive`, or run
  `git submodule update --init --recursive`.

Standard library only; Python 3.9+.

![A comparison page: Blueprint node beside its Lean counterpart](docs/screenshot.png)

How to read a page (audit freshness, axioms, hypotheses, dependency
consistency, warning banners): **[About the Lean checks](https://eyalk11.github.io/lean-dump/)**.
Every generated page links there.

## Producing the inputs

Two Claude Code skills in `.claude/skills/` walk through it:

- **`lean-dump-audit`** sets up and refreshes the Lean audit files
  (`axiom_footprint.json`, `declaration_details.json`,
  `axiom_footprint.meta.json`).
- **`lean-dump-pages`** covers the Blueprint markers, the correspondence ledger
  and the pages config, then generates the pages and fixes what they report.

Templates for a new project, to copy into `scripts/`:

- **`templates/lean_audit_exporter.lean`:** the Lean exporter. Fill in its three
  `EDIT` points: imports, project module prefixes and the modules allowed to
  contain `sorry`.
- **`templates/run_lean_audit.py`:** builds, runs the exporter and writes the
  three files together with source hashes.

## Modes

**Blueprint page** (one standalone Blueprint):

```bash
python dump_theorems_with_lean.py --blueprint path/to/blueprint.tex --ledger ledger.json --final thm:main --format html --output page.html
```

**Several Blueprint pages** from a config file:

```bash
python dump_theorems_with_lean.py --closed-case-pages pages.json
```

```json
{"pages": [{"blueprint": "…/body.tex", "ledger": "…/ledger.json",
            "final": ["thm:main"], "output": "…/page.html",
            "no_lean_defs": false, "no_lean_lemmas": false}]}
```

`ledger` is optional, and `final` is `[]` when the final theorem is not known.
The run exits nonzero when a page reports an error, unless you pass
`--allow-page-errors`.

**Manuscript mode**: fuzzy matching between a `\part{Part X}` manuscript and
the Lean tree, with an optional curated ledger (`--overrides`):

```bash
python dump_theorems_with_lean.py --manuscript paper.tex --overrides correspondence.json --format html --output out.html
```

`--lean-dir` (default `lean`) is the Lean source tree in every mode. The
generator reads the source and does not run Lean.

## Conventions it relies on

The pages report status from names and markers, so the project has to follow
these conventions.

### Lean provenance prefixes

| prefix | meaning |
|---|---|
| `EXT_` | external input: a published theorem the project uses without proving it |
| `CONJ_` | a live conjecture |
| `UNPROVED` | an unproved internal claim |

Any dotted component of a name may carry the prefix (`Ns.EXT_foo`).

- **EXT_:** an `EXT_` declaration that a Blueprint node reaches is listed under
  External inputs. This applies even when no Blueprint node names it.
- **Unproved dependencies:** an unproved supporting result should be an explicit
  hypothesis, `theorem foo (h : CONJ_x …) : …`, and not a `sorry`. Such a
  theorem is axiom-clean but establishes nothing until `CONJ_x` is proved. The
  audit records it under `assumes`, and the page marks it CONDITIONAL.
- **Where sorry lives:** `sorry` belongs only in `*_deps` modules and in the
  declared external or conjecture modules. A proof that reaches one is listed
  under `axioms` and is marked CONDITIONAL too.

### Blueprint markers

- **`\lean{Name}`:** at most one per node, and it must be the fully qualified
  declaration.
- **`\leanok` / `\notready`:** `\leanok` on the statement means the Lean
  statement matches the TeX statement exactly. For an external input, that is
  all `\leanok` claims. A `\leanok` node needs a `\lean{}` counterpart.
- **`\uses{…}`:** dependency edges. Middle statements are written bottom-up in
  dependency order.
- **`\literature{reference}{locator}`:** required on every external input, with
  an exact locator such as a theorem or equation number. Inputs without one are
  flagged.
- **External nodes:** labels starting with `ext:` or Lean names with `EXT_`.

### Audit files

These are written by the project's own Lean exporter and are read from
`--lean-dir`:

- `axiom_footprint.json`: per declaration, `axioms` (what the proof rests on)
  and `assumes` (provenance-prefixed hypotheses in the statement).
- `declaration_details.json` and `axiom_footprint.meta.json`: hypotheses,
  references and source hashes for the freshness check.

If the footprint is missing, the page says the check did NOT run. It never
treats a missing footprint as clean.
