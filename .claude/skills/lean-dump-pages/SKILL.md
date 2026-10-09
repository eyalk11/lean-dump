---
name: lean-dump-pages
description: Create or update a side-by-side Blueprint/Lean comparison page with lean-dump. That means adding \lean/\leanok/\notready/\uses/\literature markers to a Blueprint .tex, writing its correspondence ledger JSON and its entry in the pages config, generating the HTML, and fixing the ERROR/INCOMPLETE/CONDITIONAL reports. Use when asked to add a closed case or Blueprint page, map Blueprint nodes to Lean declarations, or regenerate the comparison pages.
---

# Generate a comparison page

Inputs for one page:

1. **A Blueprint `.tex`**: leanblueprint environments (`theorem`, `lemma`,
   `proposition`, `corollary`, `definition`, `question`, `conjecture`), each
   with a `\label`.
2. **An optional ledger JSON** keyed by Blueprint label.
3. **An entry in the pages config.**
4. **The Lean audit files** in `lean/` (see the `lean-dump-audit` skill).
   Without them the page still renders, but says "NOT CHECKED".

## 1. Blueprint markers (the primary record)

On each node, after `\label{…}`:

- **`\lean{Fully.Qualified.name}`**: at most one per node, and it must be a
  real declaration under `--lean-dir`. Find it by searching the Lean sources;
  never guess a name. Put any extra declarations in the ledger's
  `lean_statement`.
- **`\leanok`**: only when the Lean statement matches the TeX statement
  exactly (quantifiers, hypotheses, constants, normalisation, conclusion).
  `\leanok` inside the proof means the proof is formalised. A `\leanok` node
  must have a `\lean{}` counterpart.
- **`\notready`**: the node is not formalised yet, or is only related, weaker,
  stronger or differently normalised.
- **`\uses{lab1, lab2}`**: dependency edges. The page orders middle statements
  bottom-up from these, and compares them with Lean's compiled dependencies.
  Reported differences are review prompts, not errors.
- **External inputs**: label `ext:…`, or a Lean name with an `EXT_` component.
  Each needs `\literature{Reference}{exact locator}`, such as a theorem or
  equation number; "see Author" does not count.

## 2. Ledger JSON (optional, per page)

```json
{
  "_comment": ["what this ledger covers"],
  "thm:main": {
    "lean": "Ns.main_theorem",
    "status": "full",
    "marker": "leanok",
    "lean_remark": "why this declaration is the counterpart",
    "lean_statement": "further declarations proving other clauses of the node"
  },
  "ext:classical": {"lean": "Ns.EXT_classical", "status": "external-input"}
}
```

- **`lean` overrides the node's `\lean{}`.** `"lean": null` means no counterpart.
- **Status:** `"full"` claims a complete counterpart, `"external-input"`
  classifies the node as external, and any other text is shown as-is.
- **Consistency:** `"lean": null` together with `\leanok` (or with
  `"status": "full"`) is refused as an error.

## 3. Pages config

```json
{"pages": [{"blueprint": "blueprint/src/x_body.tex",
            "ledger": "scripts/x_lean_correspondence.json",
            "final": ["thm:main"],
            "output": "blueprint/x_with_lean.html"}]}
```

- **`final`** is `[]` when the final theorem is not decided. Ask the author
  rather than picking one.
- **Size:** `"no_lean_defs": true` and `"no_lean_lemmas": true` drop
  Lean-only definitions and lemmas from the page.

## 4. Generate

```bash
python scripts/lean-dump/dump_theorems_with_lean.py --closed-case-pages pages.json
python scripts/lean-dump/dump_theorems_with_lean.py --blueprint x_body.tex --ledger x.json --final thm:main --format html --output x.html
```

The first form writes every page in the config; the second writes one page.

If you change Lean, refresh the audit first (`lean-dump-audit`), so the page
isn't marked stale. The run exits nonzero on page errors; pass
`--allow-page-errors` only for cases already known to be bad, and say so.

## 5. Read the reports, fix the source

| report | fix |
|---|---|
| `ERROR: … Lean name(s) resolve to nothing` | Correct the `\lean{}` or ledger name. Do not delete the node. |
| `configured final theorem is not fully Lean-ready` | The final node lacks `\leanok` on its statement or proof, or its Lean name is missing. |
| `INCOMPLETE: … no \leanok marker` | Add the marker only after checking the statements match exactly. |
| `CONDITIONAL: …` | The proof reaches `sorry` or an axiom, or the statement assumes CONJ_/UNPROVED/EXT_. Report it; do not hide it. |
| `No \literature reference` | Add `\literature{ref}{locator}` to the external node. |
| `Audit freshness: stale` | Re-run the audit, then regenerate. |

Never hand-edit the generated HTML. Change the Blueprint, the ledger or the
Lean, then regenerate. The pages link to the manual at
https://eyalk11.github.io/lean-dump/ (published from `docs/`).
