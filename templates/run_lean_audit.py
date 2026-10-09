#!/usr/bin/env python3
"""Build Lean, run its semantic audit, and publish source-bound audit reports.

lean-dump template: copy to `scripts/run_lean_audit.py` in your project, with
lean-dump checked out at `scripts/lean-dump` and the exporter at
`scripts/lean_audit_exporter.lean`. Writes lean/axiom_footprint.json,
lean/declaration_details.json and lean/axiom_footprint.meta.json.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from datetime import datetime, timezone

sys.path.insert(0, str(Path(__file__).resolve().parent / "lean-dump"))
from lean_audit_report import (DETAILS, FOOTPRINT, METADATA, SCHEMA, dependency_checkouts,
                               digest, source_hashes)

ROOT = Path(__file__).resolve().parent.parent


def run_audit(root: Path = ROOT) -> None:
    # If Lake changes the manifest while resolving dependencies, require a rerun.
    before = source_hashes(root)
    subprocess.run(["lake", "build"], cwd=root, check=True)
    issues = dependency_checkouts(root)
    if issues:
        raise RuntimeError("Cannot certify dependency pins: " + "; ".join(issues))
    with tempfile.TemporaryDirectory(prefix="lean-dump-audit-") as temporary:
        output = Path(temporary)
        env = dict(os.environ, LEAN_DUMP_AUDIT_EMIT="1", LEAN_DUMP_AUDIT_DIR=str(output))
        subprocess.run(["lake", "env", "lean", "scripts/lean_audit_exporter.lean"],
                       cwd=root, env=env, check=True)
        version = subprocess.check_output(["lake", "env", "lean", "--version"],
                                          cwd=root, text=True).strip()
        if source_hashes(root) != before or dependency_checkouts(root):
            raise RuntimeError("Audit inputs changed during the build/audit; rerun.")
        for name in (FOOTPRINT, DETAILS):
            # A successful process without both reports is not a completed audit.
            json.loads((output / name).read_text(encoding="utf-8"))
        try:
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
        except (OSError, subprocess.CalledProcessError):
            revision = None
        metadata = {
            "schema_version": SCHEMA,
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "source_commit": revision,  # Informational; hashes include uncommitted source edits.
            "lean_version": version,
            "source_sha256": before,
            "output_sha256": {name: digest(output / name) for name in (FOOTPRINT, DETAILS)},
        }
        directory = root / "lean"
        for name in (FOOTPRINT, DETAILS):
            (directory / name).write_bytes((output / name).read_bytes())
        # Written last: interruption cannot make a mismatched report look current.
        (directory / METADATA).write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print("Audit saved with source hashes, explicit hypotheses and compiled dependencies.")


if __name__ == "__main__":
    run_audit()
