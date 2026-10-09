"""Freshness and graph checks for the saved, compiler-produced Lean audit.

No source-text dependency fallback is used for consistency verdicts. Legacy
footprints remain readable, but cannot claim freshness or hypothesis coverage.
"""
from __future__ import annotations

import hashlib
import html
import json
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

FOOTPRINT = "axiom_footprint.json"
DETAILS = "declaration_details.json"
METADATA = "axiom_footprint.meta.json"
SCHEMA = 1


def digest(path: Path) -> str:
    # Git checkouts on Windows and Linux must agree on text-file identity.
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def source_hashes(root: Path) -> dict[str, str]:
    paths = set((root / "lean").rglob("*.lean"))
    paths.update((root / "scripts").glob("*.lean"))
    paths.update(root / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "lean/axiom_clean.txt", "scripts/run_lean_audit.py",
        "scripts/lean_audit_report.py",
    ))
    return {p.relative_to(root).as_posix(): digest(p) for p in sorted(paths) if p.is_file()}


def dependency_checkouts(root: Path) -> list[str]:
    """Flag installed Git dependencies that differ from their locked revision.

    An absent checkout is fine for rendering a saved report: the lockfile is
    still hashed. Audit generation runs Lake first, which installs dependencies.
    """
    manifest = root / "lake-manifest.json"
    if not manifest.exists():
        return []
    issues = []
    for package in json.loads(manifest.read_text(encoding="utf-8")).get("packages", []):
        name = package["name"]
        if package.get("type") != "git":
            issues.append(f"Unpinned local dependency: {name}")
            continue
        checkout = root / ".lake/packages" / name
        if not checkout.exists():
            continue
        try:
            def git(*args: str) -> str:
                return subprocess.check_output(
                    ["git", "-C", str(checkout), *args], text=True, stderr=subprocess.DEVNULL,
                ).strip()
            # Include untracked source files; ignored Lake build outputs do not count.
            if git("rev-parse", "HEAD") != package["rev"] or git("status", "--porcelain"):
                issues.append(f"Dependency checkout differs from lockfile: {name}")
        except (OSError, subprocess.CalledProcessError):
            issues.append(f"Could not verify dependency checkout: {name}")
    return issues


@dataclass
class AuditReport:
    state: str
    reasons: list[str]
    details: dict = field(default_factory=dict)
    metadata: dict = field(default_factory=dict)


def read_audit(root: Path) -> AuditReport:
    directory = root / "lean"
    if not (directory / FOOTPRINT).exists():
        return AuditReport("missing", ["No saved axiom audit."])
    if not (directory / METADATA).exists():
        return AuditReport("unknown", ["Saved audit has no source hashes; freshness is unknown."])
    try:
        metadata = json.loads((directory / METADATA).read_text(encoding="utf-8"))
        if metadata.get("schema_version") != SCHEMA:
            return AuditReport("unknown", ["Unsupported audit metadata version."])
        reasons = []
        expected = metadata["source_sha256"]
        actual = source_hashes(root)
        changed = sorted(p for p in expected.keys() | actual.keys() if expected.get(p) != actual.get(p))
        if changed:
            reasons.append("Sources/configuration changed: " + ", ".join(changed))
        for name in (FOOTPRINT, DETAILS):
            path = directory / name
            if not path.exists() or metadata["output_sha256"].get(name) != digest(path):
                reasons.append(f"Saved audit output changed or is missing: {name}")
        reasons.extend(dependency_checkouts(root))
        if reasons:
            return AuditReport("stale", reasons, metadata=metadata)
        details = json.loads((directory / DETAILS).read_text(encoding="utf-8"))
        if not isinstance(details, dict) or any(
            not isinstance(row, dict) or not isinstance(row.get("dependencies"), list)
            or not isinstance(row.get("binders"), list) or not isinstance(row.get("type"), str)
            for row in details.values()
        ):
            return AuditReport("unknown", ["Malformed compiled declaration details."], metadata=metadata)
        return AuditReport("current", [], details, metadata)
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
        return AuditReport("unknown", [f"Audit metadata could not be validated: {exc}"])


def closure(start: str, graph: dict[str, set[str]]) -> set[str]:
    seen, pending = set(), list(graph.get(start, set()))
    while pending:
        name = pending.pop()
        if name in seen or name == start:
            continue
        seen.add(name)
        pending.extend(graph.get(name, set()))
    return seen


def blueprint_consistency(nodes: list, names: dict[str, str], audit: AuditReport) -> dict[str, dict]:
    """Compare transitive dependencies projected onto mapped Blueprint nodes.

    A documented indirect dependency is accepted. Unmapped helpers are traversed,
    aliases sharing a Lean declaration are equivalent, and missing audit records
    prevent a success verdict. Differences are review hints, not proof failures.
    """
    blueprint = {node.item.label: set(node.uses) for node in nodes}
    labels = set(blueprint)
    graph = {name: set(row.get("dependencies", [])) for name, row in audit.details.items()}
    unmapped = {label for label in labels if not names.get(label) or names[label] not in graph}
    results = {}
    for node in nodes:
        label = node.item.label
        unknown = sorted(blueprint[label] - labels)
        if audit.state != "current" or unmapped:
            results[label] = {"state": "unchecked", "unknown": unknown,
                              "missing_records": sorted(unmapped), "undocumented": [], "unseen": []}
            continue
        lean_reached = closure(names[label], graph)
        documented = closure(label, blueprint)
        documented_names = {names[d] for d in documented if d in names}
        actual = {other for other in labels if other != label and names[other] != names[label]
                  and names[other] in lean_reached}
        undocumented = sorted(d for d in actual if names[d] not in documented_names)
        unseen = sorted(d for d in blueprint[label] & labels
                        if names[d] != names[label] and names[d] not in lean_reached)
        results[label] = {"state": "review" if unknown or undocumented or unseen else "matched",
                          "unknown": unknown, "undocumented": undocumented, "unseen": unseen,
                          "missing_records": []}
    return results


def hypothesis_panel(name: str, audit: AuditReport) -> str:
    row = audit.details.get(name) if audit.state == "current" else None
    if row is None or "binders" not in row:
        return '<p class="audit-note">Explicit hypotheses: not checked for this source version.</p>'
    binders = row["binders"]
    hypotheses = [b for b in binders if b["is_proposition"] or b["binder"] == "instance"]
    items = "".join(
        f'<li><code>{html.escape(b["name"])} : {html.escape(b["type"])}</code>'
        f' <small>({html.escape(b["binder"])})</small></li>' for b in hypotheses
    )
    return (
        f'<details class="hypotheses"><summary>Explicit hypotheses and instances ({len(hypotheses)})</summary>'
        '<p>Read from the elaborated type, including implicit and unnamed assumptions. '
        'Ordinary hypotheses describe the theorem\u2019s scope; their presence is not a proof gap.</p>'
        + (f'<ul>{items}</ul>' if hypotheses else '<p>No proposition hypotheses or instance parameters.</p>')
        + '<details><summary>Full elaborated type</summary><pre>'
        + html.escape(row.get("expanded_type", row["type"])) + '</pre></details></details>'
    )


def consistency_panel(result: dict) -> str:
    messages = []
    if result["state"] == "unchecked":
        messages.append("Not checked: a current compiled audit covering all mapped nodes is required.")
    elif result["state"] == "matched":
        messages.append("Mapped dependencies agree through the audited project graph.")
    for key, prefix in (
        ("unknown", "Unknown Blueprint labels"),
        ("undocumented", "Lean reaches these mapped nodes without a Blueprint dependency path"),
        ("unseen", "Blueprint dependencies not found in the compiled dependency closure"),
        ("missing_records", "Nodes missing compiled audit records"),
    ):
        if result[key]:
            messages.append(prefix + ": " + ", ".join(result[key]) + ".")
    return ('<details class="consistency"><summary>Blueprint consistency: '
            + html.escape(result["state"]) + '</summary><p>'
            + '</p><p>'.join(html.escape(m) for m in messages)
            + '</p><p>Differences call for review: the formal proof may use a different argument. '
              'This compares dependencies, not mathematical statement equivalence.</p></details>')


def proof_summary(audit: AuditReport, footprint: dict, names: set[str], complete: bool) -> str:
    """Certify only the final theorem(s), using their transitive axiom audit."""
    if audit.state != "current" or not complete or not names:
        return ""
    records = [footprint.get(name) for name in names]
    if any(not isinstance(row, dict) or not isinstance(row.get("axioms"), list)
           or not isinstance(row.get("assumes"), list) for row in records):
        return ""
    if any(row["axioms"] or row["assumes"] for row in records):
        return ""
    subject = 'The final theorem is' if len(names) == 1 else 'The final theorems are'
    proof = 'Its Lean proof is' if len(names) == 1 else 'Their Lean proofs are'
    return (f'<strong class="proof-summary">{subject} fully proven from '
            f'Lean’s standard axioms. {proof} sorry-free.</strong>')


def audit_panel(audit: AuditReport, checks: dict[str, dict], proof_status: str = "") -> str:
    matched = sum(r["state"] == "matched" for r in checks.values())
    review = sum(r["state"] == "review" for r in checks.values())
    unchecked = sum(r["state"] == "unchecked" for r in checks.values())
    summary = f'Audit freshness: {audit.state} · Blueprint consistency: {matched}/{len(checks)} matched'
    if review:
        summary += f', {review} to review'
    if unchecked:
        summary += f', {unchecked} unchecked'
    details = ''.join(f'<li>{html.escape(reason)}</li>' for reason in audit.reasons)
    stamp = audit.metadata.get("generated_at", "not recorded")
    version = audit.metadata.get("lean_version", "not recorded")
    return (
        f'<details class="audit-checks audit-{audit.state}"><summary>{proof_status}{html.escape(summary)}</summary>'
        f'<ul>{details}</ul><p>Audit generated: {html.escape(stamp)}. {html.escape(version)}.</p>'
        '<p>Freshness compares Lean sources, audit code, toolchain and dependency lockfile hashes, '
        'plus installed dependency checkouts. Page generation does not run Lean. '
        'An unknown or stale audit is not a proof failure, but cannot certify this source version.</p>'
        '<p>The axiom audit follows dependencies transitively, like <code>#print axioms</code>. '
        'The standard Lean axioms <code>propext</code>, <code>Classical.choice</code> and '
        '<code>Quot.sound</code> are allowed. Diagnostic commands or output quoted in source comments '
        'are not fresh audit evidence.</p>'
        '<p>Consistency compares paths among mapped Blueprint nodes using compiled project references '
        '(types and proofs), including unnamed helpers. External library internals are not expanded. '
        'Hypotheses are displayed for review regardless of their names; only provenance-prefixed '
        'hypotheses contribute to the existing conditional-status rule.</p>'
        '<p>Refresh with <code>python scripts/run_lean_audit.py</code>, then regenerate this page.</p>'
        '</details>'
    )
