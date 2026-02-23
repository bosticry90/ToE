from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STATE_CLAIM_TRACEABILITY_AUDIT_v0.md"

REQUIRED_FIELDS = [
    "ClaimID",
    "ClaimText",
    "Location",
    "ImpactClass",
    "EnforcementBucket",
    "EnforcingTests",
    "EnforcedArtifacts",
    "Tokens/Invariants",
    "Notes",
    "Fix (if D)",
]

ALLOWED_IMPACT_CLASSES = {"Derivation", "Recovery", "Inevitability", "Empirical", "Cross-pillar"}
ALLOWED_BUCKETS = {"A", "B", "C", "D"}
TIMELINE_TOKEN_PATTERN = re.compile(r"\b(CYCLE[-_ ]?\d+|BY_CYCLE_\d+|Q[1-4]-\d{4}|\d{4}-\d{2}-\d{2})\b")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_claim_traceability_section(text: str) -> str:
    start = text.find("## CLAIM_TRACEABILITY")
    assert start >= 0, "Audit artifact must contain a `## CLAIM_TRACEABILITY` section."
    return text[start:]


def _extract_entries(section: str) -> list[str]:
    starts = list(re.finditer(r"(?m)^\* ClaimID:\s*", section))
    assert starts, "Audit artifact must contain at least one claim entry."

    entries: list[str] = []
    for i, match in enumerate(starts):
        entry_start = match.start()
        entry_end = starts[i + 1].start() if i + 1 < len(starts) else len(section)
        entries.append(section[entry_start:entry_end].strip())
    return entries


def _field(entry: str, field_name: str) -> str:
    m = re.search(rf"(?m)^\* {re.escape(field_name)}:\s*(.+)$", entry)
    assert m is not None, f"Missing required field `{field_name}` in entry:\n{entry}"
    value = m.group(1).strip()
    assert value, f"Field `{field_name}` must be non-empty."
    return value


def test_state_claim_traceability_audit_schema_and_bounds() -> None:
    text = _read(AUDIT_PATH)
    section = _extract_claim_traceability_section(text)
    entries = _extract_entries(section)

    assert 30 <= len(entries) <= 100, "Audit must contain between 30 and 100 claim entries."

    for entry in entries:
        for field_name in REQUIRED_FIELDS:
            _field(entry, field_name)

        location = _field(entry, "Location")
        assert "State_of_the_Theory.md:L" in location, "Each claim location must point to State_of_the_Theory.md line anchors."

        impact_class = _field(entry, "ImpactClass")
        assert impact_class in ALLOWED_IMPACT_CLASSES, f"Invalid ImpactClass `{impact_class}`."

        bucket = _field(entry, "EnforcementBucket")
        assert bucket in ALLOWED_BUCKETS, f"Invalid EnforcementBucket `{bucket}`."

        enforcing_tests = _field(entry, "EnforcingTests")
        if bucket in {"A", "B"}:
            assert enforcing_tests.upper() != "N/A", "Buckets A/B must reference enforcing tests."

        if bucket == "D":
            fix_text = _field(entry, "Fix (if D)")
            assert "TODO: add gate" in fix_text, "Bucket D entries must include TODO: add gate remediation text."
            assert TIMELINE_TOKEN_PATTERN.search(fix_text), "Bucket D entries must include a bounded timeline token."
