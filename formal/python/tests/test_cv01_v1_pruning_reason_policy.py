import json
from pathlib import Path

from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
POLICY = REPO_ROOT / "formal" / "python" / "toe" / "observables" / "cv01_v1_pruning_reason_policy.json"


def test_cv01_v1_pruning_reason_policy_schema_and_candidate_coverage() -> None:
    doc = json.loads(POLICY.read_text(encoding="utf-8"))

    assert doc["schema"] == "OVCV01_v1_pruning_reason_policy/v1"
    assert isinstance(doc.get("version"), int)

    reason_code_to_atom = dict(doc.get("reason_code_to_atom") or {})
    eliminative_atoms = set(doc.get("eliminative_atoms") or [])
    candidate_rules = dict(doc.get("candidate_rules") or {})

    assert reason_code_to_atom
    assert eliminative_atoms
    assert candidate_rules

    # Policy must explicitly cover every candidate ID present on the canonical BR table.
    base = ovdrbr01_candidate_pruning_table_record(date="2026-01-25")
    base_candidate_ids = {str(r.get("candidate_id")) for r in list(base.rows or [])}
    assert set(candidate_rules.keys()) == base_candidate_ids

    # Every eliminative atom must be reachable from at least one reason code mapping.
    mapped_atoms = set(reason_code_to_atom.values())
    assert eliminative_atoms.issubset(mapped_atoms)
