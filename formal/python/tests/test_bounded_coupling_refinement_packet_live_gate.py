from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
AUTHORITY_COUPLING_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "authority_coupling_review_20260411_v0.json"
)
BOUNDED_COUPLING_REFINEMENT_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "bounded_coupling_refinement_packet_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

PACKET_REFS = (
    "formal/docs/release/BOUNDED_COUPLING_REFINEMENT_PACKET_20260411_v0.json",
    "formal/output/reports/bounded_coupling_refinement_packet_20260411_v0.json",
    "formal/python/tests/test_bounded_coupling_refinement_packet_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_bounded_coupling_refinement_packet_live_route_is_consistent() -> None:
    review_report = _read_json(AUTHORITY_COUPLING_REVIEW_REPORT_PATH)
    packet_report = _read_json(BOUNDED_COUPLING_REFINEMENT_PACKET_REPORT_PATH)

    review_summary = review_report.get("summary", {})
    packet_summary = packet_report.get("summary", {})
    packet_criteria = packet_report.get("criteria", {})
    packet_inputs = packet_report.get("objective_quality", {}).get("inputs", {})

    assert review_summary.get("review_outcome") == "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED"
    assert review_summary.get("coupling_disposition") == "REFINE_COUPLING"
    assert review_summary.get("next_action") == "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"

    assert packet_criteria.get("review_prerequisite_satisfied") is True
    assert packet_criteria.get("seam_coherence_fires") is True
    assert packet_criteria.get("ledger_artifact_fires") is True
    assert packet_criteria.get("both_signals_fire") is True
    assert packet_criteria.get("correlation_witness_materializes") is True
    assert packet_criteria.get("all_coupling_criteria_met") is True

    assert packet_summary.get("execution_classification") == "EXECUTION_VALID_BINDING_TIGHTENED"
    assert packet_summary.get("coupling_state") == "TIGHTENED"
    assert (
        packet_summary.get("identified_defect")
        == "SEAM_COHERENCE_OBSERVABLE_BUT_NOT_CORRELATED_WITH_LEDGER_BLOCKER_ARTIFACT_FLUX"
    )
    assert (
        packet_summary.get("binding_to_establish")
        == "TIGHT_CORRELATION_BETWEEN_SEAM_COHERENCE_CHANGE_AND_LEDGER_ARTIFACT_FLUX"
    )
    assert packet_summary.get("target_row_id") == "ROW-SEAM-QM-STAT-001"
    assert packet_summary.get("no_loop_rule") == "ONE_BOUNDED_COUPLING_REFINEMENT_PACKET_EXECUTION_ONLY"
    assert packet_summary.get("next_action") == "EMIT_COUPLING_REFINEMENT_RULING"

    assert packet_inputs.get("review_outcome") == "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED"
    assert packet_inputs.get("artifact_to_refine") == "SEAM_TO_LEDGER_CORRELATOR_BINDING_WITNESS"
    assert packet_report.get("source_bundle", {}).get("authority_coupling_review_report") == (
        "formal/output/reports/authority_coupling_review_20260411_v0.json"
    )


def test_bounded_coupling_refinement_packet_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in PACKET_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )