from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "bounded_coupling_refinement_packet_20260411_v0.json"
)
RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "coupling_refinement_ruling_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

RULING_REFS = (
    "formal/docs/release/COUPLING_REFINEMENT_RULING_20260411_v0.json",
    "formal/output/reports/coupling_refinement_ruling_20260411_v0.json",
    "formal/python/tests/test_coupling_refinement_ruling_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_coupling_refinement_ruling_live_route_is_consistent() -> None:
    packet_report = _read_json(PACKET_REPORT_PATH)
    ruling_report = _read_json(RULING_REPORT_PATH)

    packet_summary = packet_report.get("summary", {})
    ruling_prereq = ruling_report.get("prerequisite", {})
    criteria = ruling_report.get("criteria_evaluation", {})
    ruling = ruling_report.get("ruling", {})
    summary = ruling_report.get("summary", {})
    promotion = ruling_report.get("authority_promotion_decision", {})

    assert packet_summary.get("execution_classification") == "EXECUTION_VALID_BINDING_TIGHTENED"
    assert packet_summary.get("coupling_state") == "TIGHTENED"
    assert packet_summary.get("next_action") == "EMIT_COUPLING_REFINEMENT_RULING"

    assert ruling_prereq.get("prerequisite_satisfied") is True
    assert ruling_prereq.get("execution_classification") == "EXECUTION_VALID_BINDING_TIGHTENED"

    assert criteria.get("criterion_1_tightened_coupling_confirmed") is True
    assert criteria.get("criterion_2_seam_coherence_fires") is True
    assert criteria.get("criterion_3_ledger_artifact_fires") is True
    assert criteria.get("criterion_4_correlation_witness_materializes") is True
    assert criteria.get("criterion_5_no_contradiction_with_blocker_authority_contract") is True
    assert criteria.get("total_criteria_met") == 5
    assert criteria.get("all_criteria_met") is True

    assert ruling.get("ruling_id") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION"
    assert ruling.get("classification") == "PROMOTION_SUPPORTED"
    assert ruling.get("promotion_gate_opens") is True
    assert ruling.get("next_action") == "PROMOTE_REVISED_BLOCKER_DEFINITION_TO_AUTHORITATIVE"
    assert ruling.get("target_row_id") == "ROW-SEAM-QM-STAT-001"

    assert promotion.get("revised_blocker_definition_promoted_to_authoritative") is True
    assert promotion.get("coupling_state_confirmation") == "TIGHTENED"
    assert promotion.get("seam_coherence_fires") is True
    assert promotion.get("ledger_artifact_fires") is True
    assert promotion.get("correlation_witness_materializes") is True

    assert summary.get("ruling_id") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION"
    assert summary.get("classification") == "PROMOTION_SUPPORTED"
    assert summary.get("promotion_gate_opens") is True
    assert summary.get("criteria_count_met") == "5/5"
    assert summary.get("next_action") == "PROMOTE_REVISED_BLOCKER_DEFINITION_TO_AUTHORITATIVE"
    assert summary.get("terminal_layer") is True


def test_coupling_refinement_ruling_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in RULING_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )