from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
TRANCHE_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qm_blocker_moving_tranche_20260411_v0.json"
RULING_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qm_blocker_moving_ruling_20260411_v0.json"
SELECTION_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "science_next_attack_class_selection_20260411_v0.json"
DIRECT_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

STACK_REFS = (
    "formal/output/reports/qm_blocker_moving_tranche_20260411_v0.json",
    "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
    "formal/output/reports/science_next_attack_class_selection_20260411_v0.json",
    "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
    "formal/python/tests/test_qm_blocker_moving_control_stack_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qm_blocker_moving_control_stack_current_route_is_consistent() -> None:
    tranche = _read_json(TRANCHE_REPORT_PATH)
    ruling = _read_json(RULING_REPORT_PATH)
    selection = _read_json(SELECTION_REPORT_PATH)
    direct_packet = _read_json(DIRECT_PACKET_REPORT_PATH)

    tranche_summary = tranche.get("summary", {})
    ruling_summary = ruling.get("summary", {})
    selection_summary = selection.get("summary", {})
    direct_summary = direct_packet.get("summary", {})

    assert tranche_summary.get("row_id") == "ROW-PILLAR-QM-001"
    assert tranche_summary.get("subtarget_id") == "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v0"
    assert tranche_summary.get("tranche_classification") == "QM_VALID_BUT_NONMOVING"
    assert tranche_summary.get("next_action") == "EMIT_QM_RULING_AND_REFRESH_ATTACK_CLASS_SELECTION"

    assert ruling_summary.get("row_id") == tranche_summary.get("row_id")
    assert ruling_summary.get("subtarget_id") == tranche_summary.get("subtarget_id")
    assert ruling_summary.get("tranche_classification") == tranche_summary.get("tranche_classification")
    assert ruling_summary.get("qm_ruling") == "EXHAUSTED_UNDER_CURRENT_FILTER"
    assert ruling_summary.get("exclude_from_immediate_reselection") is True
    assert ruling_summary.get("next_action") == "REFRESH_ATTACK_CLASS_SELECTION_AND_DO_NOT_LOOP_QM"

    assert selection_summary.get("qm_ruling") == ruling_summary.get("qm_ruling")
    assert selection_summary.get("decision") == "ESCALATE_TO_DECLARED_NEXT_ATTACK_CLASS"
    assert selection_summary.get("selected_next_attack_class") == "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS"
    assert selection_summary.get("proof_debt_parallel_reopen_allowed") is False
    assert selection_summary.get("next_action") == "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET"

    assert direct_packet.get("attack_class") == selection_summary.get("selected_next_attack_class")
    assert direct_summary.get("packet_outcome") == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED"
    assert direct_summary.get("selected_attack_class") == selection_summary.get("selected_next_attack_class")
    assert direct_summary.get("selected_target_row") == "ROW-SEAM-QM-STAT-001"
    assert direct_summary.get("selected_target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
    assert direct_summary.get("next_action") == "EXECUTE_DIRECT_MASTER_ACTION_QM_STAT_TRANSPORT_RESIDUAL_PACKET_ONCE"

    assert tranche.get("source_bundle", {}).get("qm_rework_report") == (
        "formal/output/reports/theorem_gap_qm_rework_tranche_20260411_v0.json"
    )
    assert ruling.get("source_bundle", {}).get("qm_blocker_moving_tranche_report") == STACK_REFS[0]
    assert selection.get("source_bundle", {}).get("qm_blocker_moving_ruling_report") == STACK_REFS[1]
    assert direct_packet.get("source_bundle", {}).get("science_next_attack_class_selection_report") == STACK_REFS[2]
    assert direct_packet.get("source_bundle", {}).get("qm_blocker_moving_ruling_report") == STACK_REFS[1]


def test_qm_blocker_moving_control_stack_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in STACK_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )