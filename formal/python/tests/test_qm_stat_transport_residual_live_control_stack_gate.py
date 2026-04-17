from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DIRECT_ATTACK_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json"
)
PACKET_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_transport_residual_packet_20260411_v0.json"
RULING_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_transport_residual_ruling_20260411_v0.json"
POST_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_post_direct_attack_class_decision_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

STACK_REFS = (
    "formal/output/reports/qm_stat_transport_residual_packet_20260411_v0.json",
    "formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json",
    "formal/output/reports/science_post_direct_attack_class_decision_20260411_v0.json",
    "formal/python/tests/test_qm_stat_transport_residual_live_control_stack_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qm_stat_transport_residual_live_control_stack_is_consistent() -> None:
    direct_attack = _read_json(DIRECT_ATTACK_REPORT_PATH)
    packet = _read_json(PACKET_REPORT_PATH)
    ruling = _read_json(RULING_REPORT_PATH)
    post_decision = _read_json(POST_DECISION_REPORT_PATH)

    direct_summary = direct_attack.get("summary", {})
    packet_summary = packet.get("summary", {})
    ruling_summary = ruling.get("summary", {})
    post_summary = post_decision.get("summary", {})

    assert direct_summary.get("selected_target_row") == "ROW-SEAM-QM-STAT-001"
    assert direct_summary.get("selected_target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
    assert direct_summary.get("next_action") == "EXECUTE_DIRECT_MASTER_ACTION_QM_STAT_TRANSPORT_RESIDUAL_PACKET_ONCE"

    assert packet_summary.get("row_id") == direct_summary.get("selected_target_row")
    assert packet_summary.get("target_package_id") == direct_summary.get("selected_target_package_id")
    assert packet_summary.get("packet_classification") == "QM_STAT_TRANSPORT_RESIDUAL_VALID_BUT_NONMOVING"
    assert packet_summary.get("seam_integration_gap_delta") == 0
    assert packet_summary.get("theorem_gap_delta") == 0
    assert packet_summary.get("target_row_success_increment_gt_0") is False
    assert packet_summary.get("blocker_token_delta") == 0
    assert packet_summary.get("next_action") == "EMIT_QM_STAT_TRANSPORT_RESIDUAL_RULING"

    assert ruling_summary.get("row_id") == packet_summary.get("row_id")
    assert ruling_summary.get("target_package_id") == packet_summary.get("target_package_id")
    assert ruling_summary.get("packet_classification") == packet_summary.get("packet_classification")
    assert ruling_summary.get("qm_stat_ruling") == "EXHAUSTED_UNDER_CURRENT_FILTER"
    assert ruling_summary.get("exclude_from_immediate_reselection") is True
    assert ruling_summary.get("next_action") == "REVIEW_POST_DIRECT_ATTACK_CLASS_DECISION_AND_DO_NOT_LOOP_QM_STAT"

    assert post_summary.get("decision") == "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
    assert post_summary.get("selected_next_attack_class") == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
    assert post_summary.get("local_attack_packet_hold_policy") == "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED"
    assert post_summary.get("next_action") == "MATERIALIZE_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET"

    assert packet.get("source_bundle", {}).get("direct_attack_class_packet_report") == (
        "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json"
    )
    assert ruling.get("source_bundle", {}).get("qm_stat_transport_residual_packet_report") == STACK_REFS[0]
    assert post_decision.get("source_bundle", {}).get("qm_stat_transport_residual_ruling_report") == STACK_REFS[1]


def test_qm_stat_transport_residual_live_control_stack_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in STACK_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )