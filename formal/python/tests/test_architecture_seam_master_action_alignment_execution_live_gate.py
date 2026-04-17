from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json"
)
EXECUTION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "architecture_seam_master_action_alignment_packet_execution_20260411_v0.json"
)
RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "architecture_seam_master_action_alignment_ruling_20260411_v0.json"
)
POST_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_post_architecture_alignment_decision_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

EXECUTION_STACK_REFS = (
    "formal/docs/release/ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_EXECUTION_20260411_v0.json",
    "formal/output/reports/architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
    "formal/docs/release/ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING_20260411_v0.json",
    "formal/output/reports/architecture_seam_master_action_alignment_ruling_20260411_v0.json",
    "formal/docs/release/SCIENCE_POST_ARCHITECTURE_ALIGNMENT_DECISION_20260411_v0.json",
    "formal/output/reports/science_post_architecture_alignment_decision_20260411_v0.json",
    "formal/python/tests/test_architecture_seam_master_action_alignment_execution_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_architecture_seam_master_action_alignment_execution_stack_is_consistent() -> None:
    packet = _read_json(PACKET_REPORT_PATH)
    execution = _read_json(EXECUTION_REPORT_PATH)
    ruling = _read_json(RULING_REPORT_PATH)
    post_decision = _read_json(POST_DECISION_REPORT_PATH)

    packet_summary = packet.get("summary", {})
    execution_summary = execution.get("summary", {})
    ruling_summary = ruling.get("summary", {})
    post_decision_summary = post_decision.get("summary", {})

    assert packet_summary.get("packet_outcome") == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED"
    assert packet_summary.get("next_action") == "EXECUTE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_ONCE"

    assert execution_summary.get("execution_classification") == "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING"
    assert execution_summary.get("bridge_object_materialized") is True
    assert execution_summary.get("alignment_witness_bound") is True
    assert execution_summary.get("target_row_recompute_triggered") is True
    assert execution_summary.get("blocker_movement_signal_true") is False
    assert execution_summary.get("no_loop_rule") == "ONE_BOUNDED_EXECUTION_ONLY"
    assert execution_summary.get("next_action") == "EMIT_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING"

    assert ruling_summary.get("alignment_ruling") == "EXHAUSTED_UNDER_CURRENT_FILTER"
    assert ruling_summary.get("execution_classification") == "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING"
    assert (
        ruling_summary.get("next_action")
        == "REVIEW_POST_ARCHITECTURE_ALIGNMENT_DECISION_AND_DO_NOT_LOOP_ALIGNMENT_PACKET"
    )

    assert post_decision_summary.get("post_architecture_decision") == "PROGRAM_POSTURE_REVIEW_REQUIRED"
    assert post_decision_summary.get("specific_defect_identified") is False
    assert post_decision_summary.get("defect_scope") is None
    assert post_decision_summary.get("selected_next_program_mode") == "PROGRAM_POSTURE_REVIEW"
    assert post_decision_summary.get("next_action") == "MATERIALIZE_PROGRAM_POSTURE_REVIEW_PACKET"

    assert execution.get("source_bundle", {}).get("architecture_packet_report") == (
        "formal/output/reports/architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json"
    )
    assert ruling.get("source_bundle", {}).get("execution_report") == (
        "formal/output/reports/architecture_seam_master_action_alignment_packet_execution_20260411_v0.json"
    )
    assert post_decision.get("source_bundle", {}).get("architecture_seam_master_action_alignment_ruling_report") == (
        "formal/output/reports/architecture_seam_master_action_alignment_ruling_20260411_v0.json"
    )


def test_architecture_seam_master_action_alignment_execution_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in EXECUTION_STACK_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )