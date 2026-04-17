from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DIAGNOSIS_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "architecture_level_blocker_diagnosis_packet_20260411_v0.json"
)
ALIGNMENT_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

ALIGNMENT_REFS = (
    "formal/docs/release/ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET_20260411_v0.json",
    "formal/output/reports/architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json",
    "formal/python/tests/test_architecture_seam_master_action_alignment_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_architecture_seam_master_action_alignment_live_route_is_consistent() -> None:
    diagnosis = _read_json(DIAGNOSIS_REPORT_PATH)
    alignment = _read_json(ALIGNMENT_REPORT_PATH)

    diagnosis_summary = diagnosis.get("summary", {})
    alignment_summary = alignment.get("summary", {})

    assert diagnosis_summary.get("packet_outcome") == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE"
    assert diagnosis_summary.get("blocker_conversion_failure_location") == "MASTER_ACTION_RESIDUAL_EXTRACTION"
    assert (
        diagnosis_summary.get("selected_redesigned_attack_class")
        == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS"
    )
    assert (
        diagnosis_summary.get("next_action")
        == "MATERIALIZE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET"
    )

    assert alignment_summary.get("packet_outcome") == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED"
    assert (
        alignment_summary.get("alignment_failure_mode")
        == "MASTER_ACTION_RESIDUAL_INTERFACE_NOT_BOUND_TO_SEAM_TRANSPORT_WITNESS"
    )
    assert alignment_summary.get("missing_bridge_object") == "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0"
    assert (
        alignment_summary.get("minimal_upstream_unit_to_materialize")
        == "MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0"
    )
    assert alignment_summary.get("success_rule") == (
        "ALIGNMENT_WITNESS_BOUND_AND_BRIDGE_OBJECT_MATERIALIZED_AND_TARGET_ROW_RECOMPUTE_TRIGGERED"
    )
    assert alignment_summary.get("no-loop failure rule") == "ONE_BOUNDED_ARCHITECTURE_PACKET_ONLY"
    assert alignment_summary.get("next_action") == "EXECUTE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_ONCE"

    bounded_target = alignment_summary.get("one_bounded_execution_target", {})
    assert bounded_target.get("row_id") == "ROW-SEAM-QM-STAT-001"
    assert bounded_target.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
    assert bounded_target.get("alignment_obligation") == "SEAM_TO_MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING"
    assert bounded_target.get("residual_extraction_interface") == "MASTER_ACTION_RESIDUAL_EXTRACTION_INTERFACE_QM_STAT_v0"
    assert bounded_target.get("transport_witness") == "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0"

    assert alignment.get("source_bundle", {}).get("architecture_level_blocker_diagnosis_packet_report") == (
        "formal/output/reports/architecture_level_blocker_diagnosis_packet_20260411_v0.json"
    )


def test_architecture_seam_master_action_alignment_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in ALIGNMENT_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )