from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POST_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_post_direct_attack_class_decision_20260411_v0.json"
)
DIAGNOSIS_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "architecture_level_blocker_diagnosis_packet_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

DIAGNOSIS_REFS = (
    "formal/docs/release/ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_20260411_v0.json",
    "formal/output/reports/architecture_level_blocker_diagnosis_packet_20260411_v0.json",
    "formal/python/tests/test_architecture_level_blocker_diagnosis_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_architecture_level_blocker_diagnosis_live_route_is_consistent() -> None:
    post_decision = _read_json(POST_DECISION_REPORT_PATH)
    diagnosis = _read_json(DIAGNOSIS_REPORT_PATH)

    post_summary = post_decision.get("summary", {})
    diagnosis_summary = diagnosis.get("summary", {})
    diagnosis_answers = diagnosis.get("diagnosis_answers", {})

    assert post_summary.get("decision") == "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
    assert post_summary.get("selected_next_attack_class") == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
    assert post_summary.get("local_attack_packet_hold_policy") == "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED"
    assert post_summary.get("next_action") == "MATERIALIZE_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET"

    assert diagnosis_summary.get("packet_outcome") == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE"
    assert diagnosis_summary.get("movement_filter_defect_identified") is False
    assert diagnosis_summary.get("upstream_missing_unit_identified") is True
    assert diagnosis_summary.get("blocker_conversion_failure_location") == "MASTER_ACTION_RESIDUAL_EXTRACTION"
    assert (
        diagnosis_summary.get("selected_redesigned_attack_class")
        == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS"
    )
    assert (
        diagnosis_summary.get("next_action")
        == "MATERIALIZE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET"
    )

    assert diagnosis_answers.get("blocker_conversion_failure_location") == diagnosis_summary.get(
        "blocker_conversion_failure_location"
    )
    assert diagnosis_answers.get("smallest_upstream_unit") == "ARCHITECTURE_LEVEL_BLOCKER_CONVERSION_UNIT"
    assert diagnosis_answers.get("movement_filter_vs_architecture") == "ARCHITECTURE_UNDERPOWERED"
    assert diagnosis_answers.get("selected_redesigned_attack_class") == diagnosis_summary.get(
        "selected_redesigned_attack_class"
    )

    assert diagnosis.get("source_bundle", {}).get("science_post_direct_attack_class_decision_report") == (
        "formal/output/reports/science_post_direct_attack_class_decision_20260411_v0.json"
    )
    assert diagnosis.get("source_bundle", {}).get("qm_stat_transport_residual_ruling_report") == (
        "formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json"
    )


def test_architecture_level_blocker_diagnosis_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in DIAGNOSIS_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )