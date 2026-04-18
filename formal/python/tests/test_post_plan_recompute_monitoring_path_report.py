from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_recompute_monitoring_path_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_PROGRAM_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_bounded_coupling_refinement_packet_chain_report": "formal/output/reports/post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json",
                "recompute_observation_report": "formal/output/reports/recompute_observation_20260411_v0.json",
                "post_recompute_observation_report": "formal/output/reports/post_recompute_observation_20260411_v0.json"
            },
            "execution_policy": {
                "required_packet_chain_outcome": "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED",
                "required_packet_chain_next_action": "MONITOR_RECOMPUTE_SURFACES",
                "required_trigger_propagation_confirmed": True,
                "required_recompute_observation_next_layer": "AWAIT_POST_RECOMPUTE_OBSERVATION",
                "required_post_recompute_ruling_id": "RECOMPUTE_STILL_PENDING",
                "required_post_recompute_next_action": "DEFER_RULING_MONITOR_RECOMPUTE_COMPLETION",
                "required_cascade_determination": "STILL_PENDING"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_RECOMPUTE_MONITORING_PATH_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_RECOMPUTE_MONITORING_PATH_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_RECOMPUTE_MONITORING_PATH_PENDING_COMPLETION",
                    "POST_PLAN_RECOMPUTE_MONITORING_PATH_MATERIAL_CASCADE_CONFIRMED",
                    "POST_PLAN_RECOMPUTE_MONITORING_PATH_AUTHORITY_LOCAL_ONLY",
                    "POST_PLAN_RECOMPUTE_MONITORING_PATH_BLOCKED",
                    "POST_PLAN_RECOMPUTE_MONITORING_PATH_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_RECOMPUTE_MONITORING_PATH_REPAIR"
                ],
                "default_outcome": "POST_PLAN_RECOMPUTE_MONITORING_PATH_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, local_only: bool = False) -> None:
    _write_json(root / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json", {"summary": {"terminal_outcome": "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED", "next_action": "MONITOR_RECOMPUTE_SURFACES"}})
    _write_json(root / "formal" / "output" / "reports" / "recompute_observation_20260411_v0.json", {"cascade_analysis": {"trigger_propagation_confirmed": True}, "observation_outcome": {"next_decision_layer": "AWAIT_POST_RECOMPUTE_OBSERVATION"}, "interpretation_summary": {"surfaces_triggering_recompute": 3, "trigger_propagation_confirmed": True}})
    if local_only:
        _write_json(root / "formal" / "output" / "reports" / "post_recompute_observation_20260411_v0.json", {"summary": {"ruling_id": "TRIGGER_PROPAGATION_ONLY_AUTHORITY_LOCAL", "next_action": "DOCUMENT_AUTHORITY_LOCAL_RESULT_WITH_PENDING_MONITOR", "cascade_determination": "COMPLETED_NO_OUTPUTS"}, "post_recompute_ruling": {"ruling_id": "TRIGGER_PROPAGATION_ONLY_AUTHORITY_LOCAL", "next_action": "DOCUMENT_AUTHORITY_LOCAL_RESULT_WITH_PENDING_MONITOR"}})
    else:
        _write_json(root / "formal" / "output" / "reports" / "post_recompute_observation_20260411_v0.json", {"summary": {"ruling_id": "RECOMPUTE_STILL_PENDING", "next_action": "DEFER_RULING_MONITOR_RECOMPUTE_COMPLETION", "cascade_determination": "STILL_PENDING"}, "post_recompute_ruling": {"ruling_id": "RECOMPUTE_STILL_PENDING", "next_action": "DEFER_RULING_MONITOR_RECOMPUTE_COMPLETION"}})


def _seed_material_inputs(root: Path) -> None:
    _write_json(root / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json", {"summary": {"terminal_outcome": "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED", "next_action": "MONITOR_RECOMPUTE_SURFACES"}})
    _write_json(root / "formal" / "output" / "reports" / "recompute_observation_20260411_v0.json", {"cascade_analysis": {"trigger_propagation_confirmed": True}, "observation_outcome": {"next_decision_layer": "AWAIT_POST_RECOMPUTE_OBSERVATION"}, "interpretation_summary": {"surfaces_triggering_recompute": 3, "trigger_propagation_confirmed": True, "material_cascade_confirmed": True}})
    _write_json(root / "formal" / "output" / "reports" / "post_recompute_observation_20260411_v0.json", {"summary": {"ruling_id": "MATERIAL_CASCADE_CONFIRMED", "next_action": "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS", "cascade_determination": "MATERIAL_CASCADE_OBSERVABLE"}, "post_recompute_ruling": {"ruling_id": "MATERIAL_CASCADE_CONFIRMED", "next_action": "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS"}})


def test_monitoring_path_reports_pending_completion_from_live_shape(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_RECOMPUTE_MONITORING_PATH_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, local_only=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_RECOMPUTE_MONITORING_PATH_PENDING_COMPLETION"
    assert report["summary"]["next_action"] == "DEFER_RULING_MONITOR_RECOMPUTE_COMPLETION"


def test_monitoring_path_reports_authority_local_only_when_post_ruling_says_so(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_RECOMPUTE_MONITORING_PATH_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, local_only=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_RECOMPUTE_MONITORING_PATH_AUTHORITY_LOCAL_ONLY"


def test_monitoring_path_reports_material_cascade_when_post_ruling_confirms_it(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_RECOMPUTE_MONITORING_PATH_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_material_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_RECOMPUTE_MONITORING_PATH_MATERIAL_CASCADE_CONFIRMED"
    assert report["summary"]["next_action"] == "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS"


def test_live_monitoring_path_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_RECOMPUTE_MONITORING_PATH_20260418_v0.json",
        "formal/output/reports/post_plan_recompute_monitoring_path_20260418_v0.json",
        "formal/python/tools/post_plan_recompute_monitoring_path_report.py",
        "formal/python/tests/test_post_plan_recompute_monitoring_path_report.py"
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_recompute_monitoring_path_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_RECOMPUTE_MONITORING_PATH_MATERIAL_CASCADE_CONFIRMED"
    assert report["summary"]["next_action"] == "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS"
