from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_cosmo_sr_selected_continuation_execution_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"
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


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_cosmo_sr_selected_continuation_family_report": "formal/output/reports/post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "selected_continuation_target_doc": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md",
                "selected_continuation_artifact": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
                "selected_continuation_gate": "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py"
            },
            "execution_policy": {
                "required_selected_family_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION",
                "required_selected_family_next_action": "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE",
                "required_target_row": "ROW-SEAM-COSMO-SR-001",
                "required_target_seam": "SEAM-COSMO-SR",
                "required_target_route_class": "EXECUTABLE_NOW",
                "required_row_blocker_class": "SEAM_INTEGRATION_GAP",
                "required_artifact_status": "CRITERIA_AND_TETRADECIC_EXCLUSION_PINNED_NONCLAIM",
                "required_artifact_adjudication": "NOT_YET_DISCHARGED",
                "nonpromoted_closeout_next_action": "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES",
                "promoted_next_action": "RERUN_TARGET_MAP_AND_REEVALUATE_SEAM_REROUTE_AND_MASTER_ACTION"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_NONPROMOTED_CLOSEOUT",
                    "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_AND_PROMOTED",
                    "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_REPAIR"
                ],
                "default_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EVIDENCE_INCOMPLETE"
            }
        },
    )


def _seed_inputs(root: Path, *, include_selected_family: bool = True) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION"
                if include_selected_family
                else "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE",
                "next_action": "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE",
                "selected_continuation_lane": "COSMO_SR_CYCLE08",
                "selected_continuation_machine_pinned": True,
                "target_row_id": "ROW-SEAM-COSMO-SR-001"
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "summary": {"terminal_outcome": "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"},
            "routed_rows": [{"row_id": "ROW-SEAM-COSMO-SR-001", "route_class": "EXECUTABLE_NOW"}]
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |\n"
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |\n"
        "| ROW-SEAM-COSMO-SR-001 | seam | COSMO_SR_CYCLE07 | NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED | SEAM_INTEGRATION_GAP | formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md | formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json | formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py | NOT_GOVERNANCE_COMPLETE | NOT_PHYSICS_COMPLETE | PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION |\n",
    )
    _write_json(
        root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        {"blocker_scoreboard": {"delta_by_class": {"SEAM_INTEGRATION_GAP": 0}}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md",
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0\n",
    )
    _write_json(
        root / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
        {
            "artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0",
            "seam_id": "SEAM-COSMO-SR",
            "status": "CRITERIA_AND_TETRADECIC_EXCLUSION_PINNED_NONCLAIM",
            "adjudication": {"value": "NOT_YET_DISCHARGED"}
        },
    )
    _write_text(
        root / "formal" / "python" / "tests" / "test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py",
        "def test_cosmo_sr_cycle08_artifacts_exist():\n    assert True\n",
    )


def test_selected_continuation_execution_records_nonpromoted_closeout(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_NONPROMOTED_CLOSEOUT"
    assert report["summary"]["selected_continuation_lane"] == "COSMO_SR_CYCLE08"
    assert report["summary"]["next_action"] == "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES"


def test_selected_continuation_execution_fails_without_selected_family(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, include_selected_family=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EVIDENCE_INCOMPLETE"


def test_live_selected_continuation_execution_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_20260419_v0.json",
        "formal/output/reports/post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json",
        "formal/python/tools/post_plan_cosmo_sr_selected_continuation_execution_report.py",
        "formal/python/tests/test_post_plan_cosmo_sr_selected_continuation_execution_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_NONPROMOTED_CLOSEOUT"
    assert report["summary"]["selected_continuation_lane"] == "COSMO_SR_CYCLE08"
