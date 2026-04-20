from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_cosmo_sr_bounded_continuation_family_report as tool


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


def _write_declaration(
    path: Path,
    *,
    selected_continuation_lane: str = "NONE",
    selected_continuation_target_doc: str = "",
    selected_continuation_artifact: str = "",
    selected_continuation_gate: str = "",
    selected_continuation_machine_pinned: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "post_plan_cosmo_sr_first_live_seam_tranche_report": "formal/output/reports/post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "cosmo_sr_cycle07_artifact": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
                "cosmo_sr_cycle06_to_07_synthesis_doc": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_v0.md",
                "historical_cycle08_candidate_doc": "formal/docs/release/WS_10_T12_COSMO_SR_CYCLE08_ADDITIVE_CANDIDATE_v0.md",
            },
            "execution_policy": {
                "required_target_row": "ROW-SEAM-COSMO-SR-001",
                "required_target_seam": "SEAM-COSMO-SR",
                "required_target_route_class": "EXECUTABLE_NOW",
                "required_row_blocker_class": "SEAM_INTEGRATION_GAP",
                "required_prior_outcome": "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED",
                "required_prior_next_action": "RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE",
                "required_prior_row_truth_change": False,
                "required_decision_rule": "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE08_ELSE_OPEN_QM_STAT_CYCLE08",
                "required_decision_boundary_status": "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
                "required_alternate_blocked_row": "ROW-SEAM-QM-STAT-001",
                "required_alternate_blocked_route_class": "BLOCKED_PENDING_AUTHORITY",
                "expected_cycle08_target_doc": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md",
                "expected_cycle08_artifact": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
                "expected_cycle08_gate": "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py",
                "selected_continuation_lane": selected_continuation_lane,
                "selected_continuation_target_doc": selected_continuation_target_doc,
                "selected_continuation_artifact": selected_continuation_artifact,
                "selected_continuation_gate": selected_continuation_gate,
                "selected_continuation_machine_pinned": selected_continuation_machine_pinned,
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_BLOCKER_MOVEMENT_RECORDED",
                    "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXECUTED_NONPROMOTED_CLOSEOUT",
                    "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE",
                    "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_CONTRACT_VIOLATION",
                    "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, seam_moved: bool = False, pin_cycle08: bool = False) -> None:
    seam_gap_delta = -1 if seam_moved else 0
    target_status = "GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE" if seam_moved else "NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED"
    target_physics_status = "PHYSICS_COMPLETE" if seam_moved else "NOT_PHYSICS_COMPLETE"
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "summary": {"terminal_outcome": "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"},
            "routed_rows": [
                {
                    "row_id": "ROW-SEAM-COSMO-SR-001",
                    "route_class": "EXECUTABLE_NOW",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                    "lane": "COSMO_SR_CYCLE07",
                    "current_status": target_status,
                    "physics_checkpoint_status": target_physics_status,
                },
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "route_class": "BLOCKED_PENDING_AUTHORITY",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                    "lane": "QM_STAT_CYCLE11",
                    "current_status": "NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED",
                    "physics_checkpoint_status": "NOT_PHYSICS_COMPLETE",
                },
            ],
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED",
                "row_truth_change_detected": False,
                "next_action": "RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        {"blocker_scoreboard": {"delta_by_class": {"SEAM_INTEGRATION_GAP": seam_gap_delta}}},
    )
    _write_json(
        root / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        {
            "artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0",
            "seam_id": "SEAM-COSMO-SR",
            "adjudication": {"value": "NOT_YET_DISCHARGED"},
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_v0.md",
        "\n".join(
            [
                "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE08_ELSE_OPEN_QM_STAT_CYCLE08",
                "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
                "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "release" / "WS_10_T12_COSMO_SR_CYCLE08_ADDITIVE_CANDIDATE_v0.md",
        "\n".join(
            [
                "Candidate lane: `COSMO_SR_CYCLE08`.",
                "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0",
                "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
                "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py",
            ]
        ),
    )
    if pin_cycle08:
        _write_text(
            root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md",
            "cycle08 target\n",
        )
        _write_json(
            root / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
            {"artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0"},
        )
        _write_text(
            root / "formal" / "python" / "tests" / "test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py",
            "def test_gate():\n    assert True\n",
        )


def test_defaults_to_explicit_exhaustion_when_no_machine_pinned_cycle08_exists(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, seam_moved=False, pin_cycle08=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE"
    assert report["summary"]["actual_cycle08_surfaces_pinned"] is False
    assert report["summary"]["next_action"] == "DO_NOT_REOPEN_COSMO_SR_UNTIL_NEW_MACHINE_PINNED_CYCLE08_OR_LATER_PAYLOAD_EXISTS"


def test_records_blocker_movement_when_seam_gap_delta_turns_negative(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, seam_moved=True, pin_cycle08=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_BLOCKER_MOVEMENT_RECORDED"
    assert report["summary"]["blocker_movement_detected"] is True


def test_contract_violation_when_none_selected_but_payload_marked_machine_pinned(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_20260419_v0.json"
    _write_declaration(
        declaration_path,
        selected_continuation_lane="NONE",
        selected_continuation_target_doc="formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md",
        selected_continuation_machine_pinned=True,
    )
    _seed_inputs(tmp_path, seam_moved=False, pin_cycle08=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_CONTRACT_VIOLATION"


def test_live_continuation_family_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_20260419_v0.json",
        "formal/output/reports/post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json",
        "formal/python/tools/post_plan_cosmo_sr_bounded_continuation_family_report.py",
        "formal/python/tests/test_post_plan_cosmo_sr_bounded_continuation_family_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE"
    assert report["summary"]["next_action"] == "DO_NOT_REOPEN_COSMO_SR_UNTIL_NEW_MACHINE_PINNED_CYCLE08_OR_LATER_PAYLOAD_EXISTS"