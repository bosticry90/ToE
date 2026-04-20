from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_post_cascade_successor_family_eligibility_review_report as tool


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


def _write_declaration(
    path: Path,
    *,
    selected_reopen_route: str = "NONE",
    selected_reopen_route_class: str = "",
    selected_reopen_route_family_declaration: str = "",
    selected_reopen_route_family_gate: str = "",
    selected_reopen_route_machine_pinned: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_post_cascade_explicit_exhaustion_decision_report": "formal/output/reports/post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "post_plan_physics_advancement_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
            },
            "eligibility_policy": {
                "required_exhaustion_outcome": "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY",
                "required_successor_declared": False,
                "required_fresh_movement_blocker_classes": ["THEOREM_GAP", "SEAM_INTEGRATION_GAP"],
                "authorization_mode": "AT_MOST_ONE",
                "selected_reopen_route": selected_reopen_route,
                "selected_reopen_route_class": selected_reopen_route_class,
                "selected_reopen_route_family_declaration": selected_reopen_route_family_declaration,
                "selected_reopen_route_family_gate": selected_reopen_route_family_gate,
                "selected_reopen_route_machine_pinned": selected_reopen_route_machine_pinned,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "eligibility_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE",
                    "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_ONE_ROUTE_AUTHORIZED",
                    "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_CONTRACT_VIOLATION",
                    "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, fresh_movement: bool = False) -> None:
    theorem_gap_delta = -1 if fresh_movement else 0
    seam_gap_delta = -1 if fresh_movement else 0
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY",
                "current_family_scope": "POST_CASCADE_QFT_EM_SR_CONTINUATION_CHAIN_ONLY",
                "successor_declared": False,
                "next_action": "AUTHOR_NEW_DECLARED_SUCCESSOR_FAMILY_OR_ACCEPT_TERMINAL_EXHAUSTION_READ",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        {
            "blocker_scoreboard": {
                "delta_by_class": {
                    "THEOREM_GAP": theorem_gap_delta,
                    "SEAM_INTEGRATION_GAP": seam_gap_delta,
                }
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "routed_rows": [
                {
                    "row_id": "ROW-SEAM-COSMO-SR-001",
                    "route_class": "EXECUTABLE_NOW",
                }
            ]
        },
    )


def test_successor_eligibility_defaults_to_none_when_no_fresh_movement(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, fresh_movement=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE"
    assert report["summary"]["selected_reopen_route"] == "NONE"
    assert report["summary"]["next_action"] == "ACCEPT_TERMINAL_EXHAUSTION_READ_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT_IS_MACHINE_PINNED"


def test_successor_eligibility_authorizes_one_route_when_fresh_movement_and_selection_are_pinned(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json"
    _write_declaration(
        declaration_path,
        selected_reopen_route="ROW-SEAM-COSMO-SR-001",
        selected_reopen_route_class="SEAM_CONTINUATION",
        selected_reopen_route_family_declaration="formal/docs/release/POST_PLAN_COSMO_SR_SUCCESSOR_FAMILY_20260419_v0.json",
        selected_reopen_route_family_gate="formal/python/tests/test_post_plan_cosmo_sr_successor_family_report.py",
        selected_reopen_route_machine_pinned=True,
    )
    _seed_inputs(tmp_path, fresh_movement=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_ONE_ROUTE_AUTHORIZED"
    assert report["summary"]["selected_reopen_route"] == "ROW-SEAM-COSMO-SR-001"
    assert report["summary"]["next_action"] == "AUTHOR_AND_EXECUTE_DECLARED_SUCCESSOR_FAMILY_ONCE"


def test_live_successor_eligibility_review_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json",
        "formal/output/reports/post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json",
        "formal/python/tools/post_plan_post_cascade_successor_family_eligibility_review_report.py",
        "formal/python/tests/test_post_plan_post_cascade_successor_family_eligibility_review_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE"
    assert report["summary"]["selected_reopen_route"] == "NONE"
    assert report["summary"]["next_action"] == "ACCEPT_TERMINAL_EXHAUSTION_READ_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT_IS_MACHINE_PINNED"
    assert report["summary"]["next_action"] == "ACCEPT_TERMINAL_EXHAUSTION_READ_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT_IS_MACHINE_PINNED"


def test_successor_eligibility_authorizes_one_route_when_fresh_movement_and_selection_are_pinned(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json"
    _write_declaration(
        declaration_path,
        selected_reopen_route="ROW-SEAM-COSMO-SR-001",
        selected_reopen_route_class="SEAM_CONTINUATION",
        selected_reopen_route_family_declaration="formal/docs/release/POST_PLAN_COSMO_SR_SUCCESSOR_FAMILY_20260419_v0.json",
        selected_reopen_route_family_gate="formal/python/tests/test_post_plan_cosmo_sr_successor_family_report.py",
        selected_reopen_route_machine_pinned=True,
    )
    _seed_inputs(tmp_path, fresh_movement=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_ONE_ROUTE_AUTHORIZED"
    assert report["summary"]["selected_reopen_route"] == "ROW-SEAM-COSMO-SR-001"
    assert report["summary"]["next_action"] == "AUTHOR_AND_EXECUTE_DECLARED_SUCCESSOR_FAMILY_ONCE"


def test_live_successor_eligibility_review_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json",
        "formal/output/reports/post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json",
        "formal/python/tools/post_plan_post_cascade_successor_family_eligibility_review_report.py",
        "formal/python/tests/test_post_plan_post_cascade_successor_family_eligibility_review_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE"
    assert report["summary"]["selected_reopen_route"] == "NONE"
    assert report["summary"]["next_action"] == "ACCEPT_TERMINAL_EXHAUSTION_READ_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT_IS_MACHINE_PINNED"