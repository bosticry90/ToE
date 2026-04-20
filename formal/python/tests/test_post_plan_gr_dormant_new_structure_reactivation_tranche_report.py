from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_gr_dormant_new_structure_reactivation_tranche_report as tool


REPO_ROOT = find_repo_root(Path(__file__))


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


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
                "successor_family_authorization_review_report": "formal/output/reports/auth.json",
                "fresh_movement_qualification_report": "formal/output/reports/qual.json",
                "gr_dossier_report": "formal/output/reports/dossier.json",
                "prior_gr_completion_tranche_report": "formal/output/reports/prior.json",
                "post_plan_target_map_report": "formal/output/reports/target_map.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "blocker_burn_dashboard_report": "formal/output/reports/dashboard.json",
                "science_maturity_contradiction_report": "formal/output/reports/contradiction.json",
                "gr_new_structure_blocker_file_map": "formal/docs/release/gr_blocker_map.json",
            },
            "execution_policy": {
                "required_authorization_outcome": "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED",
                "required_selected_row": "ROW-PILLAR-GR-001",
                "required_target_row": "ROW-PILLAR-GR-001",
                "required_target_route_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                "required_target_blocker_class": "THEOREM_GAP",
                "required_prior_outcome": "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED",
                "required_gr_rule": "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_EXECUTED_AND_PROMOTED",
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_EXPLICITLY_EXHAUSTED",
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_REPAIR",
                ],
                "default_outcome": "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, correct_route: bool) -> None:
    _write_json(root / "formal" / "output" / "reports" / "auth.json", {"summary": {"terminal_outcome": "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED", "selected_row": "ROW-PILLAR-GR-001"}})
    _write_json(root / "formal" / "output" / "reports" / "qual.json", {"summary": {"terminal_outcome": "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_NO_ROW_SELECTED"}})
    _write_json(root / "formal" / "output" / "reports" / "dossier.json", {"summary": {"row_id": "ROW-PILLAR-GR-001", "admissible_if_authorized": True}})
    _write_json(root / "formal" / "output" / "reports" / "prior.json", {"summary": {"terminal_outcome": "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"}})
    route_class = "FROZEN_NEW_STRUCTURE_BRANCH" if correct_route else "THEOREM_GAP_PROGRAM"
    next_step = "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY" if correct_route else "formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_05_v0.md"
    _write_json(root / "formal" / "output" / "reports" / "target_map.json", {"routed_rows": [{"row_id": "ROW-PILLAR-GR-001", "route_class": route_class, "authoritative_next_step": next_step}]})
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "\n".join(
            [
                "# Matrix",
                "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
                "| ROW-PILLAR-GR-001 | pillar | GR | SECOND_BOUNDED_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | x | y | z | N/A | THEOREM_GAP_OPEN | PINNED |",
            ]
        ),
    )
    _write_json(root / "formal" / "output" / "reports" / "dashboard.json", {"blocker_scoreboard": {"movement_status": "FLAT", "net_delta": 0}})
    _write_json(root / "formal" / "output" / "reports" / "contradiction.json", {"modeled_observations": [{"row_id": "ROW-PILLAR-GR-001", "observation_type": "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP"}]})
    _write_json(root / "formal" / "docs" / "release" / "gr_blocker_map.json", {"target_row": "ROW-PILLAR-GR-001", "authoritative_branch_classification": {"current_lane_class": route_class, "authoritative_next_step": next_step}})


def test_gr_reactivation_refuses_any_route_outside_the_dormant_package_branch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_REACTIVATION.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, correct_route=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE"


def test_live_gr_reactivation_report_is_fail_closed_pending_authorization() -> None:
    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_gr_dormant_new_structure_reactivation_tranche_20260419_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE"
