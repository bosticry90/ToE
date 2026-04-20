from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_cosmo_theorem_gap_reactivation_tranche_report as tool


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
                "cosmo_dossier_report": "formal/output/reports/dossier.json",
                "prior_cosmo_completion_tranche_report": "formal/output/reports/prior.json",
                "post_plan_target_map_report": "formal/output/reports/target_map.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "blocker_burn_dashboard_report": "formal/output/reports/dashboard.json",
                "science_maturity_contradiction_report": "formal/output/reports/contradiction.json",
                "cosmo_target_doc": "formal/docs/paper/cosmo.md",
                "cosmo_artifact": "formal/output/cosmo.json",
                "cosmo_gate": "formal/python/tests/test_cosmo_gate.py",
            },
            "execution_policy": {
                "required_authorization_outcome": "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED",
                "required_qualification_outcome": "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_COSMO_OVERRIDE_SELECTED",
                "required_selected_row": "ROW-PILLAR-COSMO-001",
                "required_target_row": "ROW-PILLAR-COSMO-001",
                "required_target_route_class": "THEOREM_GAP_PROGRAM",
                "required_target_blocker_class": "THEOREM_GAP",
                "required_prior_outcome": "POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_target_decision": "INCONCLUSIVE_v0",
                "required_target_status": "RUN_BOUNDED_v0_NONCLAIM",
                "required_target_evidence_tier": "INTERMEDIATE_v0",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_EXECUTED_AND_PROMOTED",
                    "POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_EXPLICITLY_EXHAUSTED",
                    "POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_REPAIR",
                ],
                "default_outcome": "POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, promoted: bool = False) -> None:
    _write_json(root / "formal" / "output" / "reports" / "auth.json", {"summary": {"terminal_outcome": "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED", "selected_row": "ROW-PILLAR-COSMO-001"}})
    _write_json(root / "formal" / "output" / "reports" / "qual.json", {"summary": {"terminal_outcome": "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_COSMO_OVERRIDE_SELECTED"}})
    _write_json(root / "formal" / "output" / "reports" / "dossier.json", {"summary": {"row_id": "ROW-PILLAR-COSMO-001", "fresh_movement_machine_pinned": True}})
    _write_json(root / "formal" / "output" / "reports" / "prior.json", {"summary": {"terminal_outcome": "POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"}})
    _write_json(root / "formal" / "output" / "reports" / "target_map.json", {"routed_rows": [{"row_id": "ROW-PILLAR-COSMO-001", "route_class": "THEOREM_GAP_PROGRAM"}]})
    current_status = "GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE" if promoted else "THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_PINNED"
    physics_status = "PHYSICS_COMPLETE" if promoted else "THEOREM_GAP_OPEN"
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "\n".join(
            [
                "# Matrix",
                "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
                f"| ROW-PILLAR-COSMO-001 | pillar | COSMO | {current_status} | THEOREM_GAP | formal/docs/paper/cosmo.md | formal/output/cosmo.json | formal/python/tests/test_cosmo_gate.py | N/A | {physics_status} | PINNED |",
            ]
        ),
    )
    _write_json(root / "formal" / "output" / "reports" / "dashboard.json", {"blocker_scoreboard": {"movement_status": "DECREASING", "net_delta": -1}})
    _write_json(root / "formal" / "output" / "reports" / "contradiction.json", {"modeled_observations": [{"row_id": "ROW-PILLAR-COSMO-001", "observation_type": "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP"}]})
    _write_text(root / "formal" / "docs" / "paper" / "cosmo.md", "DERIVATION_TARGET_COSMO_EMPIRICAL_COMPARISON_PACKET_04_v0\nformal/output/cosmo.json\nformal/python/tests/test_cosmo_gate.py\n")
    _write_json(root / "formal" / "output" / "cosmo.json", {"artifact_id": "cosmo_empirical_comparison_packet_04_v0", "payload": {"status": "RUN_BOUNDED_v0_NONCLAIM", "decision": "INCONCLUSIVE_v0", "evidence_tier": "INTERMEDIATE_v0"}})
    _write_text(root / "formal" / "python" / "tests" / "test_cosmo_gate.py", "def test_gate():\n    assert True\n")


def test_cosmo_reactivation_can_promote_when_override_authorization_and_row_truth_change_exist(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "COSMO_REACTIVATION.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, promoted=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_EXECUTED_AND_PROMOTED"


def test_live_cosmo_reactivation_report_is_fail_closed_pending_authorization() -> None:
    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_theorem_gap_reactivation_tranche_20260419_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE"
