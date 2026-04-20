from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_stat_fresh_movement_evidence_surface_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_REDUCTION_REACTIVATION_PROGRAM_20260419_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
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
                "stat_dossier_declaration": "formal/docs/release/dossier.json",
                "fresh_movement_qualification_report": "formal/output/reports/qualification.json",
                "stat_reactivation_tranche_report": "formal/output/reports/reactivation.json",
                "prior_stat_completion_tranche_report": "formal/output/reports/prior.json",
                "blocker_burn_dashboard_report": "formal/output/reports/dashboard.json",
                "theorem_gap_row_outcome_trend_report": "formal/output/reports/trend.json",
                "post_plan_target_map_report": "formal/output/reports/target_map.json",
                "stat_target_doc": "formal/docs/paper/stat.md",
                "stat_artifact": "formal/output/stat.json",
                "stat_gate": "formal/python/tests/test_stat_gate.py",
                "historical_stat_candidate_decision_doc": "formal/docs/release/tgc72.md",
                "historical_stat_checkpoint_doc": "formal/docs/release/tgc74.md",
            },
            "evidence_policy": {
                "required_dossier_outcome": "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_MATERIALIZED",
                "required_reactivation_outcome": "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE",
                "required_prior_completion_outcome": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_target_row": "ROW-PILLAR-STAT-001",
                "required_target_route_class": "THEOREM_GAP_PROGRAM",
                "required_target_next_action": "EXECUTE_PINNED_THEOREM_GAP_PROGRAM_AND_REQUIRE_BLOCKER_DELTA_NEGATIVE",
                "required_default_selected_row": "ROW-PILLAR-STAT-001",
                "required_measurable_blocker_delta_criterion": "NEGATIVE_THEOREM_GAP_DELTA_ATTRIBUTABLE_TO_STAT_REACTIVATION_FAMILY",
                "required_artifact_id": "stat_empirical_comparison_packet_04_v0",
                "required_artifact_status": "RUN_BOUNDED_v0_NONCLAIM",
                "required_artifact_decision": "INCONCLUSIVE_v0",
                "required_artifact_evidence_tier": "INTERMEDIATE_v0",
                "required_candidate_state_token": "TGC72_CONTINUATION_CANDIDATE_STATE_v0: NEXT_STAT_PACKET04_CONTINUATION_PACKAGE_PINNED",
                "required_checkpoint_state_token": "TGC74_EXECUTION_STATE_v0: NEXT_BOUNDED_STAT_PACKET04_CONTINUATION_INCREMENT_EXECUTION_CHECKPOINT_PINNED",
                "freshness_trigger_rule": "NEGATIVE_THEOREM_GAP_DELTA_PLUS_STAT_DEFAULT_SELECTION_REQUIRED_BEFORE_AUTHORIZATION",
            },
            "evidence_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING",
                    "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_FRESH_MOVEMENT_MACHINE_PINNED",
                    "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_CONTRACT_VIOLATION",
                    "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, theorem_gap_delta: int = 0, selected_row: str = "NONE") -> None:
    _write_json(
        root / "formal" / "docs" / "release" / "dossier.json",
        {
            "status": "ACTIVE_NONLIVE_NONCLAIM",
            "row_policy": {
                "row_id": "ROW-PILLAR-STAT-001",
                "required_route_class": "THEOREM_GAP_PROGRAM",
                "measurable_blocker_delta_criterion": "NEGATIVE_THEOREM_GAP_DELTA_ATTRIBUTABLE_TO_STAT_REACTIVATION_FAMILY",
                "bounded_execution_surface_declaration": "formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_20260419_v0.json",
            }
        },
    )
    qualification_outcome = (
        "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_STAT_DEFAULT_SELECTED"
        if selected_row == "ROW-PILLAR-STAT-001"
        else "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_NO_ROW_SELECTED"
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qualification.json",
        {
            "summary": {
                "terminal_outcome": qualification_outcome,
                "default_selected_row": "ROW-PILLAR-STAT-001",
                "selected_row": selected_row,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "reactivation.json",
        {"summary": {"terminal_outcome": "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "prior.json",
        {"summary": {"terminal_outcome": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "dashboard.json",
        {"blocker_scoreboard": {"delta_by_class": {"THEOREM_GAP": theorem_gap_delta}}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "trend.json",
        {
            "objective_quality": {
                "inputs": {
                    "row_outcome_counts": {
                        "ROW-PILLAR-STAT-001": {"total": 0, "success": 0, "no_change": 0}
                    }
                }
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "target_map.json",
        {
            "routed_rows": [
                {
                    "row_id": "ROW-PILLAR-STAT-001",
                    "route_class": "THEOREM_GAP_PROGRAM",
                    "authoritative_next_action": "EXECUTE_PINNED_THEOREM_GAP_PROGRAM_AND_REQUIRE_BLOCKER_DELTA_NEGATIVE",
                }
            ]
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "stat.md",
        "formal/output/stat.json\nformal/python/tests/test_stat_gate.py\n",
    )
    _write_json(
        root / "formal" / "output" / "stat.json",
        {
            "artifact_id": "stat_empirical_comparison_packet_04_v0",
            "payload": {
                "status": "RUN_BOUNDED_v0_NONCLAIM",
                "decision": "INCONCLUSIVE_v0",
                "evidence_tier": "INTERMEDIATE_v0",
            },
        },
    )
    _write_text(root / "formal" / "python" / "tests" / "test_stat_gate.py", "def test_gate():\n    assert True\n")
    _write_text(
        root / "formal" / "docs" / "release" / "tgc72.md",
        "TGC72_CONTINUATION_CANDIDATE_STATE_v0: NEXT_STAT_PACKET04_CONTINUATION_PACKAGE_PINNED\n",
    )
    _write_text(
        root / "formal" / "docs" / "release" / "tgc74.md",
        "TGC74_EXECUTION_STATE_v0: NEXT_BOUNDED_STAT_PACKET04_CONTINUATION_INCREMENT_EXECUTION_CHECKPOINT_PINNED\n",
    )


def test_stat_evidence_surface_stays_ready_but_fail_closed_while_theorem_gap_delta_is_flat(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "STAT_EVIDENCE.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, theorem_gap_delta=0, selected_row="NONE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING"
    )
    assert (
        report["summary"]["next_action"]
        == "PIN_ONE_FRESH_STAT_ATTRIBUTABLE_THEOREM_GAP_DELTA_BEFORE_AUTHORIZATION"
    )


def test_stat_evidence_surface_marks_fresh_movement_when_negative_theorem_gap_delta_selects_stat(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "STAT_EVIDENCE.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, theorem_gap_delta=-1, selected_row="ROW-PILLAR-STAT-001")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_FRESH_MOVEMENT_MACHINE_PINNED"
    )
    assert report["summary"]["fresh_movement_machine_pinned"] is True


def test_live_stat_evidence_surface_registered_in_mirrors_and_dossier() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_20260419_v0.json",
        "formal/output/reports/post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json",
        "formal/python/tools/post_plan_stat_fresh_movement_evidence_surface_report.py",
        "formal/python/tests/test_post_plan_stat_fresh_movement_evidence_surface_report.py",
    ]
    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
    )
    assert (
        report["summary"]["terminal_outcome"]
        == "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING"
    )

    dossier = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_row_reopen_dossier_stat_20260419_v0.json"
    )
    assert (
        dossier["summary"]["additional_bound_surfaces"]["stat_fresh_movement_evidence_surface_report"]
        == "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING"
    )
