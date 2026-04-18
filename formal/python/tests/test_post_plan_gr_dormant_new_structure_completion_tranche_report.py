from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_gr_dormant_new_structure_completion_tranche_report as tool


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


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "completion_queue_report": "formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
                "post_plan_stat_tranche_report": "formal/output/reports/post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "science_maturity_contradiction_report": "formal/output/reports/science_maturity_contradiction_report_20260416_v0.json",
                "gr_new_structure_blocker_file_map": "formal/docs/release/GR_ROW_001_NEW_STRUCTURE_BLOCKER_FILE_MAP_20260418_v0.json",
                "gr_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "gr_new_structure_concept_packet_report": "formal/output/reports/gr_row_001_new_structure_concept_packet_20260413_v0.json",
                "gr_shared_interface_declaration_report": "formal/output/reports/gr_row_001_shared_interface_declaration_20260413_v0.json",
                "gr_comparator_specification_report": "formal/output/reports/gr_row_001_comparator_specification_20260413_v0.json",
                "deeper_blocker_definition_review": "formal/docs/release/DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json"
            },
            "execution_policy": {
                "required_target_row": "ROW-PILLAR-GR-001",
                "required_target_route_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                "required_target_blocker_class": "THEOREM_GAP",
                "required_queue_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "required_queue_heavy_structural_row": "ROW-PILLAR-GR-001",
                "required_stat_outcome": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_gr_rule": "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY",
                "required_retry_path_status": "EXHAUSTED_AND_NONAUTHORITATIVE_FOR_NEXT_STEP_SELECTION",
                "required_structural_gap_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "required_concept_outcome": "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED",
                "required_shared_interface_outcome": "GR_ROW_001_SHARED_INTERFACE_DECLARED",
                "required_comparator_outcome": "GR_ROW_001_COMPARATOR_SPEC_DECLARED"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXECUTED_AND_PROMOTED",
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED",
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_REPAIR"
                ],
                "default_outcome": "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, exhausted: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED", "heavy_structural_row": "ROW-PILLAR-GR-001"}}
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"}}
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "routed_rows": [
                {
                    "row_id": "ROW-PILLAR-GR-001",
                    "route_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                    "authoritative_next_step": "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY"
                }
            ]
        }
    )
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "\n".join(
            [
                "# Matrix",
                "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
                "| ROW-PILLAR-GR-001 | pillar | GR_DERIVATION_CHAIN | SECOND_BOUNDED_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_05_v0.md | formal/output/gr_empirical_comparison_packet_05_v0.json | formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py | NOT_APPLICABLE_PILLAR_ROW | THEOREM_GAP_OPEN | PATH_PINNED_RUNTIME_RECORDED |"
            ]
        )
    )
    _write_json(root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json", {"blocker_scoreboard": {"movement_status": "DECREASING", "net_delta": -1}})
    _write_json(
        root / "formal" / "output" / "reports" / "science_maturity_contradiction_report_20260416_v0.json",
        {"modeled_observations": [{"row_id": "ROW-PILLAR-GR-001", "observation_type": "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP"}]}
    )
    _write_json(
        root / "formal" / "docs" / "release" / "GR_ROW_001_NEW_STRUCTURE_BLOCKER_FILE_MAP_20260418_v0.json",
        {
            "target_row": "ROW-PILLAR-GR-001",
            "authoritative_branch_classification": {
                "current_lane_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                "retry_path_status": "EXHAUSTED_AND_NONAUTHORITATIVE_FOR_NEXT_STEP_SELECTION",
                "authoritative_next_step": "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY"
            }
        }
    )
    _write_json(root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json", {"summary": {"terminal_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"}})
    _write_json(root / "formal" / "output" / "reports" / "gr_row_001_new_structure_concept_packet_20260413_v0.json", {"summary": {"terminal_outcome": "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED"}})
    _write_json(root / "formal" / "output" / "reports" / "gr_row_001_shared_interface_declaration_20260413_v0.json", {"summary": {"terminal_outcome": "GR_ROW_001_SHARED_INTERFACE_DECLARED"}})
    comparator_summary = {
        "terminal_outcome": "GR_ROW_001_COMPARATOR_SPEC_DECLARED",
        "next_action": "KEEP_COMPARATOR_PACKAGE_VISIBLE_FOR_POSSIBLE_FUTURE_RESTART"
    }
    if exhausted:
        comparator_summary["package_status"] = "CANONICAL_DORMANT_GR_DESIGN_PACKAGE"
        comparator_summary["next_action"] = "STOP_DORMANT_GR_LAYERING_UNTIL_P75_AND_P77_CLEAR_OR_A_NEW_DISTINCT_AMBIGUITY_IS_IDENTIFIED"
    _write_json(root / "formal" / "output" / "reports" / "gr_row_001_comparator_specification_20260413_v0.json", {"summary": comparator_summary})
    _write_json(root / "formal" / "docs" / "release" / "DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json", {"review_basis": "PROGRAM_STATE_CONVERSION_REVIEW_PRESCRIBED_DEEPER_BLOCKER_DEFINITION_REVIEW"})


def test_gr_tranche_reports_nonpromoted_when_deeper_review_only_is_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, exhausted=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"
    assert report["summary"]["target_row_id"] == "ROW-PILLAR-GR-001"
    assert report["summary"]["row_truth_change_detected"] is False
    assert report["summary"]["deeper_blocker_definition_review_justified"] is True


def test_gr_tranche_reports_exhausted_when_capstone_frozen_package_is_complete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, exhausted=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"
    assert report["summary"]["explicit_exhaustion_detected"] is True


def test_live_gr_tranche_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_20260418_v0.json",
        "formal/output/reports/post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json",
        "formal/python/tools/post_plan_gr_dormant_new_structure_completion_tranche_report.py",
        "formal/python/tests/test_post_plan_gr_dormant_new_structure_completion_tranche_report.py"
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json")
    assert report["summary"]["target_row_id"] == "ROW-PILLAR-GR-001"
    assert report["summary"]["target_route_class"] == "FROZEN_NEW_STRUCTURE_BRANCH"
    assert report["summary"]["deeper_blocker_definition_review_justified"] is True
