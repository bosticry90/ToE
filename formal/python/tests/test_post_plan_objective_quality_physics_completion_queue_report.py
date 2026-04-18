from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_objective_quality_physics_completion_queue_report as tool


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
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "post_plan_qm_tranche_report": "formal/output/reports/post_plan_qm_first_theorem_gap_tranche_20260418_v0.json",
                "theorem_gap_row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "theorem_gap_tranche_linkage_registry": "formal/docs/release/THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json",
                "seam_executable_path_normalization_report": "formal/output/reports/seam_executable_path_normalization_20260418_v0.json",
                "program_state_conversion_review": "formal/docs/release/PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json",
            },
            "queue_policy": {
                "eligible_route_classes": ["THEOREM_GAP_PROGRAM", "FROZEN_NEW_STRUCTURE_BRANCH"],
                "required_exhausted_row": "ROW-PILLAR-QM-001",
                "preferred_queue_order": [
                    "ROW-PILLAR-COSMO-001",
                    "ROW-PILLAR-STAT-001",
                    "ROW-PILLAR-GR-001"
                ],
                "required_first_active_row": "ROW-PILLAR-COSMO-001",
                "required_second_active_row": "ROW-PILLAR-STAT-001",
                "required_heavy_structural_row": "ROW-PILLAR-GR-001",
                "required_primary_executable_seam": "SEAM-COSMO-SR",
                "required_gr_route_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                "nonmoving_family_trigger_count": 3,
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                    "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_REPAIR",
                ],
                "default_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, include_stat: bool = True) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "routed_rows": [
                {
                    "row_id": "ROW-PILLAR-QM-001",
                    "lane": "QM_DERIVATION_CHAIN",
                    "route_class": "THEOREM_GAP_PROGRAM",
                    "current_status": "THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_PINNED",
                    "blocker_class": "THEOREM_GAP",
                    "authoritative_next_step": "formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_04_v0.md",
                    "primary_gate": "formal/python/tests/test_qm_empirical_comparison_packet_04_gate.py",
                },
                {
                    "row_id": "ROW-PILLAR-COSMO-001",
                    "lane": "COSMO_DERIVATION_CHAIN",
                    "route_class": "THEOREM_GAP_PROGRAM",
                    "current_status": "THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_PINNED",
                    "blocker_class": "THEOREM_GAP",
                    "authoritative_next_step": "formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_COMPARISON_PACKET_04_v0.md",
                    "primary_gate": "formal/python/tests/test_cosmo_empirical_comparison_packet_04_gate.py",
                },
                {
                    "row_id": "ROW-PILLAR-GR-001",
                    "lane": "GR_DERIVATION_CHAIN",
                    "route_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                    "current_status": "SECOND_BOUNDED_INCREMENT_EXECUTION_CHECKPOINT_PINNED",
                    "blocker_class": "THEOREM_GAP",
                    "authoritative_next_step": "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY",
                    "primary_gate": "formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py",
                },
            ]
            + (
                [
                    {
                        "row_id": "ROW-PILLAR-STAT-001",
                        "lane": "STAT_DERIVATION_CHAIN",
                        "route_class": "THEOREM_GAP_PROGRAM",
                        "current_status": "NEXT_BOUNDED_STAT_PACKET04_CONTINUATION_INCREMENT_EXECUTION_CHECKPOINT_PINNED",
                        "blocker_class": "THEOREM_GAP",
                        "authoritative_next_step": "formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_04_v0.md",
                        "primary_gate": "formal/python/tests/test_stat_empirical_comparison_packet_04_gate.py",
                    }
                ]
                if include_stat
                else []
            ),
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_qm_first_theorem_gap_tranche_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {
            "objective_quality": {
                "inputs": {
                    "row_outcome_counts": {
                        "ROW-PILLAR-QM-001": {"total": 3, "no_change": 3, "success": 0, "failure": 0},
                        "ROW-PILLAR-COSMO-001": {"total": 1, "no_change": 1, "success": 0, "failure": 0},
                        "ROW-PILLAR-GR-001": {"total": 0, "no_change": 0, "success": 0, "failure": 0},
                        "ROW-PILLAR-STAT-001": {"total": 0, "no_change": 0, "success": 0, "failure": 0},
                    },
                    "stagnation_rows": ["ROW-PILLAR-QM-001", "ROW-PILLAR-COSMO-001"],
                }
            }
        },
    )
    _write_json(
        root / "formal" / "docs" / "release" / "THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json",
        {
            "entries": [
                {"target_row": "ROW-PILLAR-QM-001"},
                {"target_row": "ROW-PILLAR-QM-001"},
                {"target_row": "ROW-PILLAR-QM-001"},
                {"target_row": "ROW-PILLAR-COSMO-001"},
            ]
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "seam_executable_path_normalization_20260418_v0.json",
        {
            "summary": {
                "authorized_executable_seams": ["SEAM-COSMO-SR"],
            }
        },
    )
    _write_json(
        root / "formal" / "docs" / "release" / "PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json",
        {
            "review_policy": {
                "default_next_action": "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW",
            }
        },
    )


def test_completion_queue_materializes_expected_order(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED"
    assert report["summary"]["queue_order"][:3] == [
        "ROW-PILLAR-COSMO-001",
        "ROW-PILLAR-STAT-001",
        "ROW-PILLAR-GR-001",
    ]
    assert report["summary"]["excluded_row"] == "ROW-PILLAR-QM-001"


def test_completion_queue_fails_when_required_row_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, include_stat=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_EVIDENCE_INCOMPLETE"


def test_live_completion_program_and_queue_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_PROGRAM_20260418_v0.md",
        "formal/docs/release/POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_20260418_v0.json",
        "formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
        "formal/python/tools/post_plan_objective_quality_physics_completion_queue_report.py",
        "formal/python/tests/test_post_plan_objective_quality_physics_completion_queue_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_objective_quality_physics_completion_queue_20260418_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED"
    assert report["summary"]["first_active_row"] == "ROW-PILLAR-COSMO-001"
    assert report["summary"]["second_active_row"] == "ROW-PILLAR-STAT-001"
    assert report["summary"]["excluded_row"] == "ROW-PILLAR-QM-001"
