from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_stat_theorem_gap_completion_tranche_report as tool


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
                "post_plan_cosmo_tranche_report": "formal/output/reports/post_plan_cosmo_theorem_gap_completion_tranche_20260418_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "science_maturity_contradiction_report": "formal/output/reports/science_maturity_contradiction_report_20260416_v0.json",
                "stat_target_doc": "formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_04_v0.md",
                "stat_artifact": "formal/output/stat_empirical_comparison_packet_04_v0.json",
                "stat_gate": "formal/python/tests/test_stat_empirical_comparison_packet_04_gate.py"
            },
            "execution_policy": {
                "required_target_row": "ROW-PILLAR-STAT-001",
                "required_target_route_class": "THEOREM_GAP_PROGRAM",
                "required_target_blocker_class": "THEOREM_GAP",
                "required_queue_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "required_queue_second_active_row": "ROW-PILLAR-STAT-001",
                "required_cosmo_outcome": "POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_target_decision": "INCONCLUSIVE_v0",
                "required_target_status": "RUN_BOUNDED_v0_NONCLAIM",
                "required_target_evidence_tier": "INTERMEDIATE_v0"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_AND_PROMOTED",
                    "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                    "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED",
                    "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_REPAIR"
                ],
                "default_outcome": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, decision: str = "INCONCLUSIVE_v0") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "second_active_row": "ROW-PILLAR-STAT-001"
            }
        }
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_theorem_gap_completion_tranche_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"
            }
        }
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "routed_rows": [
                {
                    "row_id": "ROW-PILLAR-STAT-001",
                    "route_class": "THEOREM_GAP_PROGRAM"
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
                "| ROW-PILLAR-STAT-001 | pillar | STAT_DERIVATION_CHAIN | NEXT_BOUNDED_STAT_PACKET04_CONTINUATION_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_04_v0.md | formal/output/stat_empirical_comparison_packet_04_v0.json | formal/python/tests/test_stat_empirical_comparison_packet_04_gate.py | NOT_APPLICABLE_PILLAR_ROW | THEOREM_GAP_OPEN | PATH_PINNED_RUNTIME_RECORDED |"
            ]
        )
    )
    _write_json(root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json", {"blocker_scoreboard": {"movement_status": "DECREASING", "net_delta": -1}})
    _write_json(
        root / "formal" / "output" / "reports" / "science_maturity_contradiction_report_20260416_v0.json",
        {
            "modeled_observations": [
                {
                    "row_id": "ROW-PILLAR-STAT-001",
                    "observation_type": "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP"
                }
            ]
        }
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_04_v0.md",
        "\n".join(
            [
                "# Derivation Target: STAT Empirical Comparison Packet 04 v0",
                "DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_04_v0",
                "STAT_EMPIRICAL_PACKET_04_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM",
                "STAT_EMPIRICAL_PACKET_04_DECISION_v0: INCONCLUSIVE_v0",
                "formal/output/stat_empirical_comparison_packet_04_v0.json",
                "formal/python/tests/test_stat_empirical_comparison_packet_04_gate.py"
            ]
        )
    )
    _write_json(
        root / "formal" / "output" / "stat_empirical_comparison_packet_04_v0.json",
        {
            "artifact_id": "stat_empirical_comparison_packet_04_v0",
            "payload": {
                "status": "RUN_BOUNDED_v0_NONCLAIM",
                "decision": decision,
                "evidence_tier": "INTERMEDIATE_v0"
            }
        }
    )
    _write_text(root / "formal" / "python" / "tests" / "test_stat_empirical_comparison_packet_04_gate.py", "def test_gate():\n    assert True\n")


def test_stat_tranche_reports_nonpromoted_from_live_shape(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"
    assert report["summary"]["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert report["summary"]["row_truth_change_detected"] is False


def test_stat_tranche_reports_exhausted_when_pruned(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, decision="PRUNE_v0")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"


def test_live_stat_tranche_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json",
        "formal/output/reports/post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json",
        "formal/python/tools/post_plan_stat_theorem_gap_completion_tranche_report.py",
        "formal/python/tests/test_post_plan_stat_theorem_gap_completion_tranche_report.py"
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"
    assert report["summary"]["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert report["summary"]["row_truth_change_detected"] is False
