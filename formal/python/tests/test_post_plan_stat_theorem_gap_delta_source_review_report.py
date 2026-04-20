from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_stat_theorem_gap_delta_source_review_report as tool


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
                "stat_fresh_movement_evidence_surface_report": "formal/output/reports/evidence.json",
                "stat_packet05_lane_eligibility_review_report": "formal/output/reports/review.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "foundational_empirical_protocol": "formal/docs/release/protocol.md",
                "foundational_empirical_packet04_matrix": "formal/docs/paper/packet04.json",
                "foundational_empirical_packet05_progression_policy": "formal/docs/release/progression.md",
                "foundational_empirical_packet05_matrix": "formal/docs/paper/packet05.json",
                "empirical_packet05_decision_ledger": "formal/output/packet05_ledger.json",
                "stat_target_doc": "formal/docs/paper/stat.md",
                "stat_artifact": "formal/output/stat.json",
                "stat_gate": "formal/python/tests/test_stat_gate.py",
            },
            "delta_source_policy": {
                "required_evidence_outcome": "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING",
                "required_target_row": "ROW-PILLAR-STAT-001",
                "required_lane_key": "STAT",
                "required_blocker_class": "THEOREM_GAP",
                "required_physics_checkpoint_status": "THEOREM_GAP_OPEN",
                "required_artifact_id": "stat_empirical_comparison_packet_04_v0",
                "required_artifact_status": "RUN_BOUNDED_v0_NONCLAIM",
                "required_artifact_decision": "INCONCLUSIVE_v0",
                "required_artifact_evidence_tier": "INTERMEDIATE_v0",
                "required_protocol_packet04_cap_token": "FOUNDATIONAL_EMPIRICAL_PACKET_04_BASELINE_DECISION_v0: INCONCLUSIVE_ONLY_UNTIL_PACKET05_OR_HIGHER",
                "required_protocol_packet05_enablement_token": "FOUNDATIONAL_EMPIRICAL_PACKET_05_ENABLEMENT_v0: SELECTIVE_LANE_ENABLEMENT_ALLOWED_WITH_PACKET04_INCONCLUSIVE_AND_INTERMEDIATE_EVIDENCE",
                "required_protocol_packet05_ledger_token": "FOUNDATIONAL_EMPIRICAL_PACKET_05_DECISION_LEDGER_REQUIREMENT_v0: EXPLICIT_LEDGER_REQUIRED",
                "required_progression_bootstrap_token": "FOUNDATIONAL_EMPIRICAL_PACKET_05_ALLOWED_LANE_BOOTSTRAP_v0: GR_SR_CYCLE01",
                "required_progression_non_enabled_clause": "non-enabled lanes remain governed by packet-04 baseline policy.",
                "required_packet05_review_not_eligible_outcome": "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_NOT_ELIGIBLE_UNDER_CURRENT_BOOTSTRAP",
                "required_packet05_review_eligible_outcome": "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_ELIGIBLE_FOR_PACKET05_BOOTSTRAP",
                "required_packet05_bootstrap_lanes": ["GR", "SR"],
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_PACKET04_CAP_CONFIRMED",
                    "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_HIGHER_PACKET_PATH_VISIBLE",
                    "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, stat_packet05_enabled: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "evidence.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING",
                "target_row_id": "ROW-PILLAR-STAT-001",
                "selected_evidence_target_doc": "formal/docs/paper/stat.md",
                "selected_evidence_artifact": "formal/output/stat.json",
                "selected_evidence_gate": "formal/python/tests/test_stat_gate.py",
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "\n".join(
            [
                "# Matrix",
                "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
                "| ROW-PILLAR-STAT-001 | pillar | STAT | NEXT_BOUNDED_STAT_PACKET04_CONTINUATION_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | formal/docs/paper/stat.md | formal/output/stat.json | formal/python/tests/test_stat_gate.py | N/A | THEOREM_GAP_OPEN | PINNED |",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "release" / "protocol.md",
        "\n".join(
            [
                "FOUNDATIONAL_EMPIRICAL_PACKET_04_BASELINE_DECISION_v0: INCONCLUSIVE_ONLY_UNTIL_PACKET05_OR_HIGHER",
                "FOUNDATIONAL_EMPIRICAL_PACKET_05_ENABLEMENT_v0: SELECTIVE_LANE_ENABLEMENT_ALLOWED_WITH_PACKET04_INCONCLUSIVE_AND_INTERMEDIATE_EVIDENCE",
                "FOUNDATIONAL_EMPIRICAL_PACKET_05_DECISION_LEDGER_REQUIREMENT_v0: EXPLICIT_LEDGER_REQUIRED",
            ]
        ),
    )
    _write_json(
        root / "formal" / "docs" / "paper" / "packet04.json",
        {
            "rows": {
                "STAT": {
                    "doc_path": "formal/docs/paper/stat.md",
                    "artifact_path": "formal/output/stat.json",
                    "gate_path": "formal/python/tests/test_stat_gate.py",
                }
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "progression.md",
        "\n".join(
            [
                "FOUNDATIONAL_EMPIRICAL_PACKET_05_ALLOWED_LANE_BOOTSTRAP_v0: GR_SR_CYCLE01",
                "non-enabled lanes remain governed by packet-04 baseline policy.",
            ]
        ),
    )
    enabled_lanes = ["GR", "SR"]
    rows = {"GR": {}, "SR": {}}
    ledger_rows = {"GR": {}, "SR": {}}
    if stat_packet05_enabled:
        enabled_lanes.append("STAT")
        rows["STAT"] = {
            "doc_path": "formal/docs/paper/stat_packet05.md",
            "artifact_path": "formal/output/stat_packet05.json",
            "gate_path": "formal/python/tests/test_stat_packet05_gate.py",
        }
        ledger_rows["STAT"] = {"decision": "INCONCLUSIVE_v0"}
    _write_json(root / "formal" / "docs" / "paper" / "packet05.json", {"enabled_lanes": enabled_lanes, "rows": rows})
    _write_json(root / "formal" / "output" / "packet05_ledger.json", {"rows": ledger_rows})
    _write_json(
        root / "formal" / "output" / "reports" / "review.json",
        {
            "summary": {
                "terminal_outcome": (
                    "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_ELIGIBLE_FOR_PACKET05_BOOTSTRAP"
                    if stat_packet05_enabled
                    else "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_NOT_ELIGIBLE_UNDER_CURRENT_BOOTSTRAP"
                ),
                "target_row_id": "ROW-PILLAR-STAT-001",
                "lane_key": "STAT",
            }
        },
    )
    _write_text(root / "formal" / "docs" / "paper" / "stat.md", "formal/output/stat.json\nformal/python/tests/test_stat_gate.py\n")
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


def test_delta_source_review_confirms_packet04_cap_when_stat_packet05_path_is_unpinned(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "STAT_DELTA_SOURCE.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, stat_packet05_enabled=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_PACKET04_CAP_CONFIRMED"
    assert report["summary"]["higher_packet_path_visible"] is False
    assert (
        report["summary"]["next_action"]
        == "RETAIN_STAT_PACKET04_FAIL_CLOSED_AND_REFRESH_PACKET05_LANE_ELIGIBILITY_ONLY_IF_BOOTSTRAP_CHANGES"
    )


def test_delta_source_review_marks_higher_packet_path_visible_when_stat_packet05_path_exists(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "STAT_DELTA_SOURCE.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, stat_packet05_enabled=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_HIGHER_PACKET_PATH_VISIBLE"
    assert report["summary"]["higher_packet_path_visible"] is True


def test_live_stat_delta_source_review_is_mirrored_and_bound_into_the_dossier() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_20260419_v0.json",
        "formal/output/reports/post_plan_stat_theorem_gap_delta_source_review_20260419_v0.json",
        "formal/python/tools/post_plan_stat_theorem_gap_delta_source_review_report.py",
        "formal/python/tests/test_post_plan_stat_theorem_gap_delta_source_review_report.py",
    ]
    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_stat_theorem_gap_delta_source_review_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_PACKET04_CAP_CONFIRMED"

    dossier = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_row_reopen_dossier_stat_20260419_v0.json"
    )
    assert (
        dossier["summary"]["additional_bound_surfaces"]["stat_theorem_gap_delta_source_review_report"]
        == "POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_PACKET04_CAP_CONFIRMED"
    )
    assert (
        report["summary"]["next_action"]
        == "RETAIN_STAT_PACKET04_FAIL_CLOSED_AND_REFRESH_PACKET05_LANE_ELIGIBILITY_ONLY_IF_BOOTSTRAP_CHANGES"
    )
