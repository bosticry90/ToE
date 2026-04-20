from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_post_cascade_explicit_exhaustion_decision_report as tool


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


def _write_declaration(path: Path, *, successor_decl: str = "", successor_gate: str = "") -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_post_cascade_closure_review_report": "formal/output/reports/post_plan_post_cascade_closure_review_20260418_v0.json",
                "post_plan_qft_theorem_gap_completion_tranche_report": "formal/output/reports/post_plan_qft_theorem_gap_completion_tranche_20260418_v0.json",
                "post_plan_em_theorem_gap_completion_tranche_report": "formal/output/reports/post_plan_em_theorem_gap_completion_tranche_20260418_v0.json",
                "post_plan_sr_theorem_gap_completion_tranche_report": "formal/output/reports/post_plan_sr_theorem_gap_completion_tranche_20260418_v0.json",
                "post_plan_program_state_conversion_review_wrapper_report": "formal/output/reports/post_plan_program_state_conversion_review_wrapper_20260418_v0.json"
            },
            "decision_policy": {
                "required_post_cascade_outcome": "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_BOUNDED_HOLD_RECORDED",
                "required_qft_outcome": "POST_PLAN_QFT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_em_outcome": "POST_PLAN_EM_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_sr_outcome": "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_wrapper_outcome": "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED",
                "required_wrapper_next_action": "REUSE_EXISTING_PROGRAM_STATE_CONVERSION_REVIEW_DOWNSTREAM_PATH_AND_KEEP_THEOREM_GAP_QUEUE_CLOSED",
                "required_current_family_scope": "POST_CASCADE_QFT_EM_SR_CONTINUATION_CHAIN_ONLY",
                "successor_reopen_rule": "ONLY_IF_NEW_DECLARED_SUCCESSOR_POINTER_IS_PRESENT_AND_MACHINE_PINNED",
                "lookalike_row_no_loop_rule": "NO_ADDITIONAL_LOOKALIKE_THEOREM_GAP_ROW_WITHOUT_NEW_DECLARED_SUCCESSOR_FAMILY",
                "new_declared_successor_declaration": successor_decl,
                "new_declared_successor_gate": successor_gate,
                "successor_next_action_if_declared": "EXECUTE_DECLARED_SUCCESSOR_FAMILY_ONCE"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY",
                    "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_REOPENED_BY_NEW_DECLARED_SUCCESSOR",
                    "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_REPAIR"
                ],
                "default_outcome": "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EVIDENCE_INCOMPLETE"
            }
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_post_cascade_closure_review_20260418_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_BOUNDED_HOLD_RECORDED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_qft_theorem_gap_completion_tranche_20260418_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_QFT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_em_theorem_gap_completion_tranche_20260418_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_EM_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_sr_theorem_gap_completion_tranche_20260418_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_program_state_conversion_review_wrapper_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED",
                "next_action": "REUSE_EXISTING_PROGRAM_STATE_CONVERSION_REVIEW_DOWNSTREAM_PATH_AND_KEEP_THEOREM_GAP_QUEUE_CLOSED",
            }
        },
    )


def test_post_cascade_exhaustion_defaults_to_exhausted_without_successor(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY"
    assert report["summary"]["successor_declared"] is False
    assert report["summary"]["next_action"] == "AUTHOR_NEW_DECLARED_SUCCESSOR_FAMILY_OR_ACCEPT_TERMINAL_EXHAUSTION_READ"


def test_post_cascade_exhaustion_reopens_when_successor_is_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_20260419_v0.json"
    successor_decl = "formal/docs/release/POST_PLAN_SUCCESSOR_FAMILY_20260419_v0.json"
    successor_gate = "formal/python/tests/test_post_plan_successor_family_20260419_gate.py"
    _write_declaration(declaration_path, successor_decl=successor_decl, successor_gate=successor_gate)
    _seed_inputs(tmp_path)
    _write_json(tmp_path / successor_decl, {"schema_id": "POST_PLAN_SUCCESSOR_FAMILY_20260419_v0"})
    _write_text(tmp_path / successor_gate, "def test_gate():\n    assert True\n")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_REOPENED_BY_NEW_DECLARED_SUCCESSOR"
    assert report["summary"]["successor_declared"] is True
    assert report["summary"]["next_action"] == "EXECUTE_DECLARED_SUCCESSOR_FAMILY_ONCE"


def test_live_post_cascade_exhaustion_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_20260419_v0.json",
        "formal/output/reports/post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json",
        "formal/python/tools/post_plan_post_cascade_explicit_exhaustion_decision_report.py",
        "formal/python/tests/test_post_plan_post_cascade_explicit_exhaustion_decision_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY"
    assert report["summary"]["successor_declared"] is False
    assert report["summary"]["next_action"] == "AUTHOR_NEW_DECLARED_SUCCESSOR_FAMILY_OR_ACCEPT_TERMINAL_EXHAUSTION_READ"