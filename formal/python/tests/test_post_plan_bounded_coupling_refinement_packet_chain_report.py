from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_bounded_coupling_refinement_packet_chain_report as tool


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
                "post_plan_authority_coupling_review_path_report": "formal/output/reports/post_plan_authority_coupling_review_path_20260418_v0.json",
                "bounded_coupling_refinement_packet_report": "formal/output/reports/bounded_coupling_refinement_packet_20260411_v0.json",
                "coupling_refinement_ruling_report": "formal/output/reports/coupling_refinement_ruling_20260411_v0.json",
                "authority_promotion_registration_report": "formal/output/reports/authority_promotion_registration_20260411_v0.json"
            },
            "execution_policy": {
                "required_authority_review_path_outcome": "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_MATERIALIZED",
                "required_authority_review_path_next_action": "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE",
                "required_execution_classification": "EXECUTION_VALID_BINDING_TIGHTENED",
                "required_packet_next_action": "EMIT_COUPLING_REFINEMENT_RULING",
                "required_ruling_id": "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
                "required_ruling_next_action": "PROMOTE_REVISED_BLOCKER_DEFINITION_TO_AUTHORITATIVE",
                "required_registration_completed": True,
                "required_registration_authoritative": True,
                "required_registration_next_action": "MONITOR_RECOMPUTE_SURFACES"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED",
                    "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_VALID_BUT_NONAUTHORITATIVE",
                    "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_NOT_FIT_FOR_AUTHORITY_USE",
                    "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_BLOCKED",
                    "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_REPAIR"
                ],
                "default_outcome": "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, valid_but_nonauthoritative: bool = False) -> None:
    _write_json(root / "formal" / "output" / "reports" / "post_plan_authority_coupling_review_path_20260418_v0.json", {"summary": {"terminal_outcome": "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_MATERIALIZED", "next_action": "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"}})
    _write_json(root / "formal" / "output" / "reports" / "bounded_coupling_refinement_packet_20260411_v0.json", {"summary": {"target_row_id": "ROW-SEAM-QM-STAT-001", "execution_classification": "EXECUTION_VALID_BINDING_TIGHTENED", "coupling_state": "TIGHTENED", "next_action": "EMIT_COUPLING_REFINEMENT_RULING"}})
    ruling_id = "COUPLING_REFINEMENT_VALID_BUT_STILL_NONAUTHORITATIVE" if valid_but_nonauthoritative else "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION"
    ruling_classification = "VALID_BUT_NONAUTHORITATIVE" if valid_but_nonauthoritative else "PROMOTION_SUPPORTED"
    ruling_next_action = "RETAIN_REVISED_BLOCKER_DEFINITION_AS_SECONDARY_STRENGTHENED" if valid_but_nonauthoritative else "PROMOTE_REVISED_BLOCKER_DEFINITION_TO_AUTHORITATIVE"
    _write_json(root / "formal" / "output" / "reports" / "coupling_refinement_ruling_20260411_v0.json", {"summary": {"ruling_id": ruling_id, "classification": ruling_classification, "next_action": ruling_next_action}, "ruling": {"ruling_id": ruling_id, "classification": ruling_classification, "next_action": ruling_next_action}})
    _write_json(root / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json", {"summary": {"registration_completed": not valid_but_nonauthoritative, "revised_definition_is_now_authoritative": not valid_but_nonauthoritative, "recompute_surfaces_triggered": 3 if not valid_but_nonauthoritative else 0, "next_action": "MONITOR_RECOMPUTE_SURFACES" if not valid_but_nonauthoritative else "RETAIN_REVISED_BLOCKER_DEFINITION_AS_SECONDARY_STRENGTHENED"}})


def test_packet_chain_reports_promotion_registered_from_live_shape(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, valid_but_nonauthoritative=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED"
    assert report["summary"]["next_action"] == "MONITOR_RECOMPUTE_SURFACES"


def test_packet_chain_reports_valid_but_nonauthoritative_when_ruling_stalls(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, valid_but_nonauthoritative=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_VALID_BUT_NONAUTHORITATIVE"


def test_live_packet_chain_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_20260418_v0.json",
        "formal/output/reports/post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json",
        "formal/python/tools/post_plan_bounded_coupling_refinement_packet_chain_report.py",
        "formal/python/tests/test_post_plan_bounded_coupling_refinement_packet_chain_report.py"
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED"
    assert report["summary"]["next_action"] == "MONITOR_RECOMPUTE_SURFACES"
