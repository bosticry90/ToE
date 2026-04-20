from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_cosmo_sr_selected_continuation_family_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"
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
                "post_plan_cosmo_sr_bounded_continuation_family_report": "formal/output/reports/post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json",
                "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report": "formal/output/reports/post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "selected_continuation_target_doc": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md",
                "selected_continuation_artifact": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
                "selected_continuation_gate": "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py"
            },
            "execution_policy": {
                "required_prior_continuation_outcome": "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE",
                "required_unlock_outcome": "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED",
                "required_unlock_next_action": "AUTHOR_NEW_COSMO_SR_CONTINUATION_FAMILY_AGAINST_SELECTED_MACHINE_PINNED_PAYLOAD",
                "required_target_row": "ROW-SEAM-COSMO-SR-001",
                "required_target_route_class": "EXECUTABLE_NOW",
                "required_selected_lane": "COSMO_SR_CYCLE08",
                "required_selected_machine_pinned": True,
                "required_selected_declared_nonredundant": True,
                "single_use_execution_mode": "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION",
                    "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_CONTRACT_VIOLATION",
                    "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE"
                ],
                "default_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE"
            }
        },
    )


def _seed_inputs(root: Path, *, include_unlock: bool = True) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED" if include_unlock else "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_EVIDENCE_INCOMPLETE",
                "next_action": "AUTHOR_NEW_COSMO_SR_CONTINUATION_FAMILY_AGAINST_SELECTED_MACHINE_PINNED_PAYLOAD",
                "selected_unlock_payload_lane": "COSMO_SR_CYCLE08",
                "selected_unlock_payload_machine_pinned": True,
                "selected_unlock_payload_declared_nonredundant": True,
                "target_row_id": "ROW-SEAM-COSMO-SR-001"
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "summary": {"terminal_outcome": "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"},
            "routed_rows": [{"row_id": "ROW-SEAM-COSMO-SR-001", "route_class": "EXECUTABLE_NOW"}]
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md",
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0\n",
    )
    _write_json(
        root / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
        {"artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0"},
    )
    _write_text(
        root / "formal" / "python" / "tests" / "test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py",
        "def test_cosmo_sr_cycle08_artifacts_exist():\n    assert True\n",
    )


def test_selected_continuation_family_materializes_ready_for_execution(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION"
    assert report["summary"]["selected_continuation_lane"] == "COSMO_SR_CYCLE08"
    assert report["summary"]["next_action"] == "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE"


def test_selected_continuation_family_fails_without_unlock(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, include_unlock=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE"


def test_live_selected_continuation_family_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_20260419_v0.json",
        "formal/output/reports/post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json",
        "formal/python/tools/post_plan_cosmo_sr_selected_continuation_family_report.py",
        "formal/python/tests/test_post_plan_cosmo_sr_selected_continuation_family_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION"
    assert report["summary"]["selected_continuation_lane"] == "COSMO_SR_CYCLE08"
