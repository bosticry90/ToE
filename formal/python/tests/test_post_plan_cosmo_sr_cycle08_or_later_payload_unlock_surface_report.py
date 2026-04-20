from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report as tool


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


def _write_declaration(
    path: Path,
    *,
    selected_unlock_payload_lane: str = "NONE",
    selected_unlock_payload_target_doc: str = "",
    selected_unlock_payload_artifact: str = "",
    selected_unlock_payload_gate: str = "",
    selected_unlock_payload_machine_pinned: bool = False,
    selected_unlock_payload_declared_nonredundant: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_cosmo_sr_bounded_continuation_family_report": "formal/output/reports/post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "cosmo_sr_cycle06_to_07_synthesis_doc": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_v0.md",
                "historical_cycle08_candidate_doc": "formal/docs/release/WS_10_T12_COSMO_SR_CYCLE08_ADDITIVE_CANDIDATE_v0.md",
            },
            "unlock_policy": {
                "required_continuation_outcome": "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE",
                "required_continuation_next_action": "DO_NOT_REOPEN_COSMO_SR_UNTIL_NEW_MACHINE_PINNED_CYCLE08_OR_LATER_PAYLOAD_EXISTS",
                "required_target_row": "ROW-SEAM-COSMO-SR-001",
                "required_target_route_class": "EXECUTABLE_NOW",
                "required_decision_rule": "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE08_ELSE_OPEN_QM_STAT_CYCLE08",
                "required_decision_boundary_status": "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
                "required_candidate_status": "WS_10_T12_COSMO_SR_CYCLE08_ADDITIVE_CANDIDATE_STATUS_v0: DECLARED_BOUNDED_NONREDUNDANT_PAYLOAD_v0",
                "required_candidate_payload_type": "Candidate payload type: `ONE_DOC_ONE_ARTIFACT_ONE_GATE`.",
                "authorization_mode": "AT_MOST_ONE",
                "minimum_allowed_cycle_index": 8,
                "selected_unlock_payload_lane": selected_unlock_payload_lane,
                "selected_unlock_payload_target_doc": selected_unlock_payload_target_doc,
                "selected_unlock_payload_artifact": selected_unlock_payload_artifact,
                "selected_unlock_payload_gate": selected_unlock_payload_gate,
                "selected_unlock_payload_machine_pinned": selected_unlock_payload_machine_pinned,
                "selected_unlock_payload_declared_nonredundant": selected_unlock_payload_declared_nonredundant,
            },
            "unlock_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_LOCKED_PENDING_MACHINE_PINNED_PAYLOAD",
                    "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED",
                    "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_CONTRACT_VIOLATION",
                    "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE",
                "next_action": "DO_NOT_REOPEN_COSMO_SR_UNTIL_NEW_MACHINE_PINNED_CYCLE08_OR_LATER_PAYLOAD_EXISTS",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "summary": {"terminal_outcome": "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"},
            "routed_rows": [
                {
                    "row_id": "ROW-SEAM-COSMO-SR-001",
                    "route_class": "EXECUTABLE_NOW",
                }
            ],
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_v0.md",
        "\n".join(
            [
                "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE08_ELSE_OPEN_QM_STAT_CYCLE08",
                "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
                "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "release" / "WS_10_T12_COSMO_SR_CYCLE08_ADDITIVE_CANDIDATE_v0.md",
        "\n".join(
            [
                "WS_10_T12_COSMO_SR_CYCLE08_ADDITIVE_CANDIDATE_STATUS_v0: DECLARED_BOUNDED_NONREDUNDANT_PAYLOAD_v0",
                "Candidate payload type: `ONE_DOC_ONE_ARTIFACT_ONE_GATE`.",
                "Candidate lane: `COSMO_SR_CYCLE08`.",
            ]
        ),
    )


def test_unlock_surface_stays_locked_without_machine_pinned_payload(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_20260419_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_LOCKED_PENDING_MACHINE_PINNED_PAYLOAD"
    )
    assert (
        report["summary"]["next_action"]
        == "WAIT_FOR_NEW_MACHINE_PINNED_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_BEFORE_REOPEN_AUTHORIZATION"
    )


def test_unlock_surface_authorizes_one_payload_when_cycle08_or_later_is_pinned(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_20260419_v0.json"
    )
    target_doc = "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE09_v0.md"
    artifact = "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle09_v0.json"
    gate = "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle09_gate.py"
    _write_declaration(
        declaration_path,
        selected_unlock_payload_lane="COSMO_SR_CYCLE09",
        selected_unlock_payload_target_doc=target_doc,
        selected_unlock_payload_artifact=artifact,
        selected_unlock_payload_gate=gate,
        selected_unlock_payload_machine_pinned=True,
        selected_unlock_payload_declared_nonredundant=True,
    )
    _seed_inputs(tmp_path)
    _write_text(tmp_path / target_doc, "Cycle09 target")
    _write_json(tmp_path / artifact, {"artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle09_v0"})
    _write_text(tmp_path / gate, "def test_gate():\n    assert True\n")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED"
    )
    assert report["summary"]["selected_unlock_payload_lane"] == "COSMO_SR_CYCLE09"


def test_unlock_surface_rejects_pre_cycle08_selection(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_20260419_v0.json"
    )
    target_doc = "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07B_v0.md"
    artifact = "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07b_v0.json"
    gate = "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07b_gate.py"
    _write_declaration(
        declaration_path,
        selected_unlock_payload_lane="COSMO_SR_CYCLE07",
        selected_unlock_payload_target_doc=target_doc,
        selected_unlock_payload_artifact=artifact,
        selected_unlock_payload_gate=gate,
        selected_unlock_payload_machine_pinned=True,
        selected_unlock_payload_declared_nonredundant=True,
    )
    _seed_inputs(tmp_path)
    _write_text(tmp_path / target_doc, "Cycle07 target")
    _write_json(tmp_path / artifact, {"artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle07b_v0"})
    _write_text(tmp_path / gate, "def test_gate():\n    assert True\n")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_CONTRACT_VIOLATION"
    )


def test_live_unlock_surface_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_20260419_v0.json",
        "formal/output/reports/post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json",
        "formal/python/tools/post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report.py",
        "formal/python/tests/test_post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json"
    )
    assert (
        report["summary"]["terminal_outcome"]
        == "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED"
    )
    assert report["summary"]["selected_unlock_payload_lane"] == "COSMO_SR_CYCLE08"
    assert (
        report["summary"]["next_action"]
        == "AUTHOR_NEW_COSMO_SR_CONTINUATION_FAMILY_AGAINST_SELECTED_MACHINE_PINNED_PAYLOAD"
    )