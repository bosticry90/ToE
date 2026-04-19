from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROMOTION_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json"


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _seed_protocol_and_policies(root: Path) -> None:
    _write_text(
        root / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
        "\n".join(
            [
                "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
                "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_EMISSION_RULE_v0: EMIT_ONLY_ON_GOVERNED_PROMOTION_REVIEW_PROMOTE_DECISION",
                "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_REQUIRED_FIELDS_v0: TARGET_ROW_PLUS_TARGET_SEAM_PLUS_SOURCE_ARTIFACT_PLUS_SOURCE_PAYLOAD_PLUS_DECISION_RECORD_PLUS_SURFACE_DELTA_PLUS_PRESTATE_PLUS_POSTSTATE_PLUS_ROLLBACK_ANCHOR_PLUS_NONCLAIM_BOUNDARY",
                "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_NOOP_RULE_v0: HOLD_OR_REJECT_DECISION_EMITS_NO_CANONICAL_MUTATION",
                "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_FAIL_CLOSED_RULE_v0: MISSING_SURFACE_DELTA_OR_PREPOST_STATE_OR_ROLLBACK_ANCHOR_BLOCKS_PROMOTE",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
        "\n".join(
            [
                "SANDBOX_PROMOTION_PAYLOAD_DECISION_SET_v0: PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY",
                "SANDBOX_PROMOTION_PAYLOAD_FAIL_CLOSED_RULE_v0: MISSING_METADATA_OR_TARGET_BINDING_OR_CONTRADICTION_CHECK_OR_MUTATION_PLAN_IS_HARD_FAIL",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "release" / "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md",
        "\n".join(
            [
                "PROMOTION_GOVERNANCE_LANE_PROMOTION_RULE_v0: CANONICAL_ROW_AND_SEAM_STATE_CHANGE_ONLY_AFTER_GOVERNED_PROMOTION_PASS",
                "PROMOTION_GOVERNANCE_LANE_HARD_BOUNDARY_v0: NO_CANONICAL_PROMOTION_WITHOUT_PROMOTION_REVIEW",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md",
        "TOE_CANONICAL_ACTION_PROMOTION_REQUIRES_v0: THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT\n",
    )


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "payload_record": "formal/output/reports/sandbox_promotion_cosmo_sr_cycle07_payload_record_20260419_v0.json",
                "payload_requirements": "formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
                "pilot_binding": "formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
                "sandbox_execution_report": "formal/output/reports/post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json",
                "canonical_mutation_protocol": "formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
                "promotion_lane_policy": "formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md",
                "canonical_action_promotion_standard": "formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md",
            },
            "execution_policy": {
                "required_pilot_track_id": "SANDBOX_PROMOTION_PILOT_COSMO_SR_CYCLE07",
                "required_target_row": "ROW-SEAM-COSMO-SR-001",
                "required_target_seam": "SEAM-COSMO-SR",
                "required_sandbox_terminal_outcome": "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED",
                "required_payload_decision_boundary": "PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY",
                "required_payload_artifact_class": "PROMOTION_CANDIDATE_SANDBOX_ARTIFACT",
                "required_delta_class": "SEAM_DELTA_CLASS",
                "required_promotion_readiness": "READY_FOR_PROMOTION_REVIEW",
                "required_artifact_adjudication_for_promote": "DISCHARGED",
                "hold_reason_if_not_discharged": "ARTIFACT_NOT_YET_DISCHARGED_OR_CANONICAL_ROW_TRUTH_CHANGE_NOT_YET_EARNED",
                "reject_reason_if_payload_ineligible": "PAYLOAD_NOT_PROMOTION_CANDIDATE_OR_CONTRADICTION_CHECK_NOT_PASSING",
                "required_wrapper_next_action_on_promote": "EMIT_CANONICAL_MUTATION_PROTOCOL_AND_UPDATE_ROW_STATE",
                "required_wrapper_next_action_on_hold": "REPAIR_OR_EXTEND_COSMO_SR_SANDBOX_EVIDENCE_BEFORE_ANY_CANONICAL_MUTATION",
                "required_wrapper_next_action_on_reject": "RETURN_ARTIFACT_TO_SANDBOX_SUPPORT_ONLY_OR_REPAIR_METADATA",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_OUTCOME",
                "no_loop_rule": "ONE_SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_LAYER_ONLY",
                "allowed_outcomes": [
                    "SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED",
                    "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED",
                    "SANDBOX_PROMOTION_GOVERNED_REVIEW_REJECT_DECISION_EMITTED",
                    "SANDBOX_PROMOTION_GOVERNED_REVIEW_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_SANDBOX_PROMOTION_GOVERNED_REVIEW_REPAIR",
                ],
                "default_outcome": "SANDBOX_PROMOTION_GOVERNED_REVIEW_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _write_pilot_binding(path: Path) -> None:
    _write_json(
        path,
        {
            "pilot_binding": {
                "pilot_track_id": "SANDBOX_PROMOTION_PILOT_COSMO_SR_CYCLE07",
                "target_row_id": "ROW-SEAM-COSMO-SR-001",
                "target_seam_id": "SEAM-COSMO-SR",
                "required_artifact_class": "SCIENTIFIC_DELTA_SANDBOX_ARTIFACT",
                "required_delta_class": "SEAM_DELTA_CLASS",
            }
        },
    )


def _write_payload(path: Path, *, artifact_class: str = "PROMOTION_CANDIDATE_SANDBOX_ARTIFACT") -> None:
    _write_json(
        path,
        {
            "contract_bindings": {
                "payload_requirements": "formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
                "pilot_binding": "formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
                "governed_review_wrapper": "formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json",
                "canonical_mutation_protocol": "formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
            },
            "artifact_pointer": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
            "metadata_record": {
                "artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0",
                "artifact_class": artifact_class,
                "delta_class": "SEAM_DELTA_CLASS",
                "target_binding": {
                    "row_id": "ROW-SEAM-COSMO-SR-001",
                    "seam_id": "SEAM-COSMO-SR",
                },
                "contradiction_check": {
                    "result": "PASS_NO_ACTIVE_CANONICAL_CONTRADICTION_BUT_ROW_TRUTH_REMAINS_UNCHANGED"
                },
                "promotion_readiness": "READY_FOR_PROMOTION_REVIEW",
            },
            "target_binding": {
                "row_id": "ROW-SEAM-COSMO-SR-001",
                "seam_id": "SEAM-COSMO-SR",
            },
            "contradiction_check_result": "PASS_NO_ACTIVE_CANONICAL_CONTRADICTION_BUT_ROW_TRUTH_REMAINS_UNCHANGED",
            "governed_test_selection": {
                "selected_tests": [
                    "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py"
                ]
            },
            "mutation_plan": {
                "mutation_protocol": "formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
                "candidate_canonical_surfaces_to_change_if_promoted": [
                    "State_of_the_Theory.md"
                ],
                "prestate_tokens": [
                    "ROW-SEAM-COSMO-SR-001: NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED"
                ],
                "poststate_tokens_if_promoted": [
                    "ROW-SEAM-COSMO-SR-001: GOVERNED_PROMOTION_REVIEW_PASS_PENDING_CANONICAL_WRITEBACK"
                ],
                "rollback_anchor": "formal/output/reports/post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json",
            },
            "decision_boundary": "PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY",
        },
    )


def _write_sandbox_report(path: Path) -> None:
    _write_json(
        path,
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED",
                "target_row_id": "ROW-SEAM-COSMO-SR-001",
                "target_seam_id": "SEAM-COSMO-SR",
                "promotion_earned": False,
                "next_action": "RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE",
            }
        },
    )


def _write_artifact(path: Path, *, adjudication: str) -> None:
    _write_json(
        path,
        {
            "artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0",
            "seam_id": "SEAM-COSMO-SR",
            "adjudication": {"value": adjudication},
        },
    )


def test_wrapper_holds_when_artifact_not_discharged(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    _seed_protocol_and_policies(tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json"
    )
    _write_declaration(declaration_path)
    _write_pilot_binding(
        tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json"
    )
    _write_payload(
        tmp_path / "formal" / "output" / "reports" / "sandbox_promotion_cosmo_sr_cycle07_payload_record_20260419_v0.json"
    )
    _write_sandbox_report(
        tmp_path / "formal" / "output" / "reports" / "post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json"
    )
    _write_artifact(
        tmp_path / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        adjudication="NOT_YET_DISCHARGED",
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED"
    assert report["summary"]["governed_decision"] == "hold"
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_wrapper_promotes_when_payload_is_eligible_and_artifact_is_discharged(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    _seed_protocol_and_policies(tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json"
    )
    _write_declaration(declaration_path)
    _write_pilot_binding(
        tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json"
    )
    _write_payload(
        tmp_path / "formal" / "output" / "reports" / "sandbox_promotion_cosmo_sr_cycle07_payload_record_20260419_v0.json"
    )
    _write_sandbox_report(
        tmp_path / "formal" / "output" / "reports" / "post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json"
    )
    _write_artifact(
        tmp_path / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        adjudication="DISCHARGED",
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED"
    assert report["summary"]["canonical_mutation_emitted"] is True
    assert report["emitted_mutation_instruction"]["mutation_protocol"] == "formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md"


def test_wrapper_rejects_payload_that_is_not_promotion_candidate(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    _seed_protocol_and_policies(tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json"
    )
    _write_declaration(declaration_path)
    _write_pilot_binding(
        tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json"
    )
    _write_payload(
        tmp_path / "formal" / "output" / "reports" / "sandbox_promotion_cosmo_sr_cycle07_payload_record_20260419_v0.json",
        artifact_class="SUPPORT_ONLY_SANDBOX_ARTIFACT",
    )
    _write_sandbox_report(
        tmp_path / "formal" / "output" / "reports" / "post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json"
    )
    _write_artifact(
        tmp_path / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        adjudication="DISCHARGED",
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SANDBOX_PROMOTION_GOVERNED_REVIEW_REJECT_DECISION_EMITTED"
    assert report["summary"]["governed_decision"] == "reject"


def test_live_wrapper_registered_in_repo_surfaces() -> None:
    promotion_policy_text = _read(PROMOTION_POLICY_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_refs = [
        "formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json",
        "formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
        "formal/output/reports/sandbox_promotion_cosmo_sr_cycle07_payload_record_20260419_v0.json",
        "formal/python/tools/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py",
        "formal/output/reports/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json",
        "formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py",
    ]

    for ref in required_refs:
        assert ref in state_text
        assert ref in roadmap_text

    assert "PROMOTION_GOVERNANCE_LANE_REVIEW_WRAPPER_v0: formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json" in promotion_policy_text
    assert "PROMOTION_GOVERNANCE_LANE_MUTATION_PROTOCOL_v0: formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md" in promotion_policy_text

    report = _read_json(REPORT_PATH)
    assert report["summary"]["terminal_outcome"] == "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED"
    assert report["summary"]["governed_decision"] == "hold"
    assert report["summary"]["canonical_mutation_emitted"] is False