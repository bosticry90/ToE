from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_discharge_attempt_authorization_readiness_review_20260424_v0.json"
)
WITNESS_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_consistency_witness_binding_v0.json"
)
SURFACE_PATH = REPO_ROOT / "formal" / "output" / "stat_der02_bounded_discharge_attempt_surface_v0.json"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_der02_discharge_attempt_authorization_readiness_review_gate() -> None:
    review = _read_json(REVIEW_PATH)
    witness = _read_json(WITNESS_PATH)
    surface = _read_json(SURFACE_PATH)

    assert review["schema_id"] == "POST_RECOVERY_STAT_DER02_DISCHARGE_ATTEMPT_AUTHORIZATION_READINESS_REVIEW_20260424_v0"
    assert review["artifact_id"] == "post_recovery_stat_der02_discharge_attempt_authorization_readiness_review_20260424_v0"
    assert review["status"] == "DECLARATION_ONLY_DER02_DISCHARGE_ATTEMPT_AUTHORIZATION_READINESS_REVIEW_NONCLAIM"

    trigger = review["trigger"]
    assert trigger["source"] == "DER02_BOUNDED_DISCHARGE_ATTEMPT_SURFACE_AUTHORED"
    assert trigger["bounded_discharge_attempt_surface"] == "formal/output/stat_der02_bounded_discharge_attempt_surface_v0.json"
    assert trigger["bounded_discharge_attempt_surface_gate"] == "formal/python/tests/test_stat_der02_bounded_discharge_attempt_surface_gate.py"
    assert trigger["witness_artifact"] == "formal/output/stat_der02_regime_closure_consistency_witness_binding_v0.json"
    assert trigger["witness_gate"] == "formal/python/tests/test_stat_der02_regime_closure_consistency_witness_binding_gate.py"

    boundary = review["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_AUTHORIZATION_READINESS_REVIEW"
    assert boundary["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert boundary["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert boundary["review_packet_executes_discharge"] is False
    assert boundary["review_packet_counts_theorem_gap_delta"] is False
    assert boundary["stat_packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    question = review["authorization_question"]
    assert question["question_id"] == "DER02_ONE_BOUNDED_DISCHARGE_ATTEMPT_AUTHORIZATION_READINESS"
    assert question["answer"] == "YES_ONE_BOUNDED_DER02_DISCHARGE_ATTEMPT_AUTHORIZED_AS_NEXT_PACKET_NOT_EXECUTED_BY_THIS_REVIEW"

    readiness_inputs = review["readiness_inputs"]
    assert readiness_inputs["witness_artifact_present"] is True
    assert readiness_inputs["witness_gate_present"] is True
    assert readiness_inputs["bounded_discharge_attempt_surface_present"] is True
    assert readiness_inputs["bounded_discharge_attempt_surface_gate_present"] is True
    assert readiness_inputs["witness_status"] == witness["payload"]["status"]
    assert readiness_inputs["witness_result"] == witness["payload"]["regime_closure_consistency_witness_result"]
    assert readiness_inputs["bounded_discharge_attempt_surface_status"] == surface["payload"]["status"]
    assert readiness_inputs["bounded_discharge_attempt_surface_result"] == surface["payload"]["surface_result"]
    assert readiness_inputs["bounded_discharge_attempt_object_id"] == surface["payload"]["discharge_attempt_object"]["object_id"]
    assert readiness_inputs["attempt_scope"] == "THEOREM_BODY_TO_DISCHARGE_ONLY"
    assert readiness_inputs["fresh_movement_machine_pinned_before_attempt"] is False
    assert readiness_inputs["theorem_gap_delta_before_attempt"] == 0

    checks = review["authorization_checks"]
    assert checks["witness_binding_prerequisite_satisfied"] is True
    assert checks["bounded_discharge_attempt_surface_prerequisite_satisfied"] is True
    assert checks["surface_gate_contract_preserves_no_claim_boundary"] is True
    assert checks["attempt_scope_is_der02_local"] is True
    assert checks["attempt_scope_is_single_packet_only"] is True
    assert checks["success_failure_discriminator_declared"] is True
    assert checks["packet05_dependency_absent"] is True
    assert checks["seam_dependency_absent"] is True
    assert checks["gr_dependency_absent"] is True
    assert checks["rl10_dependency_absent"] is True
    assert checks["master_action_dependency_absent"] is True
    assert checks["promotion_dependency_absent"] is True
    assert checks["bounded_discharge_attempt_authorized_now"] is True
    assert checks["bounded_discharge_attempt_executed_by_this_review"] is False

    authorized = review["authorized_attempt_scope"]
    assert authorized["authorization_id"] == "STAT_DER02_ONE_BOUNDED_DISCHARGE_ATTEMPT_AUTHORIZATION_v0"
    assert authorized["authorization_state"] == "AUTHORIZED_ONE_FUTURE_BOUNDED_ATTEMPT_ONLY"
    assert authorized["authorized_next_packet"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_EXECUTION_PACKET_v0"
    assert authorized["authorized_attempt_count"] == 1
    assert "formal/output/stat_der02_regime_closure_consistency_witness_binding_v0.json" in authorized["authorized_inputs"]
    assert "formal/output/stat_der02_bounded_discharge_attempt_surface_v0.json" in authorized["authorized_inputs"]
    assert authorized["must_consume_surface_success_discriminator"] is True
    assert authorized["must_consume_surface_failure_discriminator"] is True
    assert authorized["must_preserve_packet05_seam_gr_rl10_master_action_exclusions"] is True
    assert authorized["expires_after_one_attempt_packet"] is True

    assert review["delta_counting_boundary"]["theorem_gap_delta_counted"] == 0
    assert review["delta_counting_boundary"]["may_count_delta_in_this_review"] is False

    execution = review["execution_boundary"]
    assert execution["execution_performed_by_this_review"] is False
    assert execution["execution_authorization_before_review"] == "NONE"
    assert execution["execution_authorization_after_review"] == "ONE_BOUNDED_DER02_DISCHARGE_ATTEMPT_ONLY"
    assert execution["new_execution_packet_authored"] is False
    assert execution["packet05_allowed"] is False
    assert execution["seam_work_allowed"] is False
    assert execution["gr_work_allowed"] is False
    assert execution["rl10_work_allowed"] is False
    assert execution["master_action_allowed"] is False
    assert execution["promotion_or_closure_language_allowed"] is False

    decision = review["authorization_decision"]
    assert decision["terminal_outcome"] == "STAT_DER02_DISCHARGE_ATTEMPT_AUTHORIZATION_READINESS_ONE_BOUNDED_ATTEMPT_AUTHORIZED_NOT_EXECUTED"
    assert decision["one_bounded_der02_discharge_attempt_authorized"] is True
    assert decision["bounded_discharge_attempt_executed_now"] is False
    assert decision["theorem_gap_delta_counted"] == 0
    assert decision["new_execution_packet_authored"] is False
    assert decision["execution_authorization"] == "ONE_BOUNDED_DER02_DISCHARGE_ATTEMPT_ONLY"

    validation = review["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert validation["focused_surface_gate_result"] == "GREEN_1_PASSED"
    assert "test_post_recovery_stat_der02_discharge_attempt_authorization_readiness_review_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert "formal/output/stat_der02_regime_closure_consistency_witness_binding_v0.json" in review[
        "expected_new_artifacts_for_next_commit_bundle"
    ]
    assert "formal/output/stat_der02_bounded_discharge_attempt_surface_v0.json" in review[
        "expected_new_artifacts_for_next_commit_bundle"
    ]

    assert review["payload_sha256"] == _payload_hash({k: v for k, v in review.items() if k != "payload_sha256"})