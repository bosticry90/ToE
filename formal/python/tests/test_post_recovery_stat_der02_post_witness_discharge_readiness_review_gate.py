from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
READINESS_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_post_witness_discharge_readiness_review_20260424_v0.json"
)
WITNESS_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_consistency_witness_binding_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_der02_post_witness_discharge_readiness_review_gate() -> None:
    readiness = _read_json(READINESS_PATH)
    witness = _read_json(WITNESS_PATH)

    assert readiness["schema_id"] == "POST_RECOVERY_STAT_DER02_POST_WITNESS_DISCHARGE_READINESS_REVIEW_20260424_v0"
    assert readiness["artifact_id"] == "post_recovery_stat_der02_post_witness_discharge_readiness_review_20260424_v0"
    assert readiness["status"] == "DECLARATION_ONLY_POST_WITNESS_DISCHARGE_READINESS_REVIEW_NONCLAIM"

    trigger = readiness["trigger"]
    assert trigger["source"] == "DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_MATERIALIZED"
    assert trigger["witness_artifact"] == "formal/output/stat_der02_regime_closure_consistency_witness_binding_v0.json"
    assert trigger["witness_gate"] == "formal/python/tests/test_stat_der02_regime_closure_consistency_witness_binding_gate.py"

    boundary = readiness["frontier_boundary"]
    assert boundary["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert boundary["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["theorem_gap_delta_counted"] == 0
    assert boundary["stat_execution_packet_allowed"] is False
    assert boundary["stat_packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    question = readiness["readiness_question"]
    assert question["answer"] == "NOT_READY_FOR_DISCHARGE_ATTEMPT_AUTHORIZATION_MISSING_BOUNDED_DISCHARGE_ATTEMPT_SURFACE"

    state = readiness["post_witness_state"]
    assert state["witness_artifact_present"] is True
    assert state["witness_gate_present"] is True
    assert state["witness_status"] == witness["payload"]["status"]
    assert state["witness_result"] == witness["payload"]["regime_closure_consistency_witness_result"]
    assert state["witness_claims_der02_discharge"] is False
    assert state["witness_counts_theorem_gap_delta"] is False
    assert state["witness_authorizes_execution"] is False
    assert state["execution_authorization"] == "NONE"

    checks = readiness["readiness_checks"]
    assert checks["witness_binding_prerequisite_satisfied"] is True
    assert checks["witness_is_machine_pinned_nonclaim"] is True
    assert checks["witness_is_der02_local"] is True
    assert checks["packet05_dependency_absent"] is True
    assert checks["seam_dependency_absent"] is True
    assert checks["master_action_dependency_absent"] is True
    assert checks["theorem_body_discharge_attempt_surface_present"] is False
    assert checks["bounded_discharge_attempt_ready_now"] is False

    blocker = readiness["remaining_blocker"]
    assert blocker["missing_component_id"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_SURFACE_v0"
    assert blocker["missing_component_class"] == "DECLARATION_ONLY_DISCHARGE_ATTEMPT_BOUNDARY"
    assert len(blocker["minimum_required_future_fields"]) == 8

    decision = readiness["readiness_decision"]
    assert decision["terminal_outcome"] == "STAT_DER02_POST_WITNESS_DISCHARGE_READINESS_NOT_READY_ATTEMPT_SURFACE_MISSING"
    assert decision["witness_binding_prerequisite_satisfied"] is True
    assert decision["bounded_discharge_attempt_ready_now"] is False
    assert decision["remaining_missing_component"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_SURFACE_v0"
    assert decision["execution_authorization"] == "NONE"
    assert decision["theorem_gap_delta_counted"] == 0

    validation = readiness["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_der02_post_witness_discharge_readiness_review_gate.py" in validation["targeted_gate_command"]

    assert readiness["payload_sha256"] == _canonical_hash({k: v for k, v in readiness.items() if k != "payload_sha256"})