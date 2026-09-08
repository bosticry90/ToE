from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    gr_native_continuum_metric_variation_and_tensor_surface_packet_review_v0 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_authority_and_source_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_SOURCE_HASHES
    }
    review.build_review()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == review.AUTHORITY_AND_SOURCE_HASHES


def test_review_consumes_packet_and_returns_exact_terminal_block() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT"
    assert report["primary_diagnostic"] == "CK_FIREWALL_ACTION_SOURCE_CONFLICT"
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "FRESH_FULL_PRIORITY_RESPONSE_SELECTION_ONLY"
    )


def test_candidate_identity_and_source_blending_gates_pass() -> None:
    report = _report()
    assert report["candidate_authority_review"]["status"] == "PASS"
    assert report["candidate_authority_review"]["sole_source_id"] == (
        "TOE_CANDIDATE_MASTER_ACTION_v0"
    )
    blending = report["source_blending_review"]
    assert blending["status"] == "PASS"
    for key, value in blending.items():
        if key != "status":
            assert value is False, key


def test_ck_conflict_is_first_and_decisive_without_action_rewrite() -> None:
    conflict = _report()["C_k_conflict_review"]
    assert conflict["status"] == "FAIL"
    assert conflict["source_contains_C_k_multiplier_term"] is True
    assert conflict["retained_policy"] == "ALL_C_K_FAMILIES_ADMISSIBILITY_ONLY"
    assert conflict["action_embedding_selected"] is False
    assert conflict["action_variation_authorized"] is False
    assert conflict["action_term_deleted_or_declared_inactive"] is False
    assert conflict["projected_or_superseding_action_created"] is False
    assert conflict["readiness_possible_while_conflict_unresolved"] is False


def test_fail_fast_gate_accounting_is_exact() -> None:
    gates = _report()["fail_fast_review"]
    assert gates["gate_count"] == len(gates["rows"]) == 11
    assert gates["pass_count"] == 2
    assert gates["failure_count"] == 1
    assert gates["not_evaluated_count"] == 8
    assert gates["first_failed_gate_order"] == 3
    assert gates["first_failed_gate"] == "C_k authority consistency"
    assert gates["later_gate_may_override_first_failure"] is False
    assert gates["rows"] == review.GATE_RESULTS


def test_all_eight_downstream_gates_remain_unevaluated() -> None:
    downstream = _report()["downstream_gate_posture"]
    assert downstream["tetrad_route"] == "PROPOSED_COMPLETENESS_UNADJUDICATED"
    for key, value in downstream.items():
        if key != "tetrad_route":
            assert value == "NOT_EVALUATED", key


def test_terminal_outcome_is_incomplete_not_no_surface_spinor_or_comparator() -> None:
    reasoning = _report()["terminal_outcome_reasoning"]
    assert reasoning["selected"] == "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT"
    assert "candidate continuum working form" in reasoning["why_incomplete_not_no_surface"]
    assert "gate 6" in reasoning["why_not_spinor_primary"]
    assert "neither selected nor evaluated" in reasoning["why_not_comparator"]


def test_retained_scientific_posture_does_not_create_tensor_gravity() -> None:
    posture = _report()["retained_scientific_posture"]
    assert posture["bounded_discrete_Newton_Poisson_GR"] == "RETAINED"
    assert posture["gravitomagnetic_route"] == "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE"
    assert posture["Rep32"] == "SEPARATE_STRUCTURAL_MODEL"
    assert posture["stress_tensors"] == "COMPARISON_POLICIES_ONLY"
    assert posture["C_k"] == "ADMISSIBILITY_AUDIT_ONLY"
    assert posture["continuum_tensor_field_equation_created"] is False


def test_no_automatic_v1_or_future_route_is_authorized() -> None:
    report = _report()
    assert report["scope"]["automatic_v1_authorized"] is False
    assert len(report["fresh_priority_options"]) == 4
    assert all(row["authorized_now"] is False for row in report["fresh_priority_options"])


def test_review_executes_no_variation_comparator_or_promotion() -> None:
    scope = _report()["scope"]
    assert scope["independent_review_executed"] is True
    for key, value in scope.items():
        if key != "independent_review_executed":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "All later variational gates remain unevaluated",
        "No action rewrite",
        "tensor field equation",
        "master-action promotion",
        "automation",
    ):
        assert token in claim
