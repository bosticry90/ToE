from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_result_review_v0
    as review,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _raw() -> bytes:
    return review.artifact_bytes()


@lru_cache(maxsize=1)
def _report() -> dict[str, Any]:
    value = json.loads(_raw().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_result_review_regenerates_exactly_and_deterministically() -> None:
    raw = _raw()
    assert (ROOT / review.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert review.artifact_bytes() == raw


def test_all_thirteen_independent_custody_checks_pass() -> None:
    custody = _report()["custody_review"]
    assert custody["status"] == "ACCEPTED"
    assert custody["passed_check_count"] == custody["check_count"] == 13
    assert custody["failed_check_ids"] == []
    assert all(custody["checks"].values())
    assert custody["run_count"] == 6
    assert custody["role_payload_file_count"] == 12
    assert custody["auxiliary_record_count"] == 2
    assert custody["runtime_source_binding_count"] == 8
    assert custody["output_tree_sha256"] == review.EXPECTED_OUTPUT_TREE_SHA256


def test_all_three_saved_trajectory_pairs_are_byte_identical() -> None:
    audit = _report()["instrumentation_nonperturbation_review"]
    assert audit["status"] == "FROZEN_STORED_TRAJECTORY_GATE_PASSED"
    assert audit["pair_count"] == 3
    assert audit["checkpoint_count_including_initial"] == 17
    assert audit["packed_state_width"] == 352
    assert audit["controls_have_no_mechanism_payload"] is True
    for pair in audit["pairs"]:
        assert pair["shape"] == [17, 352]
        assert pair["all_17_checkpoint_arrays_exact"] is True
        assert pair["raw_c_order_bytes_exact"] is True
        assert (
            pair["instrumented_trajectory_sha256"]
            == pair["control_trajectory_sha256"]
        )
    assert "unsaved internal solver iterations" in audit["withheld_scope"]


def test_observable_semantics_block_is_exactly_localized() -> None:
    raw_review = _report()["raw_reconstruction_review"]
    assert raw_review["status"] == "BLOCKED"
    outcome = raw_review["frozen_assembler_outcome"]
    assert outcome == {
        "status": "BLOCKED",
        "evidence_result": "BLOCKED_OBSERVABLE_SEMANTICS",
        "evidence_diagnostic": "RAW_SUMMARY_RECOMPUTATION_MISMATCH",
        "evidence_detail": "iteration.share.THETA_KINEMATIC",
    }
    audit = raw_review["arithmetic_forensics"]
    assert audit["summary_record_count"] == 224
    assert audit["scalar_field_count_per_mapping"] == 1792
    assert audit["stored_raw_maximum_mismatch_count"] == 0
    assert audit["stored_normalized_mismatch_count"] == 0
    assert audit["stored_share_vs_numpy_producer_mismatch_count"] == 0
    assert (
        audit[
            "stored_share_vs_frozen_python_sum_verifier_mismatch_count"
        ]
        == 570
    )
    assert audit["maximum_python_sum_mismatch_ulp_distance"] == 2
    assert audit["forensic_classification"] == (
        "REDUCTION_ORDER_MISMATCH_BETWEEN_NUMPY_PRODUCER_AND_"
        "PYTHON_SCALAR_SUM_VERIFIER"
    )
    assert audit["evidence_bytes_modified"] is False
    assert audit["frozen_verifier_bypassed_for_mechanism_classification"] is False


def test_first_mismatch_matches_the_frozen_first_diagnostic() -> None:
    first = _report()["raw_reconstruction_review"]["arithmetic_forensics"][
        "first_frozen_verifier_mismatch"
    ]
    assert first["run_id"] == "MECHv0:R13_LOOSE:INSTRUMENTED"
    assert first["event_family"] == "iteration"
    assert first["step"] == 1
    assert first["iteration"] == 1
    assert first["block_id"] == "THETA_KINEMATIC"
    assert first["ulp_distance"] == 1
    assert first["numpy_reduction_total"] != first["python_scalar_sum_total"]


def test_public_classifier_fails_closed_and_assigns_no_hypothesis() -> None:
    classifier = _report()["classifier_review"]
    assert classifier["public_entry_point"] == "classify_from_raw_payloads"
    assert classifier["invocation_count"] == 2
    assert classifier["deterministic"] is True
    assert classifier["evidence_result"] == "BLOCKED_OBSERVABLE_SEMANTICS"
    assert classifier["evidence_diagnostic"] == (
        "RAW_SUMMARY_RECOMPUTATION_MISMATCH"
    )
    assert classifier["aggregate_mechanism_result"] == "BLOCKED"
    assert classifier["supported_mechanism_ids"] == []
    assert classifier["H_A_through_H_E_all_not_evaluated"] is True
    assert classifier["H_E_not_assigned"] is True
    assert set(classifier["hypothesis_status_by_id"].values()) == {
        "NOT_EVALUATED"
    }


def test_block_preserves_scientific_claim_boundaries() -> None:
    report = _report()
    assert report["verdict"] == "BLOCKED_OBSERVABLE_SEMANTICS"
    assert report["first_diagnostic"] == "RAW_SUMMARY_RECOMPUTATION_MISMATCH"
    preserved = report["preserved_scientific_core"]
    assert preserved["accepted_bounded_Maxwell_Dirac_E_REPRO"] == "PRESERVED"
    assert preserved["fourteen_row_robustness"] == "NUMERICALLY_BLOCKED"
    assert preserved["R13_root_mechanism"] == (
        "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK"
    )
    assert preserved["new_E_REPRO"] == "NONE"
    boundary = report["authority_boundary"]
    assert boundary["additional_execution_authorized"] is False
    assert boundary["retry_authorized"] is False
    assert boundary["payload_rewrite_authorized"] is False
    assert boundary["H_A_through_H_E_acceptance_authorized"] is False
    assert boundary["robustness_reclassification_authorized"] is False
    assert (
        boundary[
            "bounded_versioned_observable_semantics_reconciliation_authorized"
        ]
        is True
    )


def test_review_is_read_only_for_the_fourteen_preserved_outputs() -> None:
    output_root = ROOT / review.execution_v0.OUTPUT_ROOT_RELATIVE_PATH
    before = implementation_v0.directory_tree_sha256(output_root)
    review.build_report()
    after = implementation_v0.directory_tree_sha256(output_root)
    assert before == after == review.EXPECTED_OUTPUT_TREE_SHA256

