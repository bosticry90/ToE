from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_review_v2
    as review_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v1
    as predecessor_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v2
    as reconciliation_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as raw_v3,
)


ROOT = find_repo_root(Path(__file__))
SOURCE_ROOT = ROOT / review_v2.SOURCE_OUTPUT_ROOT_RELATIVE_PATH
RESULT_ROOT = ROOT / reconciliation_v2.RESULT_OUTPUT_ROOT_RELATIVE_PATH


@lru_cache(maxsize=1)
def _raw_review() -> bytes:
    return review_v2.artifact_bytes()


@lru_cache(maxsize=1)
def _review() -> dict[str, Any]:
    value = json.loads(_raw_review().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    raw = _raw_review()
    assert (ROOT / review_v2.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert review_v2.artifact_bytes() == raw


def test_review_never_reads_actual_payload_arrays(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: Any, **_kwargs: Any) -> None:
        raise AssertionError("actual evidence payload loader called during packet review")

    monkeypatch.setattr(predecessor_v1, "_load_payloads", forbidden)
    monkeypatch.setattr(raw_v3, "_load_role_payload", forbidden)
    before = implementation_v0.directory_tree_sha256(SOURCE_ROOT)
    review = review_v2.build_review()
    after = implementation_v0.directory_tree_sha256(SOURCE_ROOT)
    assert before == after == reconciliation_v2.EXPECTED_SOURCE_OUTPUT_TREE_SHA256
    assert review["production_path_audit"]["actual_payload_arrays_read"] is False
    assert review["production_path_audit"]["actual_field_comparison_performed"] is False
    assert not RESULT_ROOT.exists()


def test_v1_foundation_is_reconstructed_exactly_fourteen_of_fourteen() -> None:
    foundation = _review()["reconstructed_v1_foundation"]
    assert foundation["status"] == "RECONSTRUCTED_EXACTLY"
    assert foundation["passed_check_count"] == foundation["check_count"] == 14
    assert all(foundation["checks"].values())


def test_all_twelve_independent_decision_contract_checks_pass() -> None:
    audit = _review()["decision_contract_audit"]
    assert audit["passed_check_count"] == audit["check_count"] == 12
    assert all(audit["checks"].values())


def test_all_mutation_controls_reach_the_required_production_terminal() -> None:
    audit = _review()["decision_contract_audit"]
    assert audit["controls"] == audit["expected_controls"]
    assert audit["controls"]["ALL_GATES_TRUE"] == "PREDICATE_INVARIANT"
    for control_id, terminal in audit["controls"].items():
        if control_id in {
            "ALL_GATES_TRUE",
            "PURE_ONE_TWO_ULP_NO_DECISION_CHANGE",
            "GREATER_THAN_TWO_ULP_NO_DECISION_CHANGE",
        }:
            assert terminal == "PREDICATE_INVARIANT"
        else:
            assert terminal == "BLOCKED_OBSERVABLE_DECISION_INSTABILITY"


def test_ulp_bins_are_exhaustive_and_descriptive_only() -> None:
    audit = _review()["decision_contract_audit"]
    one_two = audit["one_two_ulp_control"]
    larger = audit["greater_than_two_ulp_control"]
    assert sum(one_two["ulp_histogram"].values()) == 1792
    assert sum(larger["ulp_histogram"].values()) == 1792
    assert one_two["ulp_histogram"]["one_ulp_differences"] == 1
    assert one_two["ulp_histogram"]["two_ulp_differences"] == 1
    assert larger["ulp_histogram"]["greater_than_two_ulp_differences"] == 1
    assert one_two["terminal_classification"] == "PREDICATE_INVARIANT"
    assert larger["terminal_classification"] == "PREDICATE_INVARIANT"


def test_terminal_contract_is_closed_over_all_128_boolean_assignments() -> None:
    closure = _review()["decision_contract_audit"]["terminal_closure"]
    assert closure["boolean_assignment_count"] == 128
    assert closure["all_assignments_match_independent_oracle"] is True
    assert set(closure["reachable_terminal_labels"]) == {
        "PREDICATE_INVARIANT",
        "BLOCKED_OBSERVABLE_DECISION_INSTABILITY",
    }
    assert closure["incomplete_gate_map_rejected_preterminal"] is True
    assert closure["nonboolean_gate_rejected_preterminal"] is True


def test_review_accepts_packet_v2_and_authorizes_exactly_one_calculation() -> None:
    review = _review()
    assert review["verdict"] == reconciliation_v2.EXPECTED_REVIEW_VERDICT
    assert review["selected_next_target"] == reconciliation_v2.EXPECTED_REVIEW_NEXT_TARGET
    boundary = review["authority_boundary"]
    assert boundary["packet_v2_accepted"] is True
    assert boundary["calculation_authorized_count"] == 1
    assert boundary["calculation_executed_during_review"] is False
    assert boundary["independent_result_review_required"] is True
    assert boundary["simulation_authorized"] is False
    assert boundary["additional_packet_version_authorized"] is False


def test_accepted_authority_satisfies_real_preflight_without_reading_payloads(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: Any, **_kwargs: Any) -> None:
        raise AssertionError("payload loader called during preflight")

    monkeypatch.setattr(predecessor_v1, "_load_payloads", forbidden)
    before = implementation_v0.directory_tree_sha256(SOURCE_ROOT)
    authority = reconciliation_v2.preflight_authorized_calculation(ROOT)
    after = implementation_v0.directory_tree_sha256(SOURCE_ROOT)
    assert authority["result_root_absent"] is True
    assert authority["simulation_authorized"] is False
    assert authority["H_A_through_H_E_acceptance_authorized"] is False
    assert before == after == reconciliation_v2.EXPECTED_SOURCE_OUTPUT_TREE_SHA256
    assert not RESULT_ROOT.exists()


def test_review_preserves_scientific_nonclaim_boundary() -> None:
    review = _review()
    core = review["preserved_scientific_core"]
    assert core["fourteen_row_robustness"] == "NUMERICALLY_BLOCKED"
    assert core["descendant_materiality"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert core["R13_root_mechanism"] == "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK"
    assert core["new_E_REPRO"] == "NONE"
    assert review["authority_boundary"][
        "candidate_H_A_through_H_E_results_authoritative"
    ] is False
    assert review["authority_boundary"]["canonical_semantics_selection_authorized"] is False
