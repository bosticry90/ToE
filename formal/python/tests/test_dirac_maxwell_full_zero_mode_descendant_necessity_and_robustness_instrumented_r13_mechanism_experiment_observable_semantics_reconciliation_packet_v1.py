from __future__ import annotations

import json
import math
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
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_v1
    as packet_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v1
    as reconciliation_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as raw_v3,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _raw() -> bytes:
    return packet_v1.artifact_bytes()


@lru_cache(maxsize=1)
def _packet() -> dict[str, Any]:
    value = json.loads(_raw().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def _vector(values: tuple[float, ...]) -> dict[str, float]:
    return dict(zip(raw_v3.BLOCK_IDS, values, strict=True))


def test_packet_regenerates_exactly_and_deterministically() -> None:
    raw = _raw()
    assert (ROOT / packet_v1.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert packet_v1.artifact_bytes() == raw


def test_only_the_two_historical_reductions_are_registered() -> None:
    packet = _packet()
    semantics = packet["historical_semantics"]
    assert len(semantics) == 2
    assert [item["semantics_id"] for item in semantics] == [
        reconciliation_v1.PRODUCER_SEMANTICS,
        reconciliation_v1.VERIFIER_SEMANTICS,
    ]
    assert packet["frozen_observable_definition"]["block_order"] == list(
        raw_v3.BLOCK_IDS
    )
    assert packet["calculation_tool"]["comparison_semantics_count"] == 2
    assert packet["hard_stop"]["additional_summation_algorithms_authorized"] is False


def test_pure_fixture_reconstructs_a_real_reduction_order_divergence() -> None:
    comparison = reconciliation_v1.compare_normalized_vector(
        _vector((1.0e16, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0))
    )
    assert comparison["producer_denominator"] != comparison["verifier_denominator"]
    assert comparison["mismatch_count"] > 0
    assert comparison["maximum_ulp_distance"] > 0
    assert comparison["dominant_block_changed"] is False
    assert comparison["producer_dominant_block_id"] == raw_v3.BLOCK_IDS[0]
    assert comparison["verifier_dominant_block_id"] == raw_v3.BLOCK_IDS[0]


def test_all_zero_vector_is_explicitly_defined_by_gamma64() -> None:
    comparison = reconciliation_v1.compare_normalized_vector(
        _vector((0.0,) * 8)
    )
    assert comparison["producer_denominator"] == raw_v3.GAMMA64
    assert comparison["verifier_denominator"] == raw_v3.GAMMA64
    assert comparison["exact_match_count"] == 8
    assert comparison["mismatch_count"] == 0
    assert all(item["producer_share"] == 0.0 for item in comparison["fields"])
    assert all(item["verifier_share"] == 0.0 for item in comparison["fields"])


@pytest.mark.parametrize(
    ("replacement", "diagnostic"),
    [
        (math.nan, "NONFINITE_NORMALIZED_VALUE"),
        (math.inf, "NONFINITE_NORMALIZED_VALUE"),
        (-1.0, "NEGATIVE_NORMALIZED_VALUE"),
        (-0.0, "NEGATIVE_ZERO_NORMALIZED_VALUE"),
    ],
)
def test_invalid_float_domains_fail_closed(
    replacement: float, diagnostic: str
) -> None:
    values = [1.0] * 8
    values[3] = replacement
    with pytest.raises(ValueError, match=diagnostic):
        reconciliation_v1.compare_normalized_vector(_vector(tuple(values)))


def test_unknown_or_missing_block_fails_closed() -> None:
    values = _vector((1.0,) * 8)
    values.pop(raw_v3.BLOCK_IDS[-1])
    values["UNKNOWN_NINTH_BLOCK"] = 1.0
    with pytest.raises(ValueError, match="exactly eight frozen blocks"):
        reconciliation_v1.compare_normalized_vector(values)


def test_calculation_preflight_is_blocked_without_independent_review() -> None:
    source_root = (
        ROOT / "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
    )
    before = implementation_v0.directory_tree_sha256(source_root)
    with pytest.raises(
        reconciliation_v1.ReconciliationError,
        match="RECONCILIATION_REVIEW_ANCHOR_MISSING",
    ) as captured:
        reconciliation_v1.preflight_authorized_calculation(ROOT)
    assert captured.value.diagnostic == "RECONCILIATION_REVIEW_ANCHOR_MISSING"
    assert implementation_v0.directory_tree_sha256(source_root) == before
    assert not (ROOT / reconciliation_v1.RESULT_OUTPUT_ROOT_RELATIVE_PATH).exists()


def test_packet_freezes_the_exact_1792_field_question_and_hard_stop() -> None:
    packet = _packet()
    census = packet["dispute_census"]
    assert census == {
        "ordered_normalized_vector_count": 224,
        "block_count": 8,
        "field_count": 1792,
        "exact_match_count": 1222,
        "one_or_two_ulp_mismatch_count": 570,
        "maximum_ulp_distance": 2,
        "raw_maximum_mismatch_count": 0,
        "normalized_value_mismatch_count": 0,
    }
    contract = packet["one_calculation_contract"]
    assert contract["calculation_authorized_now"] is False
    assert contract["authorized_calculation_count_after_acceptance"] == 1
    assert contract["expected_field_count"] == 1792
    assert contract["candidate_classifications_authoritative"] is False
    hard_stop = packet["hard_stop"]
    assert hard_stop["packet_count"] == 1
    assert hard_stop["read_only_calculation_count"] == 1
    assert hard_stop["independent_result_review_count"] == 1
    assert hard_stop["second_reconciliation_loop_authorized"] is False
    assert hard_stop["new_simulation_authorized"] is False


def test_preparation_does_not_read_payload_arrays_or_decide_hypotheses() -> None:
    packet = _packet()
    status = packet["preparation_status"]
    assert status == {
        "source_payload_arrays_read": False,
        "derived_field_comparison_performed": False,
        "classifier_predicates_compared": False,
        "canonical_semantics_selected": False,
        "H_A_through_H_E_evaluated": False,
        "derived_output_created": False,
        "simulation_invoked": False,
    }
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == packet_v1.SELECTED_NEXT_TARGET
    assert not (ROOT / reconciliation_v1.RESULT_OUTPUT_ROOT_RELATIVE_PATH).exists()


def test_predicate_sensitive_route_is_mandatory_block_and_lane_closeout() -> None:
    rule = _packet()["decision_rule_after_calculation"]
    assert "BLOCKED_OBSERVABLE_DECISION_INSTABILITY" in rule[
        "PREDICATE_SENSITIVE"
    ]
    assert "close the R13 mechanism lane" in rule["PREDICATE_SENSITIVE"]
    proposal = _packet()["proposed_canonical_semantics_if_and_only_if_invariant"]
    assert proposal["selected_during_preparation"] is False
    assert proposal["selection_requires_predicate_invariance"] is True
    assert proposal["selection_requires_independent_result_review"] is True

