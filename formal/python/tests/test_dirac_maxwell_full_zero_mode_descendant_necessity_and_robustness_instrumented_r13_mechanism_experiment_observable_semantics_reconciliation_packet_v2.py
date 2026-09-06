from __future__ import annotations

import copy
import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v3
    as classifier_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_v2
    as packet_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v1
    as reconciliation_v1,
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
SOURCE_OUTPUT_ROOT = (
    ROOT / "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)


def _base_shares() -> dict[str, float]:
    return {
        block_id: float(len(raw_v3.BLOCK_IDS) - index) / 36.0
        for index, block_id in enumerate(raw_v3.BLOCK_IDS)
    }


def _base_candidate() -> dict[str, Any]:
    shares = _base_shares()
    hypothesis_ids = classifier_v3.HYPOTHESES_A_TO_D + (classifier_v3.H_E,)
    return {
        "supported_mechanism_ids": [],
        "aggregate_mechanism_result": "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
        "hypothesis_decisions": {
            hypothesis_id: {
                "hypothesis_id": hypothesis_id,
                "status": (
                    "SUPPORTED" if hypothesis_id == classifier_v3.H_E else "NOT_SUPPORTED"
                ),
                "necessary_condition_decisions": [
                    {
                        "criterion_id": f"{hypothesis_id}_SYNTHETIC_CRITERION",
                        "status": "PASS",
                    }
                ],
            }
            for hypothesis_id in hypothesis_ids
        },
        "block_dominance_metrics": {
            role_id: {
                "dominant_block_id": raw_v3.BLOCK_IDS[0],
                "median_share_by_block": dict(shares),
            }
            for role_id in classifier_v3.ROLE_KEYS
        },
    }


def _unchanged_record_comparison() -> dict[str, int]:
    return {
        "per_record_winner_change_count": 0,
        "per_record_ordering_change_count": 0,
    }


def _decision(
    producer: dict[str, Any],
    verifier: dict[str, Any],
    *,
    record: dict[str, int] | None = None,
) -> dict[str, Any]:
    return reconciliation_v2.compare_decision_contract(
        producer,
        verifier,
        record or _unchanged_record_comparison(),
    )


@lru_cache(maxsize=1)
def _raw_packet() -> bytes:
    return packet_v2.artifact_bytes()


@lru_cache(maxsize=1)
def _packet() -> dict[str, Any]:
    value = json.loads(_raw_packet().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    raw = _raw_packet()
    assert (ROOT / packet_v2.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert packet_v2.artifact_bytes() == raw


def test_packet_preparation_does_not_call_actual_payload_loader(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden_loader(*_args: Any, **_kwargs: Any) -> None:
        raise AssertionError("actual payload loader was called during preparation")

    monkeypatch.setattr(reconciliation_v1, "_load_payloads", forbidden_loader)
    packet = packet_v2.build_packet()
    assert packet["preparation_status"]["actual_payload_arrays_read"] is False
    assert packet["preparation_status"]["actual_field_comparison_performed"] is False


def test_pure_v2_self_validation_passes_six_of_six() -> None:
    validation = reconciliation_v2.self_validate()
    assert len(validation) == 6
    assert all(validation.values())


def test_ranking_groups_exact_ties_and_signed_zero_without_breaking_them() -> None:
    shares = _base_shares()
    shares[raw_v3.BLOCK_IDS[0]] = shares[raw_v3.BLOCK_IDS[1]]
    shares[raw_v3.BLOCK_IDS[-2]] = 0.0
    shares[raw_v3.BLOCK_IDS[-1]] = -0.0
    ranking = reconciliation_v2.ordered_ranking(shares)
    assert ranking[0] == list(raw_v3.BLOCK_IDS[:2])
    assert ranking[-1] == list(raw_v3.BLOCK_IDS[-2:])


def test_lower_rank_swap_is_an_ordering_change_but_not_a_winner_change() -> None:
    producer = _base_candidate()
    verifier = copy.deepcopy(producer)
    role = classifier_v3.ROLE_KEYS[0]
    left = raw_v3.BLOCK_IDS[5]
    right = raw_v3.BLOCK_IDS[6]
    shares = verifier["block_dominance_metrics"][role]["median_share_by_block"]
    shares[left], shares[right] = shares[right], shares[left]
    decision = _decision(producer, verifier)
    assert decision["role_level_dominant_block_change_count"] == 0
    assert decision["role_ordering_change_count"] == 1
    assert decision["ordering_change_count"] == 1
    assert decision["terminal_classification"] == (
        reconciliation_v2.TERMINAL_DECISION_INSTABILITY
    )


def test_atomic_role_winner_change_is_explicitly_gated_even_with_tied_ranking() -> None:
    producer = _base_candidate()
    role = classifier_v3.ROLE_KEYS[0]
    shares = producer["block_dominance_metrics"][role]["median_share_by_block"]
    shares[raw_v3.BLOCK_IDS[1]] = shares[raw_v3.BLOCK_IDS[0]]
    verifier = copy.deepcopy(producer)
    verifier["block_dominance_metrics"][role]["dominant_block_id"] = (
        raw_v3.BLOCK_IDS[1]
    )
    decision = _decision(producer, verifier)
    role_row = next(
        row
        for row in decision["role_comparison"]["roles"]
        if row["role_id"] == role
    )
    assert role_row["numpy_role_dominant_block"] == raw_v3.BLOCK_IDS[0]
    assert role_row["python_role_dominant_block"] == raw_v3.BLOCK_IDS[1]
    assert role_row["role_dominant_block_changed"] is True
    assert decision["role_level_dominant_block_change_count"] == 1
    assert decision["role_ordering_change_count"] == 0
    assert decision["gates"]["role_winners_identical"] is False
    assert decision["terminal_classification"] == (
        reconciliation_v2.TERMINAL_DECISION_INSTABILITY
    )


def test_per_record_winner_change_forces_instability() -> None:
    producer = _base_candidate()
    decision = _decision(
        producer,
        copy.deepcopy(producer),
        record={
            "per_record_winner_change_count": 1,
            "per_record_ordering_change_count": 1,
        },
    )
    assert decision["gates"]["per_record_winners_identical"] is False
    assert decision["terminal_classification"] == (
        reconciliation_v2.TERMINAL_DECISION_INSTABILITY
    )


def test_threshold_status_change_forces_instability() -> None:
    producer = _base_candidate()
    verifier = copy.deepcopy(producer)
    verifier["hypothesis_decisions"][classifier_v3.HYPOTHESES_A_TO_D[0]][
        "necessary_condition_decisions"
    ][0]["status"] = "FAIL"
    decision = _decision(producer, verifier)
    assert decision["threshold_decision_change_count"] == 1
    assert decision["hypothesis_predicate_change_count"] == 0
    assert decision["terminal_classification"] == (
        reconciliation_v2.TERMINAL_DECISION_INSTABILITY
    )


def test_hypothesis_status_change_forces_instability() -> None:
    producer = _base_candidate()
    verifier = copy.deepcopy(producer)
    verifier["hypothesis_decisions"][classifier_v3.HYPOTHESES_A_TO_D[0]][
        "status"
    ] = "SUPPORTED"
    decision = _decision(producer, verifier)
    assert decision["threshold_decision_change_count"] == 0
    assert decision["hypothesis_predicate_change_count"] == 1
    assert decision["terminal_classification"] == (
        reconciliation_v2.TERMINAL_DECISION_INSTABILITY
    )


def test_supported_set_and_aggregate_result_are_independent_gates() -> None:
    producer = _base_candidate()
    supported_mutation = copy.deepcopy(producer)
    supported_mutation["supported_mechanism_ids"] = [
        classifier_v3.HYPOTHESES_A_TO_D[0]
    ]
    supported = _decision(producer, supported_mutation)
    assert supported["supported_mechanism_set_changed"] is True
    assert supported["candidate_aggregate_result_changed"] is False
    assert supported["terminal_classification"] == (
        reconciliation_v2.TERMINAL_DECISION_INSTABILITY
    )

    aggregate_mutation = copy.deepcopy(producer)
    aggregate_mutation["aggregate_mechanism_result"] = "SINGLE_SUPPORTED_MECHANISM"
    aggregate = _decision(producer, aggregate_mutation)
    assert aggregate["supported_mechanism_set_changed"] is False
    assert aggregate["candidate_aggregate_result_changed"] is True
    assert aggregate["terminal_classification"] == (
        reconciliation_v2.TERMINAL_DECISION_INSTABILITY
    )


def test_ulp_bins_are_separate_exhaustive_and_not_an_invariance_gate() -> None:
    histogram = reconciliation_v2.ulp_histogram(
        [
            {"ulp_distance": 0},
            {"ulp_distance": 1},
            {"ulp_distance": 1},
            {"ulp_distance": 2},
            {"ulp_distance": 3},
            {"ulp_distance": 99},
        ]
    )
    assert histogram == {
        "exact_matches": 1,
        "one_ulp_differences": 2,
        "two_ulp_differences": 1,
        "greater_than_two_ulp_differences": 2,
    }
    candidate = _base_candidate()
    decision = _decision(candidate, copy.deepcopy(candidate))
    assert decision["terminal_classification"] == (
        reconciliation_v2.TERMINAL_PREDICATE_INVARIANT
    )
    assert not set(histogram).intersection(reconciliation_v2.INVARIANCE_GATE_IDS)


def test_terminal_enum_is_closed_boolean_and_mutually_exclusive() -> None:
    all_true = {gate_id: True for gate_id in reconciliation_v2.INVARIANCE_GATE_IDS}
    assert reconciliation_v2.terminal_classification(all_true) == (
        reconciliation_v2.TERMINAL_PREDICATE_INVARIANT
    )
    for gate_id in reconciliation_v2.INVARIANCE_GATE_IDS:
        one_false = dict(all_true)
        one_false[gate_id] = False
        assert reconciliation_v2.terminal_classification(one_false) == (
            reconciliation_v2.TERMINAL_DECISION_INSTABILITY
        )
    with pytest.raises(ValueError, match="INVARIANCE_GATE_CLOSURE_MISMATCH"):
        reconciliation_v2.terminal_classification({})
    invalid = dict(all_true)
    invalid[next(iter(invalid))] = 1
    with pytest.raises(ValueError, match="INVARIANCE_GATE_NOT_BOOLEAN"):
        reconciliation_v2.terminal_classification(invalid)


def test_wrong_field_inventory_is_rejected_before_ranking() -> None:
    with pytest.raises(ValueError, match="FIELD_COUNT_NOT_1792"):
        reconciliation_v2.augment_field_comparison({"field_comparisons": []})


def test_v2_preflight_fails_closed_at_missing_independent_review_anchor() -> None:
    before = implementation_v0.directory_tree_sha256(SOURCE_OUTPUT_ROOT)
    with pytest.raises(
        reconciliation_v2.ReconciliationV2Error,
        match="RECONCILIATION_V2_REVIEW_ANCHOR_MISSING",
    ) as captured:
        reconciliation_v2.preflight_authorized_calculation(ROOT)
    assert captured.value.diagnostic == "RECONCILIATION_V2_REVIEW_ANCHOR_MISSING"
    assert implementation_v0.directory_tree_sha256(SOURCE_OUTPUT_ROOT) == before
    assert not (ROOT / reconciliation_v2.RESULT_OUTPUT_ROOT_RELATIVE_PATH).exists()


def test_packet_stops_at_preparation_and_preserves_scientific_boundary() -> None:
    packet = _packet()
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["preserved_foundation"]["v1_foundation_check_count"] == 14
    assert packet["preserved_foundation"][
        "v1_passed_foundation_check_count"
    ] == 14
    assert packet["preserved_foundation"]["historical_reduction_count"] == 2
    assert packet["preserved_foundation"]["ordered_vector_count"] == 224
    assert packet["preserved_foundation"]["field_count"] == 1792
    assert packet["decision_invariance_contract"]["gate_count"] == 7
    assert packet["decision_invariance_contract"]["terminal_classifications"] == [
        "PREDICATE_INVARIANT",
        "BLOCKED_OBSERVABLE_DECISION_INSTABILITY",
    ]
    assert len(packet["registered_synthetic_controls"]) == 8
    assert not any(packet["preparation_status"].values())
    assert packet["one_calculation_contract"]["calculation_authorized_now"] is False
    assert packet["hard_stop"]["additional_packet_version_authorized"] is False
    assert packet["preserved_scientific_core"]["fourteen_row_robustness"] == (
        "NUMERICALLY_BLOCKED"
    )
    assert packet["preserved_scientific_core"]["R13_root_mechanism"] == (
        "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK"
    )
    assert packet["preserved_scientific_core"]["new_E_REPRO"] == "NONE"
