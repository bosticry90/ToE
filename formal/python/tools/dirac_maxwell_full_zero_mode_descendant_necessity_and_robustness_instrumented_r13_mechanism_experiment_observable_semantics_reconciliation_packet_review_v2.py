from __future__ import annotations

"""Independent review of the narrow observable-semantics packet v2.

The review reconstructs the accepted v1 foundation with synthetic fixtures,
audits the v2 decision contract through the same production comparison
functions used by the authorized calculation, and never loads the preserved
role payloads.  Acceptance authorizes exactly one read-only comparison and a
subsequent independent result review.
"""

import argparse
import copy
import hashlib
import inspect
import itertools
import json
import math
import unicodedata
from collections.abc import Mapping
from pathlib import Path
from typing import Any, Callable

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
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_review_v1
    as review_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_v2
    as packet_v2,
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


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-17T00:00:00Z"
TARGET = packet_v2.SELECTED_NEXT_TARGET
SELECTED_NEXT_TARGET = reconciliation_v2.EXPECTED_REVIEW_NEXT_TARGET
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_REVIEW_20260716_v2"
)
REPORT_RELATIVE_PATH = reconciliation_v2.REVIEW_RELATIVE_PATH
REVIEW_TEST_RELATIVE_PATH = (
    "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_review_v2.py"
)
EXPECTED_PACKET_SHA256 = (
    "5b820fd21f534c61378d0eff2a486de1714e10385072ad7723465a91fd91c9a4"
)
EXPECTED_TOOL_SHA256 = (
    "ad2fe8febf5b925e42d3bd056f126ffc81ef7fe5f4045127ca6b095802ea8f0b"
)
EXPECTED_PACKET_GENERATOR_SHA256 = (
    "e0c9744ce0a06c0367eb55c4960206d8b9539f287bc9be8889d74a641b8746b2"
)
EXPECTED_PACKET_TEST_SHA256 = (
    "6c85aa25068d45be028e4815f4ed62fe1b3a1e96a9aa2149c65381d9ab4ea083"
)
EXPECTED_V1_REVIEW_SHA256 = reconciliation_v2.EXPECTED_V1_REVIEW_SHA256
SOURCE_OUTPUT_ROOT_RELATIVE_PATH = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if value is None or isinstance(value, (bool, int)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError("canonical JSON forbids nonfinite floats")
        return value
    if isinstance(value, Mapping):
        return {str(key): _normalize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_normalize(item) for item in value]
    raise TypeError(f"unsupported canonical JSON value: {type(value)!r}")


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            _normalize(value),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _source_binding(relative_path: str) -> dict[str, str]:
    path = REPO_ROOT / relative_path
    if not path.is_file():
        raise ValueError(f"missing review source: {relative_path}")
    return {"relative_path": relative_path, "sha256": sha256_bytes(path.read_bytes())}


def _base_shares() -> dict[str, float]:
    return {
        block_id: float(8 - index) / 36.0
        for index, block_id in enumerate(raw_v3.BLOCK_IDS)
    }


def _base_candidate() -> dict[str, Any]:
    shares = _base_shares()
    hypothesis_ids = classifier_v3.HYPOTHESES_A_TO_D + (classifier_v3.H_E,)
    return {
        "semantics_id": "SYNTHETIC_REVIEW_FIXTURE",
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


def _record_counts(winners: int = 0, orderings: int = 0) -> dict[str, int]:
    return {
        "per_record_winner_change_count": winners,
        "per_record_ordering_change_count": orderings,
    }


def _decision(
    producer: Mapping[str, Any],
    verifier: Mapping[str, Any],
    record: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return reconciliation_v2.compare_decision_contract(
        producer, verifier, record or _record_counts()
    )


def _raises_value_error(function: Callable[[], Any]) -> bool:
    try:
        function()
    except ValueError:
        return True
    return False


def _independent_ranking(shares: Mapping[str, Any]) -> list[list[str]]:
    normalized = {
        block_id: 0.0 if float(shares[block_id]) == 0.0 else float(shares[block_id])
        for block_id in raw_v3.BLOCK_IDS
    }
    values = sorted(set(normalized.values()), reverse=True)
    return [
        [block_id for block_id in raw_v3.BLOCK_IDS if normalized[block_id] == value]
        for value in values
    ]


def _terminal_closure_audit() -> dict[str, Any]:
    rows = []
    for values in itertools.product((False, True), repeat=len(reconciliation_v2.INVARIANCE_GATE_IDS)):
        gates = dict(zip(reconciliation_v2.INVARIANCE_GATE_IDS, values, strict=True))
        observed = reconciliation_v2.terminal_classification(gates)
        expected = (
            reconciliation_v2.TERMINAL_PREDICATE_INVARIANT
            if all(values)
            else reconciliation_v2.TERMINAL_DECISION_INSTABILITY
        )
        rows.append(observed == expected)
    invalid = {gate_id: True for gate_id in reconciliation_v2.INVARIANCE_GATE_IDS}
    invalid[reconciliation_v2.INVARIANCE_GATE_IDS[0]] = 1
    return {
        "boolean_assignment_count": len(rows),
        "all_assignments_match_independent_oracle": all(rows),
        "reachable_terminal_labels": sorted(
            {
                reconciliation_v2.terminal_classification(
                    dict(zip(reconciliation_v2.INVARIANCE_GATE_IDS, values, strict=True))
                )
                for values in itertools.product(
                    (False, True), repeat=len(reconciliation_v2.INVARIANCE_GATE_IDS)
                )
            }
        ),
        "incomplete_gate_map_rejected_preterminal": _raises_value_error(
            lambda: reconciliation_v2.terminal_classification({})
        ),
        "nonboolean_gate_rejected_preterminal": _raises_value_error(
            lambda: reconciliation_v2.terminal_classification(invalid)
        ),
    }


def _synthetic_fields(distances: Mapping[int, int]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    shares = _base_shares()
    for record_index in range(reconciliation_v2.EXPECTED_RECORD_COUNT):
        for block_index, block_id in enumerate(raw_v3.BLOCK_IDS):
            row_index = len(rows)
            producer = shares[block_id]
            verifier = producer
            for _ in range(distances.get(row_index, 0)):
                verifier = math.nextafter(verifier, math.inf)
            distance = predecessor_v1.ulp_distance(producer, verifier)
            rows.append(
                {
                    "run_id": "SYNTHETIC_REVIEW_RUN",
                    "event_family": "iteration",
                    "step": record_index,
                    "iteration": 0,
                    "block_id": block_id,
                    "producer_share": producer,
                    "verifier_share": verifier,
                    "ulp_distance": distance,
                }
            )
    return rows


def _ulp_invariance_control(distances: Mapping[int, int]) -> dict[str, Any]:
    augmented = reconciliation_v2.augment_field_comparison(
        {"field_comparisons": _synthetic_fields(distances)}
    )
    candidate = _base_candidate()
    decision = _decision(
        candidate,
        copy.deepcopy(candidate),
        augmented["record_ranking_comparison"],
    )
    return {
        "ulp_histogram": augmented["ulp_histogram"],
        "record_count": augmented["record_ranking_comparison"]["record_count"],
        "per_record_winner_change_count": decision["per_record_winner_change_count"],
        "ordering_change_count": decision["ordering_change_count"],
        "terminal_classification": decision["terminal_classification"],
    }


def _decision_contract_audit() -> dict[str, Any]:
    producer = _base_candidate()
    invariant = _decision(producer, copy.deepcopy(producer))

    role_winner_left = _base_candidate()
    role = classifier_v3.ROLE_KEYS[0]
    tied = role_winner_left["block_dominance_metrics"][role]["median_share_by_block"]
    tied[raw_v3.BLOCK_IDS[1]] = tied[raw_v3.BLOCK_IDS[0]]
    role_winner_right = copy.deepcopy(role_winner_left)
    role_winner_right["block_dominance_metrics"][role]["dominant_block_id"] = (
        raw_v3.BLOCK_IDS[1]
    )
    role_winner = _decision(role_winner_left, role_winner_right)

    lower_order_right = copy.deepcopy(producer)
    shares = lower_order_right["block_dominance_metrics"][role]["median_share_by_block"]
    left_block, right_block = raw_v3.BLOCK_IDS[5:7]
    shares[left_block], shares[right_block] = shares[right_block], shares[left_block]
    lower_role_order = _decision(producer, lower_order_right)

    per_record_winner = _decision(
        producer, copy.deepcopy(producer), _record_counts(winners=1, orderings=1)
    )
    per_record_lower_order = _decision(
        producer, copy.deepcopy(producer), _record_counts(orderings=1)
    )

    threshold_right = copy.deepcopy(producer)
    threshold_right["hypothesis_decisions"][classifier_v3.HYPOTHESES_A_TO_D[0]][
        "necessary_condition_decisions"
    ][0]["status"] = "FAIL"
    threshold = _decision(producer, threshold_right)

    hypothesis_right = copy.deepcopy(producer)
    hypothesis_right["hypothesis_decisions"][classifier_v3.HYPOTHESES_A_TO_D[0]][
        "status"
    ] = "SUPPORTED"
    hypothesis = _decision(producer, hypothesis_right)

    supported_right = copy.deepcopy(producer)
    supported_right["supported_mechanism_ids"] = [classifier_v3.HYPOTHESES_A_TO_D[0]]
    supported = _decision(producer, supported_right)

    aggregate_right = copy.deepcopy(producer)
    aggregate_right["aggregate_mechanism_result"] = "SINGLE_SUPPORTED_MECHANISM"
    aggregate = _decision(producer, aggregate_right)

    one_two_ulp = _ulp_invariance_control({6: 1, 7: 2})
    greater_ulp = _ulp_invariance_control({7: 8})
    terminal = _terminal_closure_audit()

    tie_fixture = _base_shares()
    tie_fixture[raw_v3.BLOCK_IDS[0]] = tie_fixture[raw_v3.BLOCK_IDS[1]]
    tie_fixture[raw_v3.BLOCK_IDS[-2]] = 0.0
    tie_fixture[raw_v3.BLOCK_IDS[-1]] = -0.0
    ranking_matches_oracle = reconciliation_v2.ordered_ranking(
        tie_fixture
    ) == _independent_ranking(tie_fixture)

    controls = {
        "ALL_GATES_TRUE": invariant["terminal_classification"],
        "ROLE_WINNER_MUTATION": role_winner["terminal_classification"],
        "LOWER_RANK_ROLE_ORDERING_SWAP_SAME_WINNER": lower_role_order[
            "terminal_classification"
        ],
        "PER_RECORD_WINNER_MUTATION": per_record_winner["terminal_classification"],
        "LOWER_RANK_PER_RECORD_ORDERING_SWAP_SAME_WINNER": per_record_lower_order[
            "terminal_classification"
        ],
        "THRESHOLD_STATUS_MUTATION": threshold["terminal_classification"],
        "HYPOTHESIS_STATUS_MUTATION": hypothesis["terminal_classification"],
        "SUPPORTED_SET_MUTATION": supported["terminal_classification"],
        "AGGREGATE_RESULT_MUTATION": aggregate["terminal_classification"],
        "PURE_ONE_TWO_ULP_NO_DECISION_CHANGE": one_two_ulp[
            "terminal_classification"
        ],
        "GREATER_THAN_TWO_ULP_NO_DECISION_CHANGE": greater_ulp[
            "terminal_classification"
        ],
    }
    expected = {
        "ALL_GATES_TRUE": reconciliation_v2.TERMINAL_PREDICATE_INVARIANT,
        "ROLE_WINNER_MUTATION": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "LOWER_RANK_ROLE_ORDERING_SWAP_SAME_WINNER": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "PER_RECORD_WINNER_MUTATION": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "LOWER_RANK_PER_RECORD_ORDERING_SWAP_SAME_WINNER": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "THRESHOLD_STATUS_MUTATION": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "HYPOTHESIS_STATUS_MUTATION": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "SUPPORTED_SET_MUTATION": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "AGGREGATE_RESULT_MUTATION": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
        "PURE_ONE_TWO_ULP_NO_DECISION_CHANGE": reconciliation_v2.TERMINAL_PREDICATE_INVARIANT,
        "GREATER_THAN_TWO_ULP_NO_DECISION_CHANGE": reconciliation_v2.TERMINAL_PREDICATE_INVARIANT,
    }
    checks = {
        "role_level_dominant_block_identity_is_gated": (
            role_winner["role_level_dominant_block_change_count"] == 1
        ),
        "role_winner_and_role_ordering_counts_are_independent": (
            role_winner["role_level_dominant_block_change_count"] == 1
            and role_winner["role_ordering_change_count"] == 0
            and lower_role_order["role_level_dominant_block_change_count"] == 0
            and lower_role_order["role_ordering_change_count"] == 1
        ),
        "per_record_winner_and_ordering_counts_are_independently_gated": (
            per_record_winner["per_record_winner_change_count"] == 1
            and per_record_lower_order["per_record_winner_change_count"] == 0
            and per_record_lower_order["per_record_ordering_change_count"] == 1
        ),
        "ranking_and_signed_zero_ties_match_independent_oracle": ranking_matches_oracle,
        "threshold_mutation_is_gated": threshold["threshold_decision_change_count"] == 1,
        "hypothesis_mutation_is_gated": (
            hypothesis["hypothesis_predicate_change_count"] == 1
        ),
        "supported_set_and_aggregate_are_separate_gates": (
            supported["supported_mechanism_set_changed"] is True
            and supported["candidate_aggregate_result_changed"] is False
            and aggregate["supported_mechanism_set_changed"] is False
            and aggregate["candidate_aggregate_result_changed"] is True
        ),
        "all_registered_mutation_outcomes_match": controls == expected,
        "four_ulp_bins_are_disjoint_and_exhaustive": (
            one_two_ulp["ulp_histogram"]
            == {
                "exact_matches": 1790,
                "one_ulp_differences": 1,
                "two_ulp_differences": 1,
                "greater_than_two_ulp_differences": 0,
            }
            and greater_ulp["ulp_histogram"]
            == {
                "exact_matches": 1791,
                "one_ulp_differences": 0,
                "two_ulp_differences": 0,
                "greater_than_two_ulp_differences": 1,
            }
        ),
        "ulp_magnitude_alone_does_not_force_instability": (
            one_two_ulp["terminal_classification"]
            == reconciliation_v2.TERMINAL_PREDICATE_INVARIANT
            and greater_ulp["terminal_classification"]
            == reconciliation_v2.TERMINAL_PREDICATE_INVARIANT
        ),
        "two_terminal_labels_are_reachable_closed_and_exhaustive": (
            terminal["boolean_assignment_count"] == 128
            and terminal["all_assignments_match_independent_oracle"]
            and set(terminal["reachable_terminal_labels"])
            == set(reconciliation_v2.TERMINAL_CLASSIFICATIONS)
            and terminal["incomplete_gate_map_rejected_preterminal"]
            and terminal["nonboolean_gate_rejected_preterminal"]
        ),
        "wrong_field_inventory_is_rejected_preterminal": _raises_value_error(
            lambda: reconciliation_v2.augment_field_comparison(
                {"field_comparisons": []}
            )
        ),
    }
    return {
        "checks": checks,
        "passed_check_count": sum(checks.values()),
        "check_count": len(checks),
        "controls": controls,
        "expected_controls": expected,
        "one_two_ulp_control": one_two_ulp,
        "greater_than_two_ulp_control": greater_ulp,
        "terminal_closure": terminal,
    }


def build_review() -> dict[str, Any]:
    packet_path = REPO_ROOT / packet_v2.REPORT_RELATIVE_PATH
    packet_raw = packet_path.read_bytes()
    packet = json.loads(packet_raw.decode("utf-8"))
    if packet_raw != packet_v2.canonical_json_bytes(packet):
        raise ValueError("packet v2 is not canonical JSON")

    source_root = REPO_ROOT / SOURCE_OUTPUT_ROOT_RELATIVE_PATH
    result_root = REPO_ROOT / reconciliation_v2.RESULT_OUTPUT_ROOT_RELATIVE_PATH
    if result_root.exists():
        raise ValueError("derived reconciliation v2 result root preexists review")
    source_tree_before = implementation_v0.directory_tree_sha256(source_root)
    source_file_count = sum(1 for path in source_root.iterdir() if path.is_file())

    reconstructed_v1 = review_v1.build_review()
    v1_review_path = REPO_ROOT / review_v1.REPORT_RELATIVE_PATH
    v1_review_raw = v1_review_path.read_bytes()
    v1_foundation = reconstructed_v1["accepted_foundation"]
    foundation_checks = dict(v1_foundation["checks"])
    foundation_reconstructed_exactly = (
        canonical_json_bytes(reconstructed_v1) == v1_review_raw
        and sha256_bytes(v1_review_raw) == EXPECTED_V1_REVIEW_SHA256
        and v1_foundation["passed_check_count"] == 14
        and v1_foundation["check_count"] == 14
        and all(foundation_checks.values())
    )

    tool_binding = _source_binding(reconciliation_v2.SCRIPT_RELATIVE_PATH)
    packet_generator_binding = _source_binding(
        Path(packet_v2.__file__).resolve().relative_to(REPO_ROOT).as_posix()
    )
    packet_test_binding = _source_binding(packet_v2.TEST_RELATIVE_PATH)
    review_test_binding = _source_binding(REVIEW_TEST_RELATIVE_PATH)
    decision_audit = _decision_contract_audit()

    build_source = inspect.getsource(reconciliation_v2.build_authorized_comparison)
    packet_source = inspect.getsource(packet_v2.build_packet)
    production_checks = {
        "packet_identity_exact": sha256_bytes(packet_raw) == EXPECTED_PACKET_SHA256,
        "tool_identity_exact": tool_binding["sha256"] == EXPECTED_TOOL_SHA256,
        "packet_generator_identity_exact": (
            packet_generator_binding["sha256"] == EXPECTED_PACKET_GENERATOR_SHA256
        ),
        "packet_test_identity_exact": (
            packet_test_binding["sha256"] == EXPECTED_PACKET_TEST_SHA256
        ),
        "v1_foundation_reconstructed_fourteen_of_fourteen": foundation_reconstructed_exactly,
        "source_tree_exact_and_unchanged": source_tree_before
        == reconciliation_v2.EXPECTED_SOURCE_OUTPUT_TREE_SHA256,
        "exact_fourteen_preserved_source_files": source_file_count == 14,
        "production_uses_shared_field_inventory_and_ranking": (
            "augment_field_comparison(base_fields)" in build_source
            and "compare_record_rankings(fields)" in inspect.getsource(
                reconciliation_v2.augment_field_comparison
            )
        ),
        "production_uses_shared_role_hypothesis_and_terminal_decision": (
            "compare_decision_contract(" in build_source
            and "compare_role_rankings(" in inspect.getsource(
                reconciliation_v2.compare_decision_contract
            )
            and "predecessor_v1._predicate_comparison(" in inspect.getsource(
                reconciliation_v2.compare_decision_contract
            )
            and "terminal_classification(gates)" in inspect.getsource(
                reconciliation_v2.compare_decision_contract
            )
        ),
        "packet_and_calculation_share_self_validation_contract": (
            "reconciliation_v2.self_validate()" in packet_source
            and all(packet["calculation_tool"]["pure_self_validation"].values())
        ),
        "derived_result_root_absent_before_authorization": not result_root.exists(),
        "simulation_path_not_present_in_production_comparison": (
            "execution_v0" not in build_source
            and "executor_v" not in build_source
            and "simulate(" not in build_source
        ),
    }
    source_tree_after = implementation_v0.directory_tree_sha256(source_root)
    production_checks["review_preserves_source_tree_and_creates_no_result"] = (
        source_tree_before == source_tree_after and not result_root.exists()
    )

    all_checks = {
        **production_checks,
        **decision_audit["checks"],
    }
    if not all(all_checks.values()):
        failed = [key for key, value in all_checks.items() if not value]
        raise ValueError(f"v2 independent review failed: {failed}")

    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": reconciliation_v2.EXPECTED_REVIEW_VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "reviewed_packet": {
            "relative_path": packet_v2.REPORT_RELATIVE_PATH,
            "sha256": sha256_bytes(packet_raw),
            "verdict": packet["verdict"],
        },
        "review_sources": {
            "calculation_tool": tool_binding,
            "packet_generator": packet_generator_binding,
            "packet_test": packet_test_binding,
            "review_test": review_test_binding,
        },
        "reconstructed_v1_foundation": {
            "status": "RECONSTRUCTED_EXACTLY",
            "check_count": v1_foundation["check_count"],
            "passed_check_count": v1_foundation["passed_check_count"],
            "checks": foundation_checks,
            "accepted_v1_review_sha256": sha256_bytes(v1_review_raw),
        },
        "decision_contract_audit": decision_audit,
        "production_path_audit": {
            "checks": production_checks,
            "passed_check_count": sum(production_checks.values()),
            "check_count": len(production_checks),
            "source_output_tree_sha256_before": source_tree_before,
            "source_output_tree_sha256_after": source_tree_after,
            "source_output_file_count": source_file_count,
            "actual_payload_arrays_read": False,
            "actual_field_comparison_performed": False,
            "derived_output_created": False,
            "simulation_invoked": False,
        },
        "accepted_calculation_authority": {
            "packet_sha256": sha256_bytes(packet_raw),
            "tool_sha256": tool_binding["sha256"],
            "predecessor_tool_sha256": reconciliation_v2.EXPECTED_PREDECESSOR_TOOL_SHA256,
            "source_output_tree_sha256": source_tree_before,
            "one_read_only_calculation_only": True,
            "simulation_authorized": False,
            "H_A_through_H_E_acceptance_authorized": False,
        },
        "authority_boundary": {
            "packet_v2_accepted": True,
            "calculation_authorized_count": 1,
            "calculation_executed_during_review": False,
            "independent_result_review_required": True,
            "candidate_H_A_through_H_E_results_authoritative": False,
            "canonical_semantics_selection_authorized": False,
            "simulation_authorized": False,
            "historical_output_modification_authorized": False,
            "additional_packet_version_authorized": False,
            "additional_reduction_algorithm_authorized": False,
        },
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_E_REPRO": "PRESERVED",
            "fourteen_row_robustness": "NUMERICALLY_BLOCKED",
            "descendant_materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "R13_root_mechanism": "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "claim_ceiling": (
            "Independent packet-v2 contract acceptance only. This authorizes exactly one "
            "read-only comparison over the preserved fourteen-file tree and one subsequent "
            "result review. It does not assign an authoritative H_A-H_E result, select "
            "canonical semantics, invoke simulation, reclassify robustness, establish "
            "materiality, close a seam, or create new E-REPRO."
        ),
    }


def artifact_bytes() -> bytes:
    return canonical_json_bytes(build_review())


def write_or_check(check: bool) -> None:
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if check:
        if not path.is_file() or path.read_bytes() != raw:
            raise SystemExit(f"artifact mismatch: {REPORT_RELATIVE_PATH}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    review = json.loads(raw.decode("utf-8"))
    print(
        json.dumps(
            {
                "status": "CHECKED" if check else "WROTE",
                "verdict": review["verdict"],
                "foundation_checks": (
                    f"{review['reconstructed_v1_foundation']['passed_check_count']}/"
                    f"{review['reconstructed_v1_foundation']['check_count']}"
                ),
                "decision_checks": (
                    f"{review['decision_contract_audit']['passed_check_count']}/"
                    f"{review['decision_contract_audit']['check_count']}"
                ),
                "calculation_authorized_count": review["authority_boundary"][
                    "calculation_authorized_count"
                ],
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Independently review observable-semantics reconciliation packet v2"
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
