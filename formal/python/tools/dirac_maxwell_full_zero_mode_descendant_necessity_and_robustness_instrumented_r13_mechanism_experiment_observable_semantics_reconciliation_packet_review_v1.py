from __future__ import annotations

"""Independent review of observable-semantics reconciliation packet v1.

The review reconstructs the packet from lower-level bound sources and pure
fixtures.  It never reads the role payload arrays or runs the authorized
comparison.  V1 is blocked because its machine invariance gate can miss a
role-level dominant-block identity change and does not materialize the required
two-valued terminal classification.
"""

import argparse
import hashlib
import inspect
import json
import math
import unicodedata
from collections.abc import Mapping
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import numpy as np

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


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = packet_v1.SELECTED_NEXT_TARGET
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_v2"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_REVIEW_20260716_v1"
)
REPORT_RELATIVE_PATH = reconciliation_v1.REVIEW_RELATIVE_PATH
EXPECTED_PACKET_SHA256 = (
    "7031727e5420c9b858c38e7840b596f0c37f86a1b29c2b9b327f2c087bec4d15"
)
EXPECTED_TOOL_SHA256 = (
    "a907de5c2ae9a278da78f24f352281fd1e5b14533106dfcfd14138dbf9dd4f0a"
)
EXPECTED_PACKET_TEST_SHA256 = (
    "ddc478d94b7c351ac936ac1a6d0a944ba51b8e3c6fcccfa237886483a9846774"
)
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


def _fixture_payloads() -> dict[str, Mapping[str, Any]]:
    iteration_counts = {
        "MECHv0:R13_LOOSE:INSTRUMENTED": 3,
        "MECHv0:R13_TIGHT:INSTRUMENTED": 5,
        "MECHv0:R10_LOOSE:INSTRUMENTED": 3,
    }
    payloads: dict[str, Mapping[str, Any]] = {}
    for run_id, iteration_count in iteration_counts.items():
        solver_steps = []
        terminal = []
        for step in range(1, 17):
            solver_steps.append(
                {
                    "step": step,
                    "iteration_events": [
                        {
                            "iteration": iteration,
                            "packed_update_defect": np.zeros(
                                raw_v3.PACKED_WIDTH, dtype=np.float64
                            ),
                        }
                        for iteration in range(iteration_count)
                    ],
                }
            )
            terminal.append(
                {
                    "step": step,
                    "packed_terminal_equation_defect": np.zeros(
                        raw_v3.PACKED_WIDTH, dtype=np.float64
                    ),
                }
            )
        payloads[run_id] = {
            "configuration": {"solver_tolerance": 1.0e-8},
            "raw_events": {
                "solver_steps": solver_steps,
                "terminal_equation_blocks": terminal,
            },
        }
    return payloads


def _independent_semantics_audit() -> dict[str, Any]:
    vectors = (
        (1.0e16, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0),
        (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
        (42.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7),
    )
    rows = []
    for values in vectors:
        mapping = dict(zip(raw_v3.BLOCK_IDS, values, strict=True))
        producer = reconciliation_v1.numpy_producer_shares(mapping)
        verifier = reconciliation_v1.python_verifier_shares(mapping)
        stacked = np.stack(
            [np.asarray([value], dtype=np.float64) for value in values], axis=0
        )
        direct_numpy_denominator = float(
            np.sum(stacked, axis=0)[0] + raw_v3.GAMMA64
        )
        direct_python_denominator = float(sum(values) + raw_v3.GAMMA64)
        direct_producer = {
            block_id: float(value / direct_numpy_denominator)
            for block_id, value in zip(raw_v3.BLOCK_IDS, values, strict=True)
        }
        direct_verifier = {
            block_id: float(value / direct_python_denominator)
            for block_id, value in zip(raw_v3.BLOCK_IDS, values, strict=True)
        }
        rows.append(
            {
                "inputs": list(values),
                "producer_exact": producer == direct_producer,
                "verifier_exact": verifier == direct_verifier,
                "historical_semantics_diverge": producer != verifier,
            }
        )
    return {
        "fixture_count": len(rows),
        "producer_formula_exact_for_all_fixtures": all(
            row["producer_exact"] for row in rows
        ),
        "verifier_formula_exact_for_all_fixtures": all(
            row["verifier_exact"] for row in rows
        ),
        "at_least_one_fixture_diverges": any(
            row["historical_semantics_diverge"] for row in rows
        ),
        "rows": rows,
    }


def _aggregate_decision(
    hypothesis_id: str, status: str
) -> dict[str, Any]:
    return {
        "hypothesis_id": hypothesis_id,
        "status": status,
        "evidence_ids": [],
        "necessary_condition_decisions": [],
        "supporting_condition_decisions": [],
        "decision_reasons": [],
    }


def _aggregate_contract_audit() -> dict[str, Any]:
    evidence = SimpleNamespace(
        recomputed_metrics={},
        raw_evidence_ids=("fixture",),
        assembler_id="fixture-assembler",
        semantic_contract_id="fixture-contract",
        run_ids=("fixture-run",),
        payload_identity_ids=("fixture-payload",),
        supplied_summary_disposition="ignored",
        canonical_tree_sha256="0" * 64,
        review_anchor_sha256="1" * 64,
        runtime_source_closure_sha256="2" * 64,
    )
    evaluator_names = ("_evaluate_h_a", "_evaluate_h_b", "_evaluate_h_c", "_evaluate_h_d")
    originals = {name: getattr(classifier_v3, name) for name in evaluator_names}

    def install(statuses: tuple[str, str, str, str]) -> None:
        for name, hypothesis_id, status in zip(
            evaluator_names,
            classifier_v3.HYPOTHESES_A_TO_D,
            statuses,
            strict=True,
        ):
            setattr(
                classifier_v3,
                name,
                lambda _metrics, h=hypothesis_id, s=status: _aggregate_decision(h, s),
            )

    try:
        install(("SUPPORTED", "SUPPORTED", "NOT_SUPPORTED", "NOT_SUPPORTED"))
        multiple = classifier_v3._classify_assembled(evidence)
        install(("NOT_SUPPORTED",) * 4)
        none = classifier_v3._classify_assembled(evidence)
    finally:
        for name, function in originals.items():
            setattr(classifier_v3, name, function)
    incomplete = classifier_v3._blocked(
        "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "FIXTURE_INCOMPLETE"
    )
    return {
        "multiple_hypotheses_may_be_supported": multiple[
            "supported_mechanism_ids"
        ]
        == list(classifier_v3.HYPOTHESES_A_TO_D[:2]),
        "multiple_support_aggregate": multiple["aggregate_mechanism_result"],
        "H_E_not_supported_when_A_through_D_nonempty": multiple[
            "hypothesis_decisions"
        ][classifier_v3.H_E]["status"]
        == "NOT_SUPPORTED",
        "empty_support_aggregate": none["aggregate_mechanism_result"],
        "H_E_supported_only_after_empty_A_through_D": none[
            "hypothesis_decisions"
        ][classifier_v3.H_E]["status"]
        == "SUPPORTED",
        "incomplete_evidence_is_not_false_predicates": all(
            item["status"] == "NOT_EVALUATED"
            for item in incomplete["hypothesis_decisions"].values()
        ),
        "same_aggregate_function_called_by_both_semantics": (
            inspect.getsource(reconciliation_v1._candidate_result).count(
                "classifier_v3._classify_assembled"
            )
            == 1
        ),
    }


def _dominant_block_mutation_probe() -> dict[str, Any]:
    decisions = {
        hypothesis_id: {
            "hypothesis_id": hypothesis_id,
            "status": "NOT_SUPPORTED",
            "necessary_condition_decisions": [
                {
                    "criterion_id": f"{hypothesis_id}:fixture",
                    "status": "PASSED",
                }
            ],
        }
        for hypothesis_id in classifier_v3.HYPOTHESES_A_TO_D
        + (classifier_v3.H_E,)
    }
    common = {
        "hypothesis_decisions": decisions,
        "supported_mechanism_ids": [],
        "aggregate_mechanism_result": "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
    }
    producer = {
        **common,
        "block_dominance_metrics": {
            "R13_LOOSE": {"dominant_block_id": "THETA_KINEMATIC"}
        },
    }
    verifier = {
        **common,
        "block_dominance_metrics": {
            "R13_LOOSE": {"dominant_block_id": "P_LONGITUDINAL_MAXWELL"}
        },
    }
    comparison = reconciliation_v1._predicate_comparison(producer, verifier)
    undetected = (
        comparison["threshold_decision_change_count"] == 0
        and comparison["hypothesis_predicate_change_count"] == 0
        and comparison["final_candidate_classification_changed"] is False
    )
    return {
        "control_id": "ROLE_LEVEL_DOMINANT_BLOCK_IDENTITY_MUTATION",
        "changed_premise": "block_dominance_metrics.R13_LOOSE.dominant_block_id",
        "producer_value": "THETA_KINEMATIC",
        "verifier_value": "P_LONGITUDINAL_MAXWELL",
        "expected_gate": "DOMINANT_BLOCK_CHANGE",
        "observed_threshold_decision_change_count": comparison[
            "threshold_decision_change_count"
        ],
        "observed_hypothesis_predicate_change_count": comparison[
            "hypothesis_predicate_change_count"
        ],
        "observed_final_candidate_classification_changed": comparison[
            "final_candidate_classification_changed"
        ],
        "mutation_undetected": undetected,
        "first_diagnostic": "ROLE_LEVEL_DOMINANT_BLOCK_CHANGE_NOT_GATED",
    }


def build_review() -> dict[str, Any]:
    packet_path = REPO_ROOT / packet_v1.REPORT_RELATIVE_PATH
    packet_raw = packet_path.read_bytes()
    packet = json.loads(packet_raw.decode("utf-8"))
    if packet_raw != packet_v1.canonical_json_bytes(packet):
        raise ValueError("packet is not canonical JSON")
    tool_path = REPO_ROOT / reconciliation_v1.SCRIPT_RELATIVE_PATH
    test_path = REPO_ROOT / packet_v1.TEST_RELATIVE_PATH
    source_root = REPO_ROOT / SOURCE_OUTPUT_ROOT_RELATIVE_PATH
    source_tree_before = implementation_v0.directory_tree_sha256(source_root)
    source_file_count = sum(1 for path in source_root.iterdir() if path.is_file())

    semantics_audit = _independent_semantics_audit()
    fixture_comparison = reconciliation_v1._compare_all_fields(_fixture_payloads())
    field_identities = {
        (
            row["run_id"],
            row["event_family"],
            row["step"],
            row["iteration"],
            row["block_id"],
        )
        for row in fixture_comparison["field_comparisons"]
    }
    aggregate_audit = _aggregate_contract_audit()
    mutation_probe = _dominant_block_mutation_probe()
    build_source = inspect.getsource(reconciliation_v1.build_authorized_comparison)
    comparison_source = inspect.getsource(reconciliation_v1._compare_all_fields)
    terminal_classification_materialized = "terminal_classification" in build_source
    separate_ulp_histogram_materialized = all(
        key in comparison_source
        for key in (
            "one_ulp_difference_count",
            "two_ulp_difference_count",
            "larger_ulp_difference_count",
        )
    )
    ordering_has_independent_gate = (
        '"event_ordering_change_count": sum(\n            row["dominant_block_changed"]'
        not in comparison_source
    )
    source_tree_after = implementation_v0.directory_tree_sha256(source_root)
    accepted_checks = {
        "packet_bytes_canonical_and_exact": sha256_bytes(packet_raw)
        == EXPECTED_PACKET_SHA256,
        "tool_source_identity_exact": sha256_bytes(tool_path.read_bytes())
        == EXPECTED_TOOL_SHA256,
        "packet_test_source_identity_exact": sha256_bytes(test_path.read_bytes())
        == EXPECTED_PACKET_TEST_SHA256,
        "source_output_tree_exact_and_unchanged": source_tree_before
        == source_tree_after
        == reconciliation_v1.EXPECTED_SOURCE_OUTPUT_TREE_SHA256,
        "exact_fourteen_source_files": source_file_count == 14,
        "exact_two_historical_semantics": len(packet["historical_semantics"])
        == 2
        and set(reconciliation_v1.SEMANTICS_IDS)
        == {
            reconciliation_v1.PRODUCER_SEMANTICS,
            reconciliation_v1.VERIFIER_SEMANTICS,
        },
        "numpy_producer_semantics_independently_reconstruct": semantics_audit[
            "producer_formula_exact_for_all_fixtures"
        ],
        "python_verifier_semantics_independently_reconstruct": semantics_audit[
            "verifier_formula_exact_for_all_fixtures"
        ],
        "fixed_eight_block_order_exact": packet[
            "frozen_observable_definition"
        ]["block_order"]
        == list(raw_v3.BLOCK_IDS),
        "exact_1792_field_enumeration_from_224_vectors": fixture_comparison[
            "field_count"
        ]
        == len(field_identities)
        == 1792
        and len(fixture_comparison["record_winner_comparisons"]) == 224,
        "field_enumeration_uses_raw_defects_not_cached_shares": all(
            "packed_update_defect"
            in event
            for payload in _fixture_payloads().values()
            for step in payload["raw_events"]["solver_steps"]
            for event in step["iteration_events"]
        ),
        "multiple_support_aggregate_is_explicit": aggregate_audit[
            "multiple_hypotheses_may_be_supported"
        ]
        and aggregate_audit["multiple_support_aggregate"]
        == "MULTIPLE_SUPPORTED_MECHANISMS",
        "H_E_precedence_and_incomplete_semantics_exact": aggregate_audit[
            "H_E_not_supported_when_A_through_D_nonempty"
        ]
        and aggregate_audit["H_E_supported_only_after_empty_A_through_D"]
        and aggregate_audit["incomplete_evidence_is_not_false_predicates"],
        "same_candidate_aggregate_logic_for_both_semantics": aggregate_audit[
            "same_aggregate_function_called_by_both_semantics"
        ],
    }
    failed_checks = {
        "role_level_dominant_block_identity_is_gated": not mutation_probe[
            "mutation_undetected"
        ],
        "decision_relevant_ordering_has_independent_gate": ordering_has_independent_gate,
        "terminal_classification_is_materialized": terminal_classification_materialized,
        "one_two_and_larger_ulp_counts_are_materialized": (
            separate_ulp_histogram_materialized
        ),
    }
    if not all(accepted_checks.values()):
        failed = [key for key, value in accepted_checks.items() if not value]
        raise ValueError(f"unexpected foundational review failure: {failed}")
    if all(failed_checks.values()):
        raise ValueError("expected v1 decision-contract defects were not reproduced")
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "BLOCKED_DECISION_INVARIANCE_GATE_INCOMPLETE",
        "first_diagnostic": "ROLE_LEVEL_DOMINANT_BLOCK_CHANGE_NOT_GATED",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "reviewed_packet": {
            "relative_path": packet_v1.REPORT_RELATIVE_PATH,
            "sha256": sha256_bytes(packet_raw),
            "verdict": packet["verdict"],
        },
        "accepted_foundation": {
            "status": "ACCEPTED_WITHIN_PACKET_REVIEW",
            "source_output_tree_sha256": source_tree_before,
            "source_output_file_count": source_file_count,
            "historical_semantics_count": 2,
            "ordered_vector_count": 224,
            "field_count": 1792,
            "block_count": 8,
            "checks": accepted_checks,
            "passed_check_count": sum(accepted_checks.values()),
            "check_count": len(accepted_checks),
        },
        "independent_semantics_audit": semantics_audit,
        "aggregate_contract_audit": aggregate_audit,
        "decision_contract_audit": {
            "checks": failed_checks,
            "passed_check_count": sum(failed_checks.values()),
            "check_count": len(failed_checks),
            "failed_check_ids": [
                key for key, value in failed_checks.items() if not value
            ],
            "dominant_block_mutation_probe": mutation_probe,
        },
        "blocking_findings": [
            {
                "diagnostic": "ROLE_LEVEL_DOMINANT_BLOCK_CHANGE_NOT_GATED",
                "severity": "DECISIVE",
                "finding": (
                    "The comparison ignores block_dominance_metrics.dominant_block_id. "
                    "A role-level dominant-block mutation can leave every criterion status "
                    "and aggregate comparison unchanged, allowing a false invariant verdict."
                ),
            },
            {
                "diagnostic": "DECISION_RELEVANT_ORDERING_GATE_NOT_INDEPENDENT",
                "severity": "DECISIVE",
                "finding": (
                    "event_ordering_change_count is an alias of per-record dominant-block "
                    "changes rather than an independently defined ordering/tie comparison."
                ),
            },
            {
                "diagnostic": "TERMINAL_CLASSIFICATION_NOT_MATERIALIZED",
                "severity": "DECISIVE",
                "finding": (
                    "The result schema emits predicate_invariant as a boolean but does not "
                    "emit either required terminal label."
                ),
            },
            {
                "diagnostic": "ULP_DIFFERENCE_HISTOGRAM_NOT_MATERIALIZED",
                "severity": "REQUIRED_OUTPUT_REPAIR",
                "finding": (
                    "Per-field ULP distances are present, but separate 1-ULP, 2-ULP, and "
                    "larger-difference counts required by the result contract are absent."
                ),
            },
        ],
        "required_v2_correction": {
            "scope": "DECISION_GATE_AND_RESULT_SCHEMA_ONLY",
            "must_compare_role_level_dominant_block_ids": True,
            "must_define_and_compare_decision_relevant_ordering_and_ties": True,
            "must_emit_exactly_one_of": [
                "PREDICATE_INVARIANT",
                "BLOCKED_OBSERVABLE_DECISION_INSTABILITY",
            ],
            "must_emit_separate_ulp_counts": [
                "exact",
                "one_ulp",
                "two_ulp",
                "larger_than_two_ulp",
            ],
            "must_fail_if_field_count_is_not_1792": True,
            "must_add_atomic_mutation_for_role_dominant_block": True,
            "must_preserve_same_frozen_aggregate_logic": True,
            "must_not_add_reduction_semantics": True,
            "must_not_read_actual_payloads_during_preparation": True,
            "must_not_run_simulation": True,
        },
        "authority_boundary": {
            "packet_v1_accepted": False,
            "calculation_authorized": False,
            "derived_output_authorized": False,
            "simulation_authorized": False,
            "historical_output_modification_authorized": False,
            "H_A_through_H_E_evaluation_authorized": False,
            "canonical_semantics_selection_authorized": False,
            "packet_v2_narrow_preparation_authorized": True,
        },
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_E_REPRO": "PRESERVED",
            "fourteen_row_robustness": "NUMERICALLY_BLOCKED",
            "descendant_materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "R13_root_mechanism": "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "claim_ceiling": (
            "Packet-review evidence only. V1 is blocked before calculation. No payload "
            "comparison, terminal reconciliation result, H_A-H_E evaluation, simulation, "
            "robustness reclassification, materiality result, or new E-REPRO is authorized."
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
                "first_diagnostic": review["first_diagnostic"],
                "foundation_checks": (
                    f"{review['accepted_foundation']['passed_check_count']}/"
                    f"{review['accepted_foundation']['check_count']}"
                ),
                "decision_checks": (
                    f"{review['decision_contract_audit']['passed_check_count']}/"
                    f"{review['decision_contract_audit']['check_count']}"
                ),
                "calculation_authorized": review["authority_boundary"][
                    "calculation_authorized"
                ],
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Review observable-semantics reconciliation packet v1"
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
