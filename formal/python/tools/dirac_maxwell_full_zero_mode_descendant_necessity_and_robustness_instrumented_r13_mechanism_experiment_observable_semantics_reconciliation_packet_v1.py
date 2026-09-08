from __future__ import annotations

"""Prepare the bounded observable-semantics reconciliation packet v1.

Preparation binds a read-only tool and exact decision boundary.  It does not
read the role payload arrays, run the comparison, write a derived result, or
evaluate H_A--H_E.
"""

import argparse
import hashlib
import json
import math
import unicodedata
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
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
TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_v1"
)
SELECTED_NEXT_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_v1_result"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_20260716_v1"
)
REPORT_RELATIVE_PATH = reconciliation_v1.PACKET_RELATIVE_PATH
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_v1.py"
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


def _source_binding(relative_path: str) -> dict[str, Any]:
    path = REPO_ROOT / relative_path
    if not path.is_file():
        raise ValueError(f"required packet source missing: {relative_path}")
    return {
        "relative_path": relative_path,
        "sha256": sha256_bytes(path.read_bytes()),
    }


def build_packet() -> dict[str, Any]:
    result_review = json.loads(
        (REPO_ROOT / reconciliation_v1.RESULT_REVIEW_RELATIVE_PATH).read_text(
            encoding="utf-8"
        )
    )
    if (
        result_review.get("verdict") != "BLOCKED_OBSERVABLE_SEMANTICS"
        or result_review.get("selected_next_target") != TARGET
        or sha256_bytes(
            (REPO_ROOT / reconciliation_v1.RESULT_REVIEW_RELATIVE_PATH).read_bytes()
        )
        != reconciliation_v1.EXPECTED_RESULT_REVIEW_SHA256
    ):
        raise ValueError("source result-review authority mismatch")
    source_root = (
        REPO_ROOT
        / "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
    )
    source_tree = implementation_v0.directory_tree_sha256(source_root)
    if source_tree != reconciliation_v1.EXPECTED_SOURCE_OUTPUT_TREE_SHA256:
        raise ValueError("preserved source output tree mismatch")
    if (REPO_ROOT / reconciliation_v1.REVIEW_RELATIVE_PATH).exists():
        raise ValueError("independent packet review must not preexist preparation")
    if (REPO_ROOT / reconciliation_v1.RESULT_OUTPUT_ROOT_RELATIVE_PATH).exists():
        raise ValueError("derived reconciliation output must be absent in preparation")
    self_validation = reconciliation_v1.self_validate()
    if not all(self_validation.values()):
        raise ValueError("pure reconciliation tool self-validation failed")
    tool_binding = _source_binding(reconciliation_v1.SCRIPT_RELATIVE_PATH)
    test_binding = _source_binding(TEST_RELATIVE_PATH)
    arithmetic = result_review["raw_reconstruction_review"][
        "arithmetic_forensics"
    ]
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "source_result_review": {
            "relative_path": reconciliation_v1.RESULT_REVIEW_RELATIVE_PATH,
            "sha256": reconciliation_v1.EXPECTED_RESULT_REVIEW_SHA256,
            "verdict": result_review["verdict"],
            "first_diagnostic": result_review["first_diagnostic"],
        },
        "preserved_evidence_identity": {
            "source_output_root": (
                "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
            ),
            "source_output_tree_sha256": source_tree,
            "source_output_file_count": 14,
            "source_outputs_mutable": False,
            "simulation_required": False,
        },
        "dispute_census": {
            "ordered_normalized_vector_count": arithmetic[
                "summary_record_count"
            ],
            "block_count": arithmetic["block_count"],
            "field_count": arithmetic["scalar_field_count_per_mapping"],
            "exact_match_count": (
                arithmetic["scalar_field_count_per_mapping"]
                - arithmetic[
                    "stored_share_vs_frozen_python_sum_verifier_mismatch_count"
                ]
            ),
            "one_or_two_ulp_mismatch_count": arithmetic[
                "stored_share_vs_frozen_python_sum_verifier_mismatch_count"
            ],
            "maximum_ulp_distance": arithmetic[
                "maximum_python_sum_mismatch_ulp_distance"
            ],
            "raw_maximum_mismatch_count": arithmetic[
                "stored_raw_maximum_mismatch_count"
            ],
            "normalized_value_mismatch_count": arithmetic[
                "stored_normalized_mismatch_count"
            ],
        },
        "frozen_observable_definition": {
            "block_order": list(raw_v3.BLOCK_IDS),
            "input_type": "ordered IEEE-754 binary64 normalized magnitudes",
            "input_derivation": (
                "max(abs(packed defect block)) / max(role tolerance, gamma64)"
            ),
            "gamma64_decimal": raw_v3.GAMMA64,
            "gamma64_hex": float(raw_v3.GAMMA64).hex(),
            "share_formula": "share_i = normalized_i / (reduction(normalized) + gamma64)",
            "finite_domain": "all eight inputs finite and nonnegative",
            "signed_zero_rule": (
                "negative zero is rejected; raw absolute-max derivation supplies positive zero"
            ),
            "zero_denominator_rule": (
                "gamma64 makes the all-zero denominator strictly positive"
            ),
            "nan_or_infinity_rule": "reject before reduction",
            "serialization_rule": (
                "canonical UTF-8 JSON, sorted keys, shortest round-trip finite decimal"
            ),
            "exact_comparison_rule": "binary64 bit identity plus recorded ULP distance",
            "tie_rule": (
                "numpy argmax; first maximum in the frozen block order wins"
            ),
        },
        "historical_semantics": [
            {
                "route_id": "A_PRODUCER_EXACT",
                "semantics_id": reconciliation_v1.PRODUCER_SEMANTICS,
                "reduction": (
                    "np.sum(np.stack(float64 scalar arrays in frozen block order), axis=0)[0]"
                ),
                "accumulation_type": "NumPy float64 reduction",
                "historical_status": "used to create cached payload shares",
            },
            {
                "route_id": "B_VERIFIER_EXACT",
                "semantics_id": reconciliation_v1.VERIFIER_SEMANTICS,
                "reduction": (
                    "Python built-in sum over eight float values in frozen block order"
                ),
                "accumulation_type": "left-to-right scalar binary64 additions",
                "historical_status": "used by frozen v3 raw-evidence verifier",
            },
        ],
        "reconciliation_routes": {
            "A_PRODUCER_EXACT": (
                "candidate only; exactly reproduces historical cached shares"
            ),
            "B_VERIFIER_EXACT": (
                "candidate only; regenerates shares from raw values under frozen verifier order"
            ),
            "C_BOUNDED_DERIVED_EQUIVALENCE": (
                "not selected and no tolerance proposed in preparation; may be considered only "
                "after predicate invariance and adversarial review"
            ),
            "D_SEMANTICS_SENSITIVE_BLOCK": (
                "mandatory verdict if any frozen criterion or candidate aggregate changes"
            ),
        },
        "proposed_canonical_semantics_if_and_only_if_invariant": {
            "proposal_id": (
                "RAW_AUTHORITATIVE_SHARED_NUMPY_ORDERED_FLOAT64_DERIVATION_v1"
            ),
            "raw_maxima_and_normalized_values_authoritative": True,
            "cached_historical_shares_authoritative": False,
            "shared_recomputation_function": reconciliation_v1.PRODUCER_SEMANTICS,
            "reason": (
                "It records the executed producer semantics exactly while moving future "
                "authority to a shared raw-derived function."
            ),
            "selected_during_preparation": False,
            "selection_requires_predicate_invariance": True,
            "selection_requires_independent_result_review": True,
        },
        "calculation_tool": {
            **tool_binding,
            "tool_id": reconciliation_v1.TOOL_ID,
            "pure_self_validation": self_validation,
            "pure_self_validation_pass_count": sum(self_validation.values()),
            "pure_self_validation_count": len(self_validation),
            "reads_role_payloads_during_packet_preparation": False,
            "invokes_simulation": False,
            "implementation_module_use": "directory_tree_sha256 only",
            "modifies_frozen_assembler_source": False,
            "modifies_historical_payloads": False,
            "comparison_semantics_count": 2,
        },
        "focused_test_source": test_binding,
        "one_calculation_contract": {
            "calculation_authorized_now": False,
            "independent_packet_review_anchor_required": True,
            "authorized_calculation_count_after_acceptance": 1,
            "source_output_tree_sha256": source_tree,
            "expected_field_count": 1792,
            "expected_derived_result_relative_path": (
                reconciliation_v1.RESULT_RELATIVE_PATH
            ),
            "derived_result_root_currently_absent": True,
            "comparison_rows_required": [
                "producer value",
                "verifier value",
                "absolute difference",
                "relative difference",
                "ULP distance",
                "dominant-block change",
            ],
            "decision_comparisons_required": [
                "dominant-block changes",
                "event-ordering changes",
                "threshold-decision changes",
                "H_A-H_E predicate changes",
                "final candidate-classification changes",
            ],
            "candidate_classifications_authoritative": False,
            "independent_reconciliation_result_review_required": True,
        },
        "hypothesis_dependency_map": {
            "H_A_CANCELLATION_CONDITIONING": (
                "share-reduction independent; status still compared"
            ),
            "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE": (
                "share-reduction dependent"
            ),
            "H_C_DISCRETE_CLOSURE_MISMATCH": (
                "share-reduction independent; status still compared"
            ),
            "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR": (
                "share-reduction dependent"
            ),
            "H_E_UNRESOLVED_MECHANISM": (
                "aggregate-dependent and never assigned during preparation/calculation"
            ),
        },
        "independent_packet_review_requirements": [
            "reconstruct the exact tool and test source hashes",
            "confirm only NumPy producer and Python verifier reductions are compared",
            "confirm all signed-zero, nonfinite, ordering, and denominator rules are explicit",
            "confirm the calculation cannot run without an accepted review anchor",
            "confirm the source output tree is path- and hash-bound",
            "confirm the derived result root is absent",
            "confirm no simulation invocation or source-payload write path is reachable",
            "confirm candidate predicate evaluations remain nonauthoritative",
            "confirm one calculation and one result review are the hard stop",
        ],
        "decision_rule_after_calculation": {
            "PREDICATE_INVARIANT": (
                "all dominant blocks, event ordering, criterion statuses, hypothesis statuses, "
                "supported-mechanism sets, and aggregate candidates agree; a later independent "
                "review may select explicit canonical derived semantics"
            ),
            "PREDICATE_SENSITIVE": (
                "record BLOCKED_OBSERVABLE_DECISION_INSTABILITY, keep H_A-H_E unevaluated, "
                "and close the R13 mechanism lane"
            ),
        },
        "hard_stop": {
            "packet_count": 1,
            "read_only_calculation_count": 1,
            "independent_result_review_count": 1,
            "second_reconciliation_loop_authorized": False,
            "new_simulation_authorized": False,
            "threshold_tuning_authorized": False,
            "additional_summation_algorithms_authorized": False,
            "general_floating_point_framework_authorized": False,
        },
        "preparation_status": {
            "source_payload_arrays_read": False,
            "derived_field_comparison_performed": False,
            "classifier_predicates_compared": False,
            "canonical_semantics_selected": False,
            "H_A_through_H_E_evaluated": False,
            "derived_output_created": False,
            "simulation_invoked": False,
        },
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_E_REPRO": "PRESERVED",
            "fourteen_row_robustness": "NUMERICALLY_BLOCKED",
            "descendant_materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "R13_root_mechanism": "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "claim_ceiling": (
            "Preparation of one observable-semantics reconciliation only. No calculation, "
            "canonical-semantics selection, H_A-H_E result, simulation, robustness "
            "reclassification, materiality result, or new E-REPRO is authorized."
        ),
    }


def artifact_bytes() -> bytes:
    return canonical_json_bytes(build_packet())


def write_or_check(check: bool) -> None:
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if check:
        if not path.is_file() or path.read_bytes() != raw:
            raise SystemExit(f"artifact mismatch: {REPORT_RELATIVE_PATH}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    packet = json.loads(raw.decode("utf-8"))
    print(
        json.dumps(
            {
                "status": "CHECKED" if check else "WROTE",
                "verdict": packet["verdict"],
                "fields_frozen": packet["dispute_census"]["field_count"],
                "historical_semantics": len(packet["historical_semantics"]),
                "calculation_authorized": packet["one_calculation_contract"][
                    "calculation_authorized_now"
                ],
                "derived_output_created": packet["preparation_status"][
                    "derived_output_created"
                ],
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the observable-semantics reconciliation packet v1"
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
