from __future__ import annotations

"""Prepare the narrow observable-semantics reconciliation packet v2."""

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
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_review_v1
    as review_v1,
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
CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = review_v1.SELECTED_NEXT_TARGET
SELECTED_NEXT_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_v2_result"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_20260716_v2"
)
REPORT_RELATIVE_PATH = reconciliation_v2.PACKET_RELATIVE_PATH
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_v2.py"
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
    v1_review_path = REPO_ROOT / review_v1.REPORT_RELATIVE_PATH
    v1_review_raw = v1_review_path.read_bytes()
    v1_review = json.loads(v1_review_raw.decode("utf-8"))
    if (
        sha256_bytes(v1_review_raw) != reconciliation_v2.EXPECTED_V1_REVIEW_SHA256
        or v1_review.get("verdict")
        != "BLOCKED_DECISION_INVARIANCE_GATE_INCOMPLETE"
        or v1_review.get("selected_next_target") != TARGET
    ):
        raise ValueError("v1 blocking-review authority mismatch")
    source_root = (
        REPO_ROOT
        / "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
    )
    source_tree = implementation_v0.directory_tree_sha256(source_root)
    if source_tree != reconciliation_v2.EXPECTED_SOURCE_OUTPUT_TREE_SHA256:
        raise ValueError("preserved source output tree mismatch")
    if (REPO_ROOT / reconciliation_v2.REVIEW_RELATIVE_PATH).exists():
        raise ValueError("independent v2 packet review must not preexist preparation")
    if (REPO_ROOT / reconciliation_v2.RESULT_OUTPUT_ROOT_RELATIVE_PATH).exists():
        raise ValueError("v2 derived result root must be absent in preparation")
    self_validation = reconciliation_v2.self_validate()
    if not all(self_validation.values()):
        raise ValueError("v2 pure self-validation failed")
    tool_binding = _source_binding(reconciliation_v2.SCRIPT_RELATIVE_PATH)
    predecessor_binding = _source_binding(predecessor_v1.SCRIPT_RELATIVE_PATH)
    if predecessor_binding["sha256"] != reconciliation_v2.EXPECTED_PREDECESSOR_TOOL_SHA256:
        raise ValueError("predecessor tool identity changed")
    test_binding = _source_binding(TEST_RELATIVE_PATH)
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "predecessor_review": {
            "relative_path": review_v1.REPORT_RELATIVE_PATH,
            "sha256": sha256_bytes(v1_review_raw),
            "verdict": v1_review["verdict"],
            "first_diagnostic": v1_review["first_diagnostic"],
        },
        "preserved_foundation": {
            "v1_foundation_check_count": 14,
            "v1_passed_foundation_check_count": 14,
            "source_output_tree_sha256": source_tree,
            "source_output_file_count": 14,
            "historical_reduction_count": len(predecessor_v1.SEMANTICS_IDS),
            "ordered_vector_count": 224,
            "field_count": reconciliation_v2.EXPECTED_FIELD_COUNT,
            "block_order": list(raw_v3.BLOCK_IDS),
            "thresholds_changed": False,
            "hypothesis_definitions_changed": False,
            "aggregate_logic_changed": False,
        },
        "calculation_tool": {
            **tool_binding,
            "tool_id": reconciliation_v2.TOOL_ID,
            "predecessor_tool_relative_path": predecessor_binding[
                "relative_path"
            ],
            "predecessor_tool_sha256": predecessor_binding["sha256"],
            "pure_self_validation": self_validation,
            "pure_self_validation_pass_count": sum(self_validation.values()),
            "pure_self_validation_count": len(self_validation),
            "reads_actual_payloads_during_preparation": False,
            "invokes_simulation": False,
            "historical_reduction_count": 2,
        },
        "focused_test_source": test_binding,
        "ranking_contract": {
            "ranked_value": "derived binary64 dominance share",
            "direction": "descending",
            "exact_tie_rule": "numeric binary64 equality",
            "signed_zero_rule": "+0.0 and -0.0 are one tie value",
            "tie_group_representation": (
                "members remain in the frozen eight-block order; this does not break the tie"
            ),
            "per_record_levels": (
                "all 224 solver-iteration and terminal records are decision-bearing for "
                "reconciliation stability"
            ),
            "role_levels": (
                "all three median_share_by_block rankings and dominant_block_id values"
            ),
            "separate_counts": [
                "per_record_winner_change_count",
                "role_level_dominant_block_change_count",
                "per_record_ordering_change_count",
                "role_ordering_change_count",
                "ordering_change_count",
            ],
            "ordering_change_count_definition": (
                "per_record_ordering_change_count + role_ordering_change_count"
            ),
            "winner_and_ordering_counts_are_aliases": False,
        },
        "ulp_summary_contract": {
            "categories": [
                "exact_matches",
                "one_ulp_differences",
                "two_ulp_differences",
                "greater_than_two_ulp_differences",
            ],
            "categories_mutually_exclusive": True,
            "categories_exhaustive": True,
            "sum_must_equal": reconciliation_v2.EXPECTED_FIELD_COUNT,
            "scientific_invariance_gate": False,
            "purpose": "descriptive only",
        },
        "decision_invariance_contract": {
            "gate_ids": list(reconciliation_v2.INVARIANCE_GATE_IDS),
            "gate_count": len(reconciliation_v2.INVARIANCE_GATE_IDS),
            "invariant_if_and_only_if_all_gates_true": True,
            "terminal_classifications": list(
                reconciliation_v2.TERMINAL_CLASSIFICATIONS
            ),
            "terminal_classification_count": 2,
            "no_intermediate_or_discretionary_result": True,
            "ulp_magnitude_alone_is_not_a_gate": True,
        },
        "candidate_aggregate_contract_frozen_unchanged": {
            "multiple_A_through_D_support_allowed": True,
            "multiple_support_result": "MULTIPLE_SUPPORTED_MECHANISMS",
            "H_E_only_after_empty_A_through_D_support": True,
            "incomplete_evidence_status": "NOT_EVALUATED",
            "both_semantics_call_same_aggregate_function": True,
        },
        "registered_synthetic_controls": [
            {
                "control_id": "ROLE_WINNER_MUTATION",
                "expected_terminal": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
            },
            {
                "control_id": "LOWER_RANK_ORDERING_SWAP_SAME_WINNER",
                "expected_terminal": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
            },
            {
                "control_id": "PER_RECORD_WINNER_MUTATION",
                "expected_terminal": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
            },
            {
                "control_id": "THRESHOLD_STATUS_MUTATION",
                "expected_terminal": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
            },
            {
                "control_id": "HYPOTHESIS_STATUS_MUTATION",
                "expected_terminal": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
            },
            {
                "control_id": "AGGREGATE_RESULT_MUTATION",
                "expected_terminal": reconciliation_v2.TERMINAL_DECISION_INSTABILITY,
            },
            {
                "control_id": "PURE_ONE_TWO_ULP_NO_DECISION_CHANGE",
                "expected_terminal": reconciliation_v2.TERMINAL_PREDICATE_INVARIANT,
            },
            {
                "control_id": "ALL_GATES_TRUE",
                "expected_terminal": reconciliation_v2.TERMINAL_PREDICATE_INVARIANT,
            },
        ],
        "one_calculation_contract": {
            "calculation_authorized_now": False,
            "independent_v2_packet_review_required": True,
            "authorized_calculation_count_after_acceptance": 1,
            "source_output_tree_sha256": source_tree,
            "expected_field_count": reconciliation_v2.EXPECTED_FIELD_COUNT,
            "expected_record_count": reconciliation_v2.EXPECTED_RECORD_COUNT,
            "expected_role_count": reconciliation_v2.EXPECTED_ROLE_COUNT,
            "expected_result_relative_path": reconciliation_v2.RESULT_RELATIVE_PATH,
            "derived_result_root_currently_absent": True,
            "candidate_results_authoritative": False,
            "independent_reconciliation_result_review_required": True,
        },
        "independent_v2_review_requirements": [
            "reconstruct all fourteen accepted v1 foundation checks",
            "verify role-level dominant-block mutations force instability",
            "verify lower-rank ordering swaps force instability without changing the winner",
            "verify winner and ordering counts are independent",
            "verify both terminal labels are reachable and mutually exclusive",
            "verify four ULP bins are present, mutually exclusive, and exhaustive",
            "verify threshold, hypothesis, and aggregate mutations force instability",
            "verify 1-2 ULP changes without decision changes remain invariant-eligible",
            "verify no actual payload is read and no derived output is created",
            "verify no simulation path is invoked and the source tree is unchanged",
        ],
        "hard_stop": {
            "packet_version": 2,
            "additional_packet_version_authorized": False,
            "read_only_calculation_count": 1,
            "independent_result_review_count": 1,
            "additional_reduction_algorithms_authorized": False,
            "new_observable_authorized": False,
            "new_threshold_authorized": False,
            "new_simulation_authorized": False,
            "general_ranking_framework_authorized": False,
        },
        "preparation_status": {
            "actual_payload_arrays_read": False,
            "actual_field_comparison_performed": False,
            "actual_classifier_predicates_compared": False,
            "terminal_result_assigned": False,
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
            "Narrow v2 decision-gate preparation only. No actual comparison, terminal "
            "reconciliation result, canonical-semantics selection, H_A-H_E evaluation, "
            "simulation, robustness reclassification, materiality result, or new E-REPRO."
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
                "gates": packet["decision_invariance_contract"]["gate_count"],
                "terminal_classifications": packet[
                    "decision_invariance_contract"
                ]["terminal_classification_count"],
                "synthetic_controls": len(packet["registered_synthetic_controls"]),
                "calculation_authorized": packet["one_calculation_contract"][
                    "calculation_authorized_now"
                ],
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare observable-semantics reconciliation packet v2"
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
