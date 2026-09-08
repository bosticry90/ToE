from __future__ import annotations

import argparse
import hashlib
import json
import math
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v1.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v1.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_"
    "replacement_packet_review_v1.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketReviewV1.lean"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v1.json"
)
V0_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v0.json"
)

TARGET = "review_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_result"
VERDICT = "BLOCKED_ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_INCOMPLETE"
PRINCIPAL_OUTCOME = "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE"
SECONDARY_OUTCOMES = (
    "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
    "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
)
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_"
    "review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "FRESH_SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_AUTOMATIC_V2_OR_KERNEL_IMPLEMENTATION"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_20260719_v1.md":
        "9bf1dba644e61fba90ea77a26111e03ffd689f385eae8931c8a8577b05d87974",
    PACKET_RELATIVE_PATH:
        "cbd393070a567368a83327bd99e53dbb18013bba8ac9447cc7952b74a2d6c122",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1.py":
        "9c7fd5132d501da5b6de7db72418d6d3b47803f66c1fd0e15bbd0e2bf7e4d00c",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1.py":
        "caa89ca62767a021e0f6c16ee6e012b86e6562de82476830a36fe501c3e18663",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV1.lean":
        "4b1ed0b5121d7e89d424f4560d21ea81ba1d9deeb0aa863281b8a87c9fdfc471",
}

REPAIRED_GATE_IDS = (
    "R32_INTERNAL_REPLACEMENT_TARGETS_EXACT",
    "R33_LAMBDA_COMPONENT_COMPATIBILITY_MATRIX_COMPLETE",
    "R34_ARRAY_DOMAIN_FAILURE_SEMANTICS_COMPLETE",
    "R35_VALIDATION_ONLY_HOOK_ENFORCEMENT_EXECUTABLE",
    "R37_EIGHT_REGRESSION_INPUT_RECORDS_COMPLETE",
    "R40_INDEPENDENT_RADIAL_DERIVATIVE_REFERENCE_COMPLETE",
    "R41_LIMIT_AND_BOUNDARY_PROBES_NUMERIC",
    "R43_MUTATION_ROUTES_COMPLETE",
    "R44_MUTATION_DETECTION_PREDICATES_NUMERIC",
    "R50_RUNTIME_PROBE_INPUTS_EXACT",
    "R52_CANONICAL_SERIALIZATION_SCHEMA_EXACT",
)
FAILED_GATE_IDS = (
    "R35_VALIDATION_ONLY_HOOK_ENFORCEMENT_EXECUTABLE",
    "R41_LIMIT_AND_BOUNDARY_PROBES_NUMERIC",
    "R43_MUTATION_ROUTES_COMPLETE",
    "R44_MUTATION_DETECTION_PREDICATES_NUMERIC",
    "R52_CANONICAL_SERIALIZATION_SCHEMA_EXACT",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, str]:
    return {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}


def _valid_regression_rows(rows: list[dict[str, Any]]) -> bool:
    required = {
        "case_id", "component_order", "radius_1_m_hex", "radius_2_m_hex",
        "density_1_kg_m3_hex", "density_2_kg_m3_hex", "mass_1_kg_hex",
        "mass_2_kg_hex", "surface_gap_m_hex", "center_distance_m_hex",
        "lambda_m_hex", "yukawa_amplitude_hex",
        "newtonian_energy_reference_J_decimal", "yukawa_energy_reference_J_decimal",
        "newtonian_dU_dD_reference_N_decimal", "yukawa_dU_dD_reference_N_decimal",
        "energy_acceptance", "derivative_acceptance", "derivative_reference_provenance",
    }
    if len(rows) != 8 or any(not required <= set(row) for row in rows):
        return False
    for row in rows:
        try:
            values = [
                float.fromhex(row[key]) for key in (
                    "radius_1_m_hex", "radius_2_m_hex", "density_1_kg_m3_hex",
                    "density_2_kg_m3_hex", "mass_1_kg_hex", "mass_2_kg_hex",
                    "surface_gap_m_hex", "center_distance_m_hex", "lambda_m_hex",
                    "yukawa_amplitude_hex",
                )
            ]
        except (TypeError, ValueError):
            return False
        if not all(math.isfinite(value) and value > 0.0 for value in values):
            return False
        r1 = float.fromhex(row["radius_1_m_hex"])
        r2 = float.fromhex(row["radius_2_m_hex"])
        distance = float.fromhex(row["center_distance_m_hex"])
        if distance <= r1 + r2 or row["component_order"] != ["newtonian", "yukawa", "total"]:
            return False
    return True


def _valid_derivative_references(rows: list[dict[str, Any]]) -> bool:
    getcontext().prec = 100
    for row in rows:
        distance = Decimal(str(float.fromhex(row["center_distance_m_hex"])))
        lambda_m = Decimal(str(float.fromhex(row["lambda_m_hex"])))
        un = Decimal(row["newtonian_energy_reference_J_decimal"])
        uy = Decimal(row["yukawa_energy_reference_J_decimal"])
        stored_un = Decimal(row["newtonian_dU_dD_reference_N_decimal"])
        stored_uy = Decimal(row["yukawa_dU_dD_reference_N_decimal"])
        if stored_un != -un / distance:
            return False
        if stored_uy != -uy * (Decimal(1) / distance + Decimal(1) / lambda_m):
            return False
        if "NO_CANDIDATE_CALL" not in row["derivative_reference_provenance"]:
            return False
        if row["derivative_acceptance"] != {
            "absolute_tolerance_N_decimal": "1E-34",
            "relative_tolerance_decimal": "5E-12",
        }:
            return False
    return True


def build_report() -> dict[str, Any]:
    for relative_path, expected in PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"V1 replacement packet custody drift: {relative_path}")

    packet = _load_json(PACKET_RELATIVE_PATH)
    v0_review = _load_json(V0_REVIEW_RELATIVE_PATH)
    if packet.get("target") != "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1":
        raise ValueError("V1 replacement packet target mismatch")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("V1 packet did not authorize this review")
    if packet.get("verdict") != "PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V1":
        raise ValueError("V1 replacement packet verdict mismatch")

    v0_rows = v0_review["review_gates"]["rows"]
    accepted_ids = [row["gate_id"] for row in v0_rows if row["status"] == "PASS"]
    v1_scope = packet["v1_repair_scope"]
    frozen_gates_preserved = (
        len(accepted_ids) == 51
        and v1_scope["accepted_review_gate_ids"] == accepted_ids
        and v1_scope["repaired_review_gate_ids"] == list(REPAIRED_GATE_IDS)
        and len(packet["authority"]["frozen_v0_packet_artifacts"]) == 5
        and len(packet["authority"]["frozen_v0_review_artifacts"]) == 5
    )
    if not frozen_gates_preserved:
        raise ValueError("V1 did not preserve the exact V0 review partition")

    identity = packet["replacement_interface_identity_v1"]
    regressions = packet["regression_and_derivative_reference_v1"]
    probes = packet["limit_and_boundary_probe_contract_v1"]
    mutations = packet["mutation_routing_v1"]
    runtime = packet["runtime_workload_v1"]
    serialization = packet["canonical_serialization_and_comparison_v1"]

    r32 = (
        identity["candidate_replaces_internal_functions"] == [
            "uniform_sphere_form_factor", "scaled_uniform_sphere_form_factor",
            "pair_energy_and_radial_derivative",
        ]
        and identity["future_dispatch_seam_symbol"] == "SPHERE_PAIR_KERNEL_ID"
        and identity["unchanged_callers"] == [
            "apparatus_energy", "analytic_energy_derivative_torque",
            "direct_pair_force_lever_torque", "five_point_energy_derivative_torque",
        ]
        and identity["excluded_read_only_helper"] ==
        "reduced_four_dimensional_density_integral_yukawa_energy"
    )
    matrix = identity["lambda_component_compatibility_matrix"]
    r33 = len(matrix) == 12 and {
        (row["component"], row["lambda_class"]) for row in matrix
    } == {
        (component, cls)
        for component in ("newtonian", "yukawa", "total")
        for cls in ("POSITIVE_FINITE", "ZERO", "NEGATIVE_FINITE", "NONFINITE")
    } and all({
        "historical_v0_behavior", "proposed_v1_behavior", "compatibility",
        "failure_type_if_rejected",
    } <= set(row) for row in matrix)
    array = identity["array_invalid_element_behavior"]
    r34 = (
        array["atomic"] is True and array["partial_output"] == "FORBIDDEN"
        and array["input_mutation"] == "FORBIDDEN"
        and array["invalid_index_order"] == "ASCENDING_C_ORDER_FLAT_INDICES"
        and identity["component_evaluation_order"][4] ==
        "IF_ANY_INVALID_RAISE_ONE_VALUE_ERROR_BEFORE_ANY_OUTPUT"
    )

    hooks = identity["validation_hook_authorization_mechanism"]
    executable_hook_keys = {
        "capability_issuer", "private_entrypoint_signature",
        "capability_constructor_visibility", "capability_validation_failure",
        "capability_process_scope", "mutation_id_binding",
    }
    missing_hook_keys = sorted(executable_hook_keys - set(hooks))
    r35 = not missing_hook_keys

    rows = regressions["rows"]
    r37 = _valid_regression_rows(rows)
    r40 = _valid_derivative_references(rows)

    numeric_probe_keys = {
        "expected_energy_decimal", "expected_derivative_decimal",
        "energy_absolute_tolerance_decimal", "energy_relative_tolerance_decimal",
        "derivative_absolute_tolerance_decimal", "derivative_relative_tolerance_decimal",
    }
    exception_probe_keys = {"required_exception_type", "required_exception_message"}
    relational_probe_keys = {
        "comparison_operands", "comparison_operator", "comparison_threshold_decimal",
    }
    probe_rows = probes["rows"]
    fully_adjudicable_probe_ids = [
        row["probe_id"] for row in probe_rows
        if numeric_probe_keys <= set(row)
        or exception_probe_keys <= set(row)
        or relational_probe_keys <= set(row)
    ]
    incomplete_probe_ids = [
        row["probe_id"] for row in probe_rows
        if row["probe_id"] not in fully_adjudicable_probe_ids
    ]
    p13 = next(row for row in probe_rows if row["probe_id"] == "P13_EMPTY_ARRAY_REJECTED")
    p13_required_inputs_complete = {
        "distance_m_hex_array", "lambda_m_hex", "mass_1_kg_hex", "mass_2_kg_hex",
        "radius_1_m_hex", "radius_2_m_hex", "yukawa_amplitude_hex",
    } <= set(p13["inputs"])
    r41 = (
        len(probe_rows) == 13 and not incomplete_probe_ids
        and p13_required_inputs_complete
    )

    route_keys = {
        "candidate_function", "private_entrypoint", "capability_argument",
        "injection_operation", "adjudicator",
    }
    mutation_rows = mutations["rows"]
    route_complete_ids = [
        row["mutation_id"] for row in mutation_rows if route_keys <= set(row)
    ]
    r43 = len(mutation_rows) == 12 and len(route_complete_ids) == 12
    predicate_keys = {
        "predicate_kind", "observed_field", "operator", "threshold_or_exception",
    }
    predicate_complete_ids = [
        row["mutation_id"] for row in mutation_rows if predicate_keys <= set(row)
    ]
    static_row = next(row for row in mutation_rows if row["mutation_id"].startswith("M12_"))
    static_scanner_keys = {
        "scanner_entrypoint", "source_roots", "forbidden_imports",
        "forbidden_call_targets", "scan_failure_type",
    }
    static_scanner_complete = static_scanner_keys <= set(static_row)
    r44 = len(predicate_complete_ids) == 12 and static_scanner_complete

    r50 = (
        runtime["timed_call_count_per_trial"] == 10000
        and runtime["warmup_call_count"] == 24
        and runtime["trial_count"] == 5
        and len(runtime["runtime_probe_case_rows"]) == 8
        and runtime["runtime_probe_case_order"] == [row["case_id"] for row in rows]
        and runtime["runtime_probe_component_order"] == ["newtonian", "yukawa", "total"]
        and runtime["maximum_median_seconds"] == 5.0
        and runtime["parallelism"] == "FORBIDDEN_SINGLE_PROCESS_SINGLE_THREAD"
    )

    nested_schema_keys = {
        "custody_schema", "regression_row_schema", "limit_row_schema",
        "mutation_row_schema", "runtime_schema", "status_enum",
        "terminal_outcome_enum", "duplicate_key_parser",
    }
    missing_nested_schema_keys = sorted(nested_schema_keys - set(serialization))
    r52 = len(serialization["root_keys_exact"]) == 11 and not missing_nested_schema_keys

    repair_results = {
        "R32_INTERNAL_REPLACEMENT_TARGETS_EXACT": (r32, "internal targets, dispatch seam, callers, and excluded helper are exact"),
        "R33_LAMBDA_COMPONENT_COMPATIBILITY_MATRIX_COMPLETE": (r33, "all twelve component/range rows are unique and complete"),
        "R34_ARRAY_DOMAIN_FAILURE_SEMANTICS_COMPLETE": (r34, "array preflight is atomic and invalid-index reporting is exact"),
        "R35_VALIDATION_ONLY_HOOK_ENFORCEMENT_EXECUTABLE": (r35, f"named capability route omits executable fields: {missing_hook_keys}"),
        "R37_EIGHT_REGRESSION_INPUT_RECORDS_COMPLETE": (r37, "eight finite nonoverlapping binary64 rows contain every required input and reference"),
        "R40_INDEPENDENT_RADIAL_DERIVATIVE_REFERENCE_COMPLETE": (r40, "all sixteen derivative values reproduce from accepted energy evidence without a candidate call"),
        "R41_LIMIT_AND_BOUNDARY_PROBES_NUMERIC": (r41, f"typed numeric/exception/relational adjudicators absent for {incomplete_probe_ids}; P13 complete inputs={p13_required_inputs_complete}"),
        "R43_MUTATION_ROUTES_COMPLETE": (r43, f"fully bound private candidate routes present for {len(route_complete_ids)}/12 mutations"),
        "R44_MUTATION_DETECTION_PREDICATES_NUMERIC": (r44, f"structured predicates present for {len(predicate_complete_ids)}/12; static scanner complete={static_scanner_complete}"),
        "R50_RUNTIME_PROBE_INPUTS_EXACT": (r50, "eight-case, three-component, warmup, trial, clock, and threshold workload is exact"),
        "R52_CANONICAL_SERIALIZATION_SCHEMA_EXACT": (r52, f"root keys and encoding are fixed, but nested schema fields are absent: {missing_nested_schema_keys}"),
    }

    review_rows: list[dict[str, str]] = []
    for row in v0_rows:
        gate_id = row["gate_id"]
        if gate_id in repair_results:
            passed, finding = repair_results[gate_id]
            review_rows.append(_gate(gate_id, passed, finding))
        else:
            review_rows.append(_gate(gate_id, True, "accepted V0 gate preserved by frozen artifact custody"))
    failed = [row["gate_id"] for row in review_rows if row["status"] == "FAIL"]
    if tuple(failed) != FAILED_GATE_IDS:
        raise ValueError(f"unexpected V1 review failure set: {failed}")

    scope = {
        "independent_v1_review_performed": True,
        "v1_packet_custody_verified": True,
        "fifty_one_frozen_gates_preserved": True,
        "six_of_eleven_repairs_accepted": True,
        "five_repairs_blocked": True,
        "fresh_scientific_response_selector_authorized": True,
        "replacement_contract_ready": False,
        "candidate_kernel_creation_authorized": False,
        "candidate_kernel_created": False,
        "candidate_kernel_execution_authorized": False,
        "candidate_kernel_executed": False,
        "production_source_or_dispatch_change_authorized": False,
        "shadow_qualification_authorized": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "silent_correction_authorized": False,
        "automatic_v2_authorized": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_kernel.replacement_packet_review.v1",
        "review_id": "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_REVIEW_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "INDEPENDENT_FINAL_V1_PRE_IMPLEMENTATION_REVIEW_COMPLETE_BLOCKED",
        "principal_review_outcome": PRINCIPAL_OUTCOME,
        "secondary_review_outcomes": list(SECONDARY_OUTCOMES),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in PACKET_HASHES.items()
            ],
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
                "replacement_packet_review_v1.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "frozen_gate_audit": {
            "accepted_v0_gate_count": len(accepted_ids),
            "accepted_v0_gate_ids": accepted_ids,
            "preserved_count": len(accepted_ids),
            "altered_or_weakened_gate_ids": [],
            "custody_result": "PASS",
        },
        "repair_audit": {
            "repair_gate_count": len(REPAIRED_GATE_IDS),
            "passed_repair_gate_ids": [
                gate_id for gate_id in REPAIRED_GATE_IDS if gate_id not in FAILED_GATE_IDS
            ],
            "failed_repair_gate_ids": list(FAILED_GATE_IDS),
            "validation_hook_missing_fields": missing_hook_keys,
            "incomplete_probe_ids": incomplete_probe_ids,
            "p13_complete_public_inputs": p13_required_inputs_complete,
            "mutation_route_complete_count": len(route_complete_ids),
            "mutation_predicate_complete_count": len(predicate_complete_ids),
            "static_scanner_complete": static_scanner_complete,
            "serialization_missing_nested_schema_fields": missing_nested_schema_keys,
        },
        "accepted_v1_repairs": {
            "replacement_target_and_dispatch_identity": "ACCEPTED",
            "component_lambda_compatibility_matrix": "ACCEPTED",
            "atomic_array_failure_semantics": "ACCEPTED",
            "complete_regression_inputs": "ACCEPTED",
            "energy_derived_derivative_references": "ACCEPTED",
            "runtime_workload": "ACCEPTED",
        },
        "blocking_findings": [
            {
                "finding_id": "F01_VALIDATION_CAPABILITY_ROUTE_NOT_EXECUTABLE",
                "outcome": "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE",
                "detail": "The packet names a private entrypoint and capability type but freezes no issuer, private signature, constructor visibility, process scope, validation failure, or mutation binding.",
            },
            {
                "finding_id": "F02_LIMIT_PROBES_NOT_QUANTITATIVELY_ADJUDICABLE",
                "outcome": "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
                "detail": "Probe rows carry qualitative expected strings and generic tolerances rather than typed numeric, exception, or relational predicates; the empty-array probe also omits mandatory public inputs.",
            },
            {
                "finding_id": "F03_MUTATION_ROUTES_AND_PREDICATES_NOT_EXECUTABLE",
                "outcome": "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE",
                "detail": "Symbolic injection labels are not bound to a private candidate call/capability/adjudicator, predicates are unstructured strings, and the forbidden-dependency scanner has no executable scan contract.",
            },
            {
                "finding_id": "F04_CANONICAL_RESULT_SCHEMA_ONLY_FIXES_ROOT",
                "outcome": "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
                "detail": "The eleven root keys and JSON byte encoding are frozen, but nested row/custody/runtime schemas, enums, and duplicate-key parser are absent.",
            },
        ],
        "review_gates": {
            "gate_count": len(review_rows),
            "pass_count": sum(row["status"] == "PASS" for row in review_rows),
            "failure_count": len(failed),
            "failed_gate_ids": failed,
            "rows": review_rows,
        },
        "required_next_action": {
            "fresh_selector_required": True,
            "silent_correction": "PROHIBITED",
            "automatic_v2": "PROHIBITED",
            "candidate_creation_or_execution": "NOT_AUTHORIZED",
            "bounded_selector_options": [
                "NARROW_OR_SPLIT_THE_REPLACEMENT_QUALIFICATION_BURDEN",
                "RETIRE_ANALYTIC_REPLACEMENT_IMPLEMENTATION_LANE",
                "DEFER_OR_CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
            ],
        },
        "scope": scope,
        "claim_ceiling": (
            "This final V1 review preserves all 51 accepted V0 gates and accepts six of the "
            "eleven repairs, but finds five remaining execution-contract defects. It does not "
            "repair V1, create or execute a candidate, change production source or dispatch, "
            "qualify a shadow kernel, call or adjudicate cubature, rerun Stage A, compute torque, "
            "DFT, vector, Jacobian, SVD, or identifiability, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the final analytic sphere-kernel replacement packet V1."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    output = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output.read_bytes() if output.exists() else None
    if args.write:
        if current != expected:
            output.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("analytic sphere-kernel replacement V1 review already current")
        return 0
    if current != expected:
        print("analytic sphere-kernel replacement V1 review drift")
        return 1
    report = build_report()
    print(
        "analytic sphere-kernel replacement V1 review OK "
        f"verdict={report['verdict']} pass={report['review_gates']['pass_count']} "
        f"fail={report['review_gates']['failure_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
