from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_"
    "replacement_packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketReviewV0.lean"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v0.json"
)

TARGET = "review_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_result"
VERDICT = "BLOCKED_ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_INCOMPLETE"
PRINCIPAL_OUTCOME = "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE"
SECONDARY_OUTCOMES = (
    "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
    "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
)
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_"
    "review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "FRESH_SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_AUTOMATIC_PACKET_REPAIR_OR_KERNEL_IMPLEMENTATION"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_20260719_v0.md":
        "ca67c420ebed4032d0556d88759e8f48b7d72188cf4810b132bd23fbf1bd57fb",
    PACKET_RELATIVE_PATH:
        "3b05386c4b386595d41a283c8b665386fc55abc81f865218a3eff1395755bcec",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0.py":
        "cda104a3546fad24d74166d0d880b0e9ee6dfdbea4a6f34bfa0cb3697cbbf124",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0.py":
        "e44a2fe8b3cb3e0902ad57e7c4004e07bb577c7c30419e90778a96ba9e92b1e0",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV0.lean":
        "21096d6a5fe86ca912798dc7f7d92941f2aac389f5743dbf4167c031c87117a0",
}

FAILED_GATE_IDS = (
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


def build_report() -> dict[str, Any]:
    for relative_path, expected in PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"replacement packet custody drift: {relative_path}")

    packet = _load_json(PACKET_RELATIVE_PATH)
    if packet.get("target") != (
        "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0"
    ):
        raise ValueError("replacement packet target mismatch")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("replacement packet did not authorize this review")
    if packet.get("verdict") != (
        "PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V0"
    ):
        raise ValueError("replacement packet verdict mismatch")

    identity = packet["historical_path_identity"]
    kernel = packet["analytic_kernel_contract"]
    evaluator = packet["numerical_evaluator_contract"]
    domain = packet["domain_and_limit_contract"]
    interface = packet["caller_interface_contract"]
    regressions = packet["accepted_oracle_regression_contract"]
    validation = packet["validation_independence_contract"]
    future = packet["future_shadow_qualification_contract"]
    adoption = packet["implementation_adoption_and_rollback_contract"]
    scope = packet["scope"]

    internal_targets_exact = all(
        key in identity
        for key in (
            "candidate_replaces_internal_functions",
            "dispatch_seam_symbol",
            "unchanged_callers",
        )
    )
    lambda_matrix_complete = "lambda_component_compatibility_matrix" in interface
    array_failure_complete = "array_invalid_element_behavior" in interface
    hook_enforcement_complete = "validation_hook_authorization_mechanism" in interface

    regression_required_inputs = {
        "radius_1_m",
        "radius_2_m",
        "mass_1_kg",
        "mass_2_kg",
        "surface_gap_m",
        "center_distance_m",
        "lambda_m",
        "yukawa_amplitude",
    }
    regression_input_keys = set.intersection(
        *(set(row) for row in regressions["rows"])
    ) if regressions["rows"] else set()
    regression_inputs_complete = regression_required_inputs <= regression_input_keys

    derivative_reference_keys = {
        "newtonian_dU_dD_reference_J_per_m_decimal",
        "yukawa_dU_dD_reference_J_per_m_decimal",
        "derivative_tolerance",
    }
    derivative_reference_complete = derivative_reference_keys <= regression_input_keys

    exact_limit_rows = validation.get("limit_and_boundary_probe_rows")
    limits_numeric = isinstance(exact_limit_rows, list) and bool(exact_limit_rows) and all(
        isinstance(row, dict)
        and {"probe_id", "inputs", "expected", "absolute_tolerance", "relative_tolerance"}
        <= set(row)
        for row in exact_limit_rows
    )

    mutation_required_keys = {
        "mutation_id",
        "case_ids",
        "components",
        "injection_point",
        "execution_order",
        "acceptance_rule",
        "failure_consequence",
    }
    mutation_rows = validation["validation_mutations"]
    mutation_routes_complete = all(mutation_required_keys <= set(row) for row in mutation_rows)
    mutation_predicates_numeric = all(
        isinstance(row.get("absolute_tolerance"), (int, float))
        or isinstance(row.get("relative_tolerance"), (int, float))
        or isinstance(row.get("required_exception"), str)
        for row in mutation_rows
    )

    runtime_inputs_exact = all(
        key in future
        for key in (
            "runtime_probe_case_rows",
            "runtime_probe_case_order",
            "runtime_probe_component_order",
        )
    )
    serialization_exact = all(
        key in adoption
        for key in (
            "canonical_serialization_schema",
            "float_serialization_rule",
            "key_order_rule",
            "serialization_failure_consequence",
        )
    )

    gate_rows = [
        _gate("R01_EXACT_PACKET_CUSTODY", True, "five packet artifacts hash-verified"),
        _gate("R02_SELECTOR_AUTHORITY_PRESERVED", len(packet["authority"]["frozen_selector_artifacts"]) == 5, "selector custody retained"),
        _gate("R03_ACCEPTED_ORACLE_CUSTODY_PRESERVED", len(packet["authority"]["frozen_accepted_oracle_artifacts"]) == 8, "accepted execution and review evidence pinned"),
        _gate("R04_HISTORICAL_INTERFACE_CUSTODY_PRESERVED", len(packet["authority"]["frozen_historical_interface_artifacts"]) == 3, "Stage A interface sources pinned"),
        _gate("R05_PREPARED_STATUS_NO_IMPLEMENTATION", packet["status"] == "PREPARED_PENDING_INDEPENDENT_REVIEW_NO_IMPLEMENTATION", "pre-implementation status exact"),
        _gate("R06_SCOPE_FIREWALL_NO_KERNEL_CREATED", scope["analytic_kernel_implemented"] is False and scope["production_kernel_replaced"] is False, "no candidate or production change"),
        _gate("R07_OLD_CUBATURE_UNADJUDICATED", scope["old_cubature_adjudicated"] is False, "retirement created no scientific verdict"),
        _gate("R08_LIVE_ENTRYPOINT_AND_HELPER_DISTINCT", identity["paths_are_distinct"] is True, "live entry point is not relabeled as cubature helper"),
        _gate("R09_NEWTONIAN_ENERGY_FORMULA", kernel["newtonian_energy"] == "U_N=-G*M1*M2/D", "formula exact"),
        _gate("R10_NEWTONIAN_DERIVATIVE_FORMULA", kernel["newtonian_radial_derivative"] == "dU_N/dD=G*M1*M2/D^2", "derivative sign and power exact"),
        _gate("R11_YUKAWA_TWO_FACTOR_ENERGY_FORMULA", "F(x1)*F(x2)*exp(-D/lambda)" in kernel["yukawa_energy"], "two factors and center exponent present"),
        _gate("R12_YUKAWA_RADIAL_DERIVATIVE_FORMULA", "1/D^2+1/(lambda*D)" in kernel["yukawa_radial_derivative"], "analytic dU/dD exact"),
        _gate("R13_AMPLITUDE_UNITS_AND_SIGNS", kernel["yukawa_amplitude_production_exact"] == "1/3" and kernel["units"]["energy"] == "J", "A_Y, J, and signs frozen"),
        _gate("R14_EXCHANGE_AND_RADIUS_SYMMETRY", kernel["sphere_exchange_symmetry_required"] and kernel["equal_and_unequal_radii_supported"], "same formula for both radius classes"),
        _gate("R15_SCALED_SURFACE_GAP_IDENTITY", "exp(-g/lambda)" in kernel["stable_pair_identity"], "stable identity exact"),
        _gate("R16_SMALL_X_BRANCH", evaluator["small_x"]["domain"] == "0<=x<=0.1", "series boundary fixed"),
        _gate("R17_MODERATE_X_BRANCH", evaluator["moderate_x"]["domain"] == "0.1<x<=40", "direct branch bounded"),
        _gate("R18_LARGE_X_BRANCH", evaluator["large_x"]["domain"] == "40<x<=1000" and evaluator["large_x"]["direct_sinh_or_cosh_forbidden"], "scaled branch required"),
        _gate("R19_X1000_AND_OUT_OF_DOMAIN_BEHAVIOR", evaluator["qualified_x_interval"] == "0<=x<=1000" and evaluator["x_above_1000"].startswith("REJECT"), "qualified endpoint exact"),
        _gate("R20_SIX_OVERLAP_PROBES", sum(len(row["x_values"]) for row in evaluator["overlap_probes"]) == 6, "both overlap grids retained"),
        _gate("R21_FINITE_INPUT_GUARDS", len(domain["finite_required"]) == 7, "decision-bearing scalars finite"),
        _gate("R22_STRICT_NONOVERLAP_DOMAIN", "D>R1+R2" in domain["production_physical_domain"], "strict nonoverlap exact"),
        _gate("R23_MACHINE_RESOLVABLE_GAP", "16*ulp" in domain["machine_resolvable_gap_rule"], "binary64 gap margin fixed"),
        _gate("R24_TOUCHING_AND_OVERLAP_REJECTION", domain["touching_or_overlap"] == "REJECT", "domain fails closed"),
        _gate("R25_POINT_PARTICLE_COMPATIBILITY", "H(0)=1" in domain["point_particle_compatibility"], "zero-radius limit explicit"),
        _gate("R26_NEAR_CONTACT_LIMIT", "g_TO_0_PLUS" in domain["near_contact_limit"], "finite analytic limit stated"),
        _gate("R27_LARGE_SEPARATION_AND_LONG_RANGE_LIMITS", "D_TO_INFINITY" in domain["large_separation_limit"] and "lambda_TO_INFINITY" in domain["long_range_limit"], "both asymptotic claims stated"),
        _gate("R28_SMALL_COUPLING_LIMIT", "LINEAR_IN_A_Y" in domain["small_coupling_limit"], "zero and linear limits stated"),
        _gate("R29_PUBLIC_ENTRYPOINT_IDENTITY", interface["public_compatibility_entrypoint"] == "pair_energy_and_radial_derivative", "caller name frozen"),
        _gate("R30_OUTPUT_SHAPE_DTYPE_AND_COMPONENTS", "numpy_float64_array" in interface["return_schema"] and interface["components"] == ["newtonian", "yukawa", "total"], "public return surface frozen"),
        _gate("R31_MUTATION_HOOKS_IDENTIFIED", len(interface["mutation_only_arguments"]) == 3, "nonproduction arguments named"),
        _gate("R32_INTERNAL_REPLACEMENT_TARGETS_EXACT", internal_targets_exact, "missing exact internal function replacement list, dispatch symbol, and unchanged caller list"),
        _gate("R33_LAMBDA_COMPONENT_COMPATIBILITY_MATRIX_COMPLETE", lambda_matrix_complete, "no complete current-versus-proposed matrix for lambda<=0 across all components"),
        _gate("R34_ARRAY_DOMAIN_FAILURE_SEMANTICS_COMPLETE", array_failure_complete, "array call behavior with one invalid element is unspecified"),
        _gate("R35_VALIDATION_ONLY_HOOK_ENFORCEMENT_EXECUTABLE", hook_enforcement_complete, "hooks are labeled validation-only but no enforceable authorization route is frozen"),
        _gate("R36_EIGHT_REGRESSION_CASE_IDENTITIES", regressions["case_order"] == [row["case_id"] for row in regressions["rows"]] and len(regressions["rows"]) == 8, "case IDs and order exact"),
        _gate("R37_EIGHT_REGRESSION_INPUT_RECORDS_COMPLETE", regression_inputs_complete, "rows freeze outputs but omit radii, masses, gap, distance, lambda, and amplitude"),
        _gate("R38_ACCEPTED_REFERENCE_VALUES_PINNED", all("newtonian_reference_J_decimal" in row and "yukawa_reference_J_decimal" in row for row in regressions["rows"]), "energy references present"),
        _gate("R39_ENERGY_AGREEMENT_TOLERANCES", "1e-38" in regressions["newtonian_tolerance"] and "5e-12" in regressions["yukawa_tolerance"], "energy tolerance envelope numeric"),
        _gate("R40_INDEPENDENT_RADIAL_DERIVATIVE_REFERENCE_COMPLETE", derivative_reference_complete, "dU/dD is decision-bearing but has no independent values or tolerance"),
        _gate("R41_LIMIT_AND_BOUNDARY_PROBES_NUMERIC", limits_numeric, "limits are named but exact cases, ladders, expected values, and tolerances are absent"),
        _gate("R42_TWELVE_MUTATION_IDENTITIES", len(mutation_rows) == 12, "twelve mutation IDs exact"),
        _gate("R43_MUTATION_ROUTES_COMPLETE", mutation_routes_complete, "mutation rows omit cases, components, injection points, sequence, and failure consequence"),
        _gate("R44_MUTATION_DETECTION_PREDICATES_NUMERIC", mutation_predicates_numeric, "required result text does not define numeric or exception predicates"),
        _gate("R45_ORACLE_AND_CUBATURE_IMPORT_BANS", validation["candidate_may_import_accepted_oracle_evaluator"] is False and validation["candidate_may_import_old_cubature_helper"] is False, "candidate/reference separation declared"),
        _gate("R46_REFERENCE_PARSER_DOES_NOT_RECOMPUTE", validation["reference_parser_may_not_compute_form_factor"] is True, "reference path read-only"),
        _gate("R47_SHADOW_MODULE_ISOLATED", future["production_import_or_dispatch_change"] == "FORBIDDEN", "shadow run cannot alter production"),
        _gate("R48_TOTAL_RUNTIME_AND_MEMORY_BOUNDS", future["total_wall_clock_seconds_max"] == 300 and future["memory_mib_max"] == 1024, "resource envelope exact"),
        _gate("R49_STAGE_BUDGETS_SUM_TO_TOTAL", sum(row["seconds_max"] for row in future["stage_rows"]) == 300, "five stage caps exact"),
        _gate("R50_RUNTIME_PROBE_INPUTS_EXACT", runtime_inputs_exact, "ten-thousand-call workload lacks exact input vector and component order"),
        _gate("R51_OUTPUT_KERNEL_IDENTITY_FIELDS", adoption["every_future_output_must_record"] == ["kernel_id", "kernel_source_sha256", "oracle_reference_sha256"], "three provenance fields required"),
        _gate("R52_CANONICAL_SERIALIZATION_SCHEMA_EXACT", serialization_exact, "no canonical object schema, float encoding, key order, or failure rule"),
        _gate("R53_PROCESS_AND_ATOMIC_CUSTODY", future["process_group_termination"] == "MANDATORY" and future["stage_atomic_status"] == "REQUIRED", "future custody bounded"),
        _gate("R54_FIVE_PHASE_SEPARATION", len(adoption["phase_rows"]) == 5, "derivation, shadow, review, selection, adoption separated"),
        _gate("R55_NO_IN_PLACE_HISTORICAL_OVERWRITE", adoption["historical_source_in_place_edit_during_shadow_qualification"] == "FORBIDDEN", "historical source retained"),
        _gate("R56_ADOPTION_PRECONDITIONS", len(adoption["production_adoption_preconditions"]) == 6, "fresh selector and adoption packet required"),
        _gate("R57_ROLLBACK_NOT_SCIENTIFIC_VALIDATION", "OPERATIONAL_RESTORATION_ONLY" in adoption["rollback_result"], "rollback claim ceiling correct"),
        _gate("R58_NO_MIXED_KERNEL_OUTPUTS", adoption["mixed_kernel_outputs_in_one_scientific_record"] == "FORBIDDEN", "kernel identity cannot be mixed"),
        _gate("R59_DOWNSTREAM_FIREWALLS", not any(scope[key] for key in ("torque_or_dft_authorized", "real_150_vector_authorized", "jacobian_svd_or_identifiability_authorized", "stage_a_rerun_authorized", "stage_b_authorized")), "all downstream work closed"),
        _gate("R60_FIVE_REVIEW_OUTCOMES_EXACT", len(packet["packet_review_outcomes"]) == 5, "review namespace exact"),
        _gate("R61_READY_REVIEW_ONLY_SHADOW_QUALIFICATION", packet["review_consequence"]["production_adoption_on_ready_review"] == "NOT_AUTHORIZED", "ready cannot adopt"),
        _gate("R62_BLOCK_REQUIRES_FRESH_SELECTOR_NO_AUTOMATIC_REPAIR", packet["review_consequence"]["automatic_packet_v1_or_comparison_v2"] == "PROHIBITED", "no automatic continuation"),
    ]
    failed = [row["gate_id"] for row in gate_rows if row["status"] == "FAIL"]
    if tuple(failed) != FAILED_GATE_IDS:
        raise ValueError(f"unexpected review failure set: {failed}")

    review_scope = {
        "independent_packet_review_performed": True,
        "packet_custody_verified": True,
        "accepted_formula_and_evaluator_surfaces_preserved": True,
        "architecture_distinction_preserved": True,
        "blocked_contract_result_issued": True,
        "fresh_scientific_response_selector_authorized": True,
        "replacement_contract_ready": False,
        "shadow_kernel_implementation_authorized": False,
        "shadow_kernel_implementation_performed": False,
        "production_kernel_replacement_authorized": False,
        "production_kernel_replacement_performed": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "automatic_packet_repair_authorized": False,
        "comparison_v2_authorized": False,
        "torque_or_dft_authorized": False,
        "stage_a_rerun_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_kernel.replacement_packet_review.v0",
        "review_id": "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_REVIEW_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "INDEPENDENT_PRE_IMPLEMENTATION_PACKET_REVIEW_COMPLETE_BLOCKED",
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
                "replacement_packet_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "accepted_surfaces": {
            "newtonian_and_yukawa_formulas": "ACCEPTED_AS_ALGEBRAICALLY_COMPLETE",
            "stable_x_regimes_and_overlap_contract": "ACCEPTED",
            "strict_nonoverlap_and_machine_gap_guard": "ACCEPTED",
            "live_entrypoint_vs_cubature_helper_distinction": "ACCEPTED",
            "accepted_oracle_and_historical_source_custody": "ACCEPTED",
            "shadow_adoption_and_rollback_phase_separation": "ACCEPTED",
            "downstream_firewall": "ACCEPTED",
            "overall_replacement_contract": "NOT_READY",
        },
        "independent_interface_audit": {
            "public_entrypoint": interface["public_compatibility_entrypoint"],
            "internal_replacement_targets_exact": internal_targets_exact,
            "lambda_component_compatibility_matrix_complete": lambda_matrix_complete,
            "array_invalid_element_behavior_complete": array_failure_complete,
            "validation_hook_authorization_mechanism_complete": hook_enforcement_complete,
            "finding": (
                "The public function name and output surface are frozen, but the packet does "
                "not bind the exact internal functions and dispatch seam to replace, fully "
                "map current versus proposed lambda/component behavior, specify atomic array "
                "failure, or enforce validation-only mutation hooks."
            ),
        },
        "independent_domain_and_regression_audit": {
            "regression_case_count": len(regressions["rows"]),
            "regression_reference_values_present": True,
            "regression_required_input_keys": sorted(regression_required_inputs),
            "regression_observed_common_keys": sorted(regression_input_keys),
            "regression_inputs_complete": regression_inputs_complete,
            "limit_and_boundary_probe_rows_present": isinstance(exact_limit_rows, list),
            "limit_and_boundary_probes_numeric": limits_numeric,
            "runtime_probe_inputs_exact": runtime_inputs_exact,
            "canonical_serialization_schema_exact": serialization_exact,
            "finding": (
                "The eight output references are pinned, but their executable geometry and "
                "range inputs are absent. Limit, boundary, and runtime probes do not freeze "
                "exact input rows, and deterministic serialization is not canonically specified."
            ),
        },
        "independent_validation_audit": {
            "energy_references_complete": True,
            "radial_derivative_references_complete": derivative_reference_complete,
            "mutation_count": len(mutation_rows),
            "mutation_routes_complete": mutation_routes_complete,
            "mutation_detection_predicates_numeric": mutation_predicates_numeric,
            "candidate_oracle_import_forbidden": validation["candidate_may_import_accepted_oracle_evaluator"] is False,
            "candidate_cubature_import_forbidden": validation["candidate_may_import_old_cubature_helper"] is False,
            "finding": (
                "The packet proposes replacing both energy and dU/dD, but freezes independent "
                "references only for energy. The twelve mutation rows name defects without "
                "binding cases, components, injection points, execution order, tolerances or "
                "required exceptions, so their future outcomes are not reproducible."
            ),
        },
        "review_gates": {
            "gate_count": len(gate_rows),
            "pass_count": sum(row["status"] == "PASS" for row in gate_rows),
            "failure_count": len(failed),
            "failed_gate_ids": failed,
            "rows": gate_rows,
        },
        "required_next_action": {
            "fresh_selector_required": True,
            "silent_packet_repair": "PROHIBITED",
            "automatic_packet_v1": "PROHIBITED",
            "shadow_implementation": "NOT_AUTHORIZED",
            "bounded_selector_options": [
                "ONE_NARROW_PRE_IMPLEMENTATION_CONTRACT_REPAIR_IF_FRESHLY_SELECTED",
                "SPLIT_ENERGY_AND_RADIAL_DERIVATIVE_QUALIFICATION",
                "DEFER_OR_CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
            ],
        },
        "scope": review_scope,
        "claim_ceiling": (
            "This review accepts the packet's formulas, stable evaluator regimes, source "
            "custody, architecture distinction, and firewalls, but finds the interface and "
            "future validation contract non-executable in eleven decision-bearing places. "
            "It does not repair the packet, create or execute a candidate, call or adjudicate "
            "cubature, change production code, compute torque, DFT, vector, Jacobian, SVD, "
            "identifiability, rerun Stage A, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the analytic sphere-kernel replacement packet V0."
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
            print("analytic sphere-kernel replacement review already current")
        return 0
    if current != expected:
        print("analytic sphere-kernel replacement review drift")
        return 1
    report = build_report()
    print(
        "analytic sphere-kernel replacement review OK "
        f"verdict={report['verdict']} pass={report['review_gates']['pass_count']} "
        f"fail={report['review_gates']['failure_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
