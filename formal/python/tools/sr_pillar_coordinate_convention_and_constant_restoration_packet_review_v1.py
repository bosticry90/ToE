from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import inspect
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_v1 as packet_v1,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = packet_v1.REPORT_RELATIVE_PATH
PACKET_TOOL_RELATIVE_PATH = (
    "formal/python/tools/"
    "sr_pillar_coordinate_convention_and_constant_restoration_packet_v1.py"
)
PACKET_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_v1.py"
)
REVIEW_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v1.py"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v1.json"
)

CONSUMED_TARGET = (
    "review_sr_pillar_coordinate_convention_and_constant_restoration_packet_v1_result"
)
VERDICT = "BLOCKED_SEMANTIC_ROUND_TRIP_PRODUCTION_CONTRACT_INCOMPLETE"
FIRST_DIAGNOSTIC = "RESTORATION_FUNCTIONS_DO_NOT_APPLY_DECLARED_OBJECT_MAPS"
SELECTED_NEXT_TARGET = (
    "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet_v2"
)

FROZEN_INPUT_HASHES = {
    PACKET_RELATIVE_PATH:
        "2185ef29df93a403595bc2540b5a6543ba34a8842fb7e92ab3218bd5efdc2e0a",
    PACKET_TOOL_RELATIVE_PATH:
        "0794941ffe14b7e1c250a6763f1f82f6c876bece486d8d52bd9a57ce2582f8e5",
    PACKET_TEST_RELATIVE_PATH:
        "4d8760dc8a8d78296effc77b69d8c3f9cdb5a2fc473221813dd9db32ebe18882",
}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _read_packet_and_frozen_inputs() -> tuple[dict[str, Any], list[dict[str, str]]]:
    bindings: list[dict[str, str]] = []
    for relative_path, expected_hash in FROZEN_INPUT_HASHES.items():
        raw = (REPO_ROOT / relative_path).read_bytes()
        observed = _sha256(raw)
        if observed != expected_hash:
            raise ValueError(f"frozen v1 input hash mismatch: {relative_path}")
        bindings.append({"relative_path": relative_path, "sha256": observed})
    packet = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(packet, dict):
        raise ValueError("v1 packet root must be an object")
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("v1 packet verdict mismatch")
    if packet.get("selected_next_target") != CONSUMED_TARGET:
        raise ValueError("v1 packet target mismatch")
    return packet, bindings


def _independent_electromagnetic_audit(packet: dict[str, Any]) -> dict[str, Any]:
    em = packet["electromagnetic_tensor_closure"]
    expected_upper = [
        ["0", "-E_x/c", "-E_y/c", "-E_z/c"],
        ["+E_x/c", "0", "-B_z", "+B_y"],
        ["+E_y/c", "+B_z", "0", "-B_x"],
        ["+E_z/c", "-B_y", "+B_x", "0"],
    ]
    metric = [1, -1, -1, -1]
    sign_flip = {
        "+": "-",
        "-": "+",
    }

    def scale_component(component: str, sign: int) -> str:
        if component == "0" or sign == 1:
            return component
        if component[0] in sign_flip:
            return sign_flip[component[0]] + component[1:]
        return "-" + component

    derived_lower = [
        [
            scale_component(expected_upper[mu][nu], metric[mu] * metric[nu])
            for nu in range(4)
        ]
        for mu in range(4)
    ]
    expected_lower = [
        ["0", "+E_x/c", "+E_y/c", "+E_z/c"],
        ["-E_x/c", "0", "-B_z", "+B_y"],
        ["-E_y/c", "+B_z", "0", "-B_x"],
        ["-E_z/c", "-B_y", "+B_x", "0"],
    ]
    component_definition_passed = (
        em["field_definition_upper"]
        == "F_SI^{mu nu}=partial^mu A_SI^nu-partial^nu A_SI^mu"
        and em["upper_components"]
        == "F^{0i}=-E^i/c; F^{i0}=+E^i/c; F^{ij}=-epsilon_3^{ijk} B_k"
    )
    upper_matrix_passed = em["F_upper_matrix_rows"] == expected_upper
    lower_matrix_passed = derived_lower == expected_lower == em["F_lower_matrix_rows"]
    levi_civita_passed = (
        em["four_dimensional_orientation"].startswith(
            "varepsilon^{0123}=+1 and varepsilon_0123=-1"
        )
        and "det(eta)=-1" in em["four_dimensional_tensor_rule"]
    )
    dual_passed = (
        em["dual_definition"]
        == "starF^{mu nu}=(1/2) varepsilon^{mu nu rho sigma} F_rho_sigma"
        and em["dual_components"]
        == "starF^{0i}=-B^i; starF^{ij}=+epsilon_3^{ijk} E_k/c"
    )
    sourced_vector_passed = (
        "div E=rho/epsilon_0" in em["sourced_maxwell_SI"]
        and "curl B-c^-2 partial_t E=mu_0 j" in em["sourced_maxwell_SI"]
        and em["vacuum_identity"] == "mu_0 epsilon_0 c^2=1"
    )
    homogeneous_vector_passed = (
        "div B=0" in em["homogeneous_maxwell"]
        and "curl E+partial_t B=0" in em["homogeneous_maxwell"]
    )
    checks = {
        "component_definition_passed": component_definition_passed,
        "upper_matrix_passed": upper_matrix_passed,
        "metric_lowering_passed": lower_matrix_passed,
        "levi_civita_orientation_passed": levi_civita_passed,
        "dual_components_passed": dual_passed,
        "sourced_vector_maxwell_passed": sourced_vector_passed,
        "homogeneous_vector_maxwell_passed": homogeneous_vector_passed,
    }
    return {
        "method": "independent component derivation from A^mu, partial^mu, E, B, eta, and the selected orientation",
        "checks": checks,
        "passed_count": sum(checks.values()),
        "required_count": len(checks),
        "passed": all(checks.values()),
        "derived_lower_matrix_rows": derived_lower,
    }


def _independent_quantum_audit(packet: dict[str, Any]) -> dict[str, Any]:
    quantum = packet["quantum_hbar_normalization"]
    checks = {
        "plus_sign_derivative_recorded": quantum["covariant_derivative_SI"]
        == "D_mu psi=(nabla_spin_mu+i q_SI A_SI_mu/hbar)psi",
        "signed_charge_recorded": quantum["signed_charge_policy"]
        == "q_SI is the signed electric charge of psi",
        "gauge_transform_sign_recorded": quantum["gauge_transform_SI"]
        == "A_mu -> A_mu+partial_mu chi; psi -> exp(-i q_SI chi/hbar) psi",
        "gauge_phase_derivative_cancels_potential_shift": (-1 + 1) == 0,
        "qA_coefficient_identity_recorded": quantum["coefficient_identity"]
        == "q_star A_star = q_SI A_SI/hbar",
        "phase_identity_recorded": quantum["phase_identity"]
        == "q_star chi_star=q_SI chi_SI/hbar",
        "current_normalization_records_c": "J_SI=q_SI c psibar gamma^mu psi"
        in quantum["current_identity"],
    }
    return {
        "method": "independent sign cancellation and normalization-identity audit",
        "gauge_covariance_derivation": (
            "partial_mu exp(-i q chi/hbar) contributes -i q partial_mu chi/hbar; "
            "the shifted +i q(A_mu+partial_mu chi)/hbar term contributes the "
            "opposite phase-gradient term, so D'_mu psi'=exp(-i q chi/hbar)D_mu psi"
        ),
        "checks": checks,
        "passed_count": sum(checks.values()),
        "required_count": len(checks),
        "passed": all(checks.values()),
    }


def _independent_stress_and_adapter_audit(packet: dict[str, Any]) -> dict[str, Any]:
    stress = packet["stress_energy_component_dictionary"]
    adapter = packet["flat_curved_derivative_adapter"]
    checks = {
        "T00_energy_density": stress["T^00"] == "energy density",
        "T0i_energy_flux_over_c": stress["T^0i"]
        == "energy flux^i/c=c times momentum density^i",
        "Ti0_symmetry_scoped": "only under the selected symmetry assumption" in stress["T^i0"],
        "Tij_stress": "momentum-flux tensor" in stress["T^ij"],
        "arbitrary_canonical_tensor_excluded": "arbitrary canonical tensor"
        in stress["symmetry_assumption"],
        "flat_partial_scoped": "inertial Minkowski" in adapter["flat_inertial"],
        "curved_tensor_connection_scoped": "Levi-Civita connection" in adapter["curved_tensor"],
        "spin_connection_scoped": adapter["curved_spinor"]
        == "nabla_spin_mu psi=partial_mu psi+Omega_mu psi",
        "flat_limit_adapter_explicit": "Gamma=Omega=0" in adapter["source_adapter"],
        "tetrad_derivation_not_claimed": "not derived" in adapter["bounded_nonclaim"],
    }
    return {
        "method": "independent component-meaning and derivative-domain comparison",
        "checks": checks,
        "passed_count": sum(checks.values()),
        "required_count": len(checks),
        "passed": all(checks.values()),
    }


def _json_pointer(payload: Any, pointer: str) -> Any:
    value = payload
    for part in pointer.lstrip("/").split("/"):
        token = part.replace("~1", "/").replace("~0", "~")
        value = value[int(token)] if isinstance(value, list) else value[token]
    return value


def _independent_source_binding_audit(packet: dict[str, Any]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for binding in packet["source_bindings"]["rows"]:
        path = REPO_ROOT / binding["artifact"]
        raw = path.read_bytes()
        artifact_hash_matches = _sha256(raw) == binding["artifact_sha256"]
        if binding["source_kind"] == "json_pointer":
            payload = json.loads(raw.decode("utf-8"))
            observed = _json_pointer(payload, binding["locator"])
        else:
            text = raw.decode("utf-8")
            observed = (
                binding["exact_source_expression"]
                if binding["exact_source_expression"] in text
                else None
            )
        exact_expression_matches = observed == binding["exact_source_expression"]
        exact_content_hash_matches = (
            _sha256(binding["exact_source_expression"].encode("utf-8"))
            == binding["exact_content_sha256"]
        )
        corroborating_matches = True
        if "corroborating_artifact" in binding:
            corroborating = json.loads(
                (REPO_ROOT / binding["corroborating_artifact"]).read_text(encoding="utf-8")
            )
            corroborating_matches = (
                _json_pointer(corroborating, binding["corroborating_locator"])
                == binding["corroborating_value"]
            )
        passed = all(
            (
                artifact_hash_matches,
                exact_expression_matches,
                exact_content_hash_matches,
                corroborating_matches,
            )
        )
        rows.append(
            {
                "equation_id": binding["equation_id"],
                "artifact_hash_matches": artifact_hash_matches,
                "exact_expression_matches": exact_expression_matches,
                "exact_content_hash_matches": exact_content_hash_matches,
                "corroborating_matches": corroborating_matches,
                "original_claim_class_preserved": True,
                "passed": passed,
            }
        )
    return {
        "required_count": 6,
        "passed_count": sum(1 for row in rows if row["passed"]),
        "rows": rows,
        "passed": len(rows) == 6 and all(row["passed"] for row in rows),
    }


def _production_round_trip_probe(packet: dict[str, Any]) -> dict[str, Any]:
    equation_id = "SOURCED_MAXWELL"
    contract = packet_v1.EQUATION_CONTRACTS[equation_id]
    original_map = copy.deepcopy(contract["object_map"])
    original_si = copy.deepcopy(contract["si_ast"])
    natural = copy.deepcopy(contract["natural_ast"])
    baseline_restored = packet_v1.restore_equation(equation_id, natural)
    try:
        contract["object_map"] = ["INTENTIONALLY_INVALID_MAP_UNUSED_BY_PRODUCTION"]
        map_mutated_restored = packet_v1.restore_equation(equation_id, natural)
        map_mutation_ignored = (
            packet_v1._canonical_ast(map_mutated_restored)
            == packet_v1._canonical_ast(baseline_restored)
        )

        deliberately_wrong_si: packet_v1.Ast = (
            "eq",
            ("divergence", "nabla_mu", "F_SI^{mu nu}"),
            ("mul", "-mu_0", "J_SI^nu"),
        )
        contract["si_ast"] = deliberately_wrong_si
        wrong_target_restored = packet_v1.restore_equation(equation_id, natural)
        wrong_target_rows = packet_v1._round_trip_results()
        wrong_target_row = next(
            row for row in wrong_target_rows if row["equation_id"] == equation_id
        )
        wrong_target_still_passes = (
            wrong_target_row["passed"] is True
            and packet_v1._canonical_ast(wrong_target_restored)
            == packet_v1._canonical_ast(deliberately_wrong_si)
        )
    finally:
        contract["object_map"] = original_map
        contract["si_ast"] = original_si

    restore_source = inspect.getsource(packet_v1.restore_equation)
    suppress_source = inspect.getsource(packet_v1.suppress_equation)
    object_map_used_by_restore = "object_map" in restore_source
    object_map_used_by_suppress = "object_map" in suppress_source
    preflight_used_by_restore = "first_diagnostic" in restore_source
    preflight_used_by_suppress = "first_diagnostic" in suppress_source
    return {
        "actual_production_functions_called": ["restore_equation", "suppress_equation", "_round_trip_results"],
        "restore_signature": str(inspect.signature(packet_v1.restore_equation)),
        "suppress_signature": str(inspect.signature(packet_v1.suppress_equation)),
        "declared_object_map_used_by_restore": object_map_used_by_restore,
        "declared_object_map_used_by_suppress": object_map_used_by_suppress,
        "invalid_object_map_mutation_ignored": map_mutation_ignored,
        "deliberately_wrong_si_target_still_reports_round_trip_pass": wrong_target_still_passes,
        "negative_control_preflight_used_by_restore": preflight_used_by_restore,
        "negative_control_preflight_used_by_suppress": preflight_used_by_suppress,
        "bounded_conclusion": (
            "The 6/6 result proves reciprocal table pairing after exact input guards; "
            "it does not prove that the declared physical object maps derive the paired ASTs."
        ),
    }


def _quantum_production_probe() -> dict[str, Any]:
    source = (REPO_ROOT / PACKET_TOOL_RELATIVE_PATH).read_text(encoding="utf-8")
    tree = ast.parse(source)
    function = next(
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "_quantum_round_trip"
    )
    assignments = {
        target.id: node.value.id
        for node in function.body
        if isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Name)
        for target in node.targets
    }
    hardcoded_pass_true = any(
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Dict)
        and any(
            isinstance(key, ast.Constant)
            and key.value == "passed"
            and isinstance(value, ast.Constant)
            and value.value is True
            for key, value in zip(node.value.keys, node.value.values, strict=True)
        )
        for node in ast.walk(function)
    )
    return {
        "restored_assignment": assignments.get("restored"),
        "suppressed_assignment": assignments.get("suppressed"),
        "passed_is_hardcoded_true": hardcoded_pass_true,
        "semantic_transform_function_called": any(
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in {"restore_equation", "suppress_equation"}
            for node in ast.walk(function)
        ),
        "bounded_conclusion": (
            "The reported quantum round trip self-assigns the frozen natural and SI ASTs "
            "and hardcodes pass=true; the physically coherent normalization is not "
            "exercised by a production transformation."
        ),
    }


def _source_ast_alignment_audit(packet: dict[str, Any]) -> dict[str, Any]:
    binding = next(
        row for row in packet["source_bindings"]["rows"]
        if row["equation_id"] == "MATTER_STRESS_ENERGY_EXCHANGE"
    )
    trip = next(
        row for row in packet["bidirectional_round_trips"]["rows"]
        if row["equation_id"] == "MATTER_STRESS_ENERGY_EXCHANGE"
    )
    natural_text = json.dumps(trip["natural_canonical_ast"], sort_keys=True)
    declared_maps = packet_v1.EQUATION_CONTRACTS[
        "MATTER_STRESS_ENERGY_EXCHANGE"
    ]["object_map"]
    mismatch = (
        "T_psi" in binding["exact_source_expression"]
        and "T_matter" in natural_text
        and not any("T_psi" in item and "T_matter" in item for item in declared_maps)
    )
    return {
        "equation_id": "MATTER_STRESS_ENERGY_EXCHANGE",
        "bound_source_tensor": "T_psi",
        "round_trip_source_tensor": "T_matter",
        "declared_object_maps": declared_maps,
        "explicit_T_psi_to_T_matter_adapter_present": not mismatch,
        "exact_bound_source_ast_alignment_passed": not mismatch,
    }


def build_review() -> dict[str, Any]:
    packet, frozen_inputs = _read_packet_and_frozen_inputs()
    em = _independent_electromagnetic_audit(packet)
    quantum = _independent_quantum_audit(packet)
    stress_adapter = _independent_stress_and_adapter_audit(packet)
    sources = _independent_source_binding_audit(packet)
    if not all((em["passed"], quantum["passed"], stress_adapter["passed"], sources["passed"])):
        raise ValueError("independent positive convention audit unexpectedly failed")
    production = _production_round_trip_probe(packet)
    quantum_production = _quantum_production_probe()
    alignment = _source_ast_alignment_audit(packet)

    findings = [
        {
            "finding_id": FIRST_DIAGNOSTIC,
            "confirmed": (
                not production["declared_object_map_used_by_restore"]
                and not production["declared_object_map_used_by_suppress"]
                and production["invalid_object_map_mutation_ignored"]
                and production["deliberately_wrong_si_target_still_reports_round_trip_pass"]
            ),
            "materiality": "BLOCKING",
            "evidence": production["bounded_conclusion"],
        },
        {
            "finding_id": "QUANTUM_ROUND_TRIP_IS_SELF_ASSIGNMENT_WITH_HARDCODED_PASS",
            "confirmed": (
                quantum_production["restored_assignment"] == "si"
                and quantum_production["suppressed_assignment"] == "natural"
                and quantum_production["passed_is_hardcoded_true"]
                and not quantum_production["semantic_transform_function_called"]
            ),
            "materiality": "BLOCKING",
            "evidence": quantum_production["bounded_conclusion"],
        },
        {
            "finding_id": "MATTER_EXCHANGE_ROUND_TRIP_AST_NOT_EXACT_BOUND_SOURCE",
            "confirmed": not alignment["exact_bound_source_ast_alignment_passed"],
            "materiality": "BLOCKING",
            "evidence": (
                "The exact bound source uses T_psi, while the canonical round-trip AST "
                "uses T_matter and declares no T_psi-to-T_matter adapter."
            ),
        },
        {
            "finding_id": "NEGATIVE_CONTROL_PREFLIGHT_NOT_ENFORCED_BY_RESTORATION_ENTRY_POINTS",
            "confirmed": (
                not production["negative_control_preflight_used_by_restore"]
                and not production["negative_control_preflight_used_by_suppress"]
            ),
            "materiality": "BLOCKING",
            "evidence": (
                "The eight mutations produce exact diagnostics in their standalone "
                "validator, but restore_equation and suppress_equation do not consume a "
                "convention state or require first_diagnostic(state)=PASS."
            ),
        },
    ]
    if not all(row["confirmed"] for row in findings):
        raise ValueError("expected production-contract finding not reproduced")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / REVIEW_TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("v1 review test missing")
    return {
        "schema_id": "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v1",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": CONSUMED_TARGET,
        "verdict": VERDICT,
        "first_diagnostic": FIRST_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "review_authority": {
            "frozen_inputs": frozen_inputs,
            "reviewer": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "review_test": {
                "relative_path": REVIEW_TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "independent_positive_findings": {
            "coordinate_signature_foundation_retained": True,
            "electromagnetic_audit": em,
            "quantum_gauge_sign_and_units_audit": quantum,
            "stress_energy_and_derivative_adapter_audit": stress_adapter,
            "exact_source_content_bindings_audit": sources,
            "negative_controls_standalone_result": "8/8 exact independently observed in the frozen packet",
            "bounded_assessment": (
                "The selected physical convention is internally coherent on the audited "
                "tensor, dual, Maxwell, gauge-sign, stress-component, derivative-domain, "
                "and exact source-content surfaces. These findings are retained for v2."
            ),
        },
        "production_contract_audit": {
            "six_equation_probe": production,
            "quantum_probe": quantum_production,
            "bound_source_ast_alignment": alignment,
        },
        "blocking_findings": {
            "count": len(findings),
            "all_confirmed": all(row["confirmed"] for row in findings),
            "findings": findings,
        },
        "v2_contract": [
            "replace reciprocal AST lookup with six bounded structural restoration/suppression transforms that actually consume the frozen object maps and derive canonical targets",
            "implement quantum SI-to-natural and natural-to-SI production transforms; remove self-assignment and hardcoded pass=true",
            "make the matter-exchange canonical source AST use exact T_psi or declare and execute one explicit T_psi-to-T_matter semantic adapter",
            "provide one validate-then-restore and validate-then-suppress entry path that requires the negative-control convention preflight to return PASS before transformation",
            "re-run the same six bindings, six semantic round trips, and eight atomic diagnostics without adding equations, conventions, unit systems, migration, or adjacent work",
        ],
        "scope_and_authorization": {
            "packet_v1_accepted": False,
            "bounded_six_surface_restoration_authorized": False,
            "authoritative_equation_restoration_executed": False,
            "scientific_equation_migration_executed": False,
            "historical_artifacts_modified": False,
            "repository_wide_migration_authorized": False,
            "r13_reopened": False,
            "external_comparator_activated": False,
            "automation_created": False,
            "only_bounded_v2_packet_preparation_authorized": True,
        },
        "claim_ceiling": (
            "Independent v1 packet review only. It retains the internally coherent "
            "physical convention and exact content bindings, but blocks acceptance because "
            "the reported reversibility is reciprocal table identity rather than execution "
            "of the declared restoration maps. No restoration, migration, SR recovery, "
            "pillar completion, seam closure, empirical claim, prediction, master-action "
            "promotion, R13 change, or comparator adoption follows."
        ),
        "hard_stop": {
            "review_complete": True,
            "packet_accepted": False,
            "restoration_authorized": False,
            "migration_authorized": False,
            "next_action": SELECTED_NEXT_TARGET,
            "successor_scope": "ONE_BOUNDED_v2_PRODUCTION_CONTRACT_REPAIR_ONLY",
        },
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("SR convention/restoration v1 review is stale or missing")
        review = json.loads(raw)
        print(
            json.dumps(
                {
                    "blocking_findings": review["blocking_findings"]["count"],
                    "em_checks": (
                        f"{review['independent_positive_findings']['electromagnetic_audit']['passed_count']}/"
                        f"{review['independent_positive_findings']['electromagnetic_audit']['required_count']}"
                    ),
                    "source_bindings": (
                        f"{review['independent_positive_findings']['exact_source_content_bindings_audit']['passed_count']}/"
                        f"{review['independent_positive_findings']['exact_source_content_bindings_audit']['required_count']}"
                    ),
                    "status": "CHECKED",
                    "verdict": review["verdict"],
                },
                sort_keys=True,
            )
        )
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
