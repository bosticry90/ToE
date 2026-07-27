from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_"
    "20260718_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_"
    "REVIEW_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_"
    "REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_scalar_only_quadratic_gravity_viability_and_native_relevance_"
    "packet_review_v0.py"
)
TARGET = "review_scalar_only_quadratic_gravity_viability_and_native_relevance_packet_v0_result"
VERDICT = "ACCEPTED_SCALAR_ONLY_VIABILITY_CONTRACT_READY_FOR_ONE_BOUNDED_EXECUTION"
PRINCIPAL_OUTCOME = "SCALAR_ONLY_VIABILITY_CONTRACT_READY"
SELECTED_NEXT_TARGET = (
    "execute_scalar_only_quadratic_gravity_viability_and_native_relevance_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "ONE_BOUNDED_SCALAR_ONLY_COMPARISON_EXECUTION_THEN_INDEPENDENT_RESULT_REVIEW"
)
RESULT_REVIEW_TARGET = (
    "review_scalar_only_quadratic_gravity_viability_and_native_relevance_v0_result"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_20260718_v0.md":
        "ca94cb6483d60e987da5ad9edd4a7c1dd1dd94bb9e6b33f30b16847b160bb23f",
    "formal/docs/release/SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_20260718_v0.json":
        "70fa95ee3e09679d51e003034f925ad6ddbd963f69fd792cc53143cb446ee9fb",
    "formal/python/tools/scalar_only_quadratic_gravity_viability_and_native_relevance_packet_v0.py":
        "903fb5d179dbae55c655ade29a6dee7306e3f7399c912c1d417ca11909fde7d8",
    "formal/python/tests/test_scalar_only_quadratic_gravity_viability_and_native_relevance_packet_v0.py":
        "c3f7c018d7982cc24f3131c77f0e70a2e94ae59d6708531b20136db1d94465d0",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyQuadraticGravityViabilityAndNativeRelevancePacketV0.lean":
        "ee94b53c7afef616eb3abeaa6aec994a91b342615e76992ab20eea1983db6eed",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_packet() -> dict[str, Any]:
    value = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("scalar-only packet must be a JSON object")
    return value


def _validate_packet() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"scalar-only packet custody drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    packet = _load_packet()
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("scalar-only packet is not pending independent review")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("scalar-only packet did not rotate to this review")
    if packet["scope"].get("scientific_execution_authorized") is not False:
        raise ValueError("prepared scalar-only packet improperly authorized execution")
    return custody, packet


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "PASS" if passed else "FAIL",
        "finding": finding,
    }


def _convention_translation_audit(packet: dict[str, Any]) -> dict[str, Any]:
    accepted = packet["accepted_input"]
    return {
        "packet_metric_signature": "(+,-,-,-)",
        "literature_metric_signature": "(-,+,+,+)_WALD_STYLE_REFERENCE",
        "Riemann_one_up_convention_relation": "SAME_DERIVATIVE_ORDERING",
        "metric_map": "g_literature=-g_packet",
        "Levi_Civita_connection_map": "Gamma_literature=Gamma_packet",
        "lower_Ricci_map": "Ricci_literature=Ricci_packet",
        "Ricci_scalar_map": "R_literature=-R_packet",
        "whole_equation_overall_sign_map": "MULTIPLY_TOTAL_PACKET_ACTION_BY_MINUS_ONE",
        "quadratic_coupling_map": "alpha_literature=-alpha_packet",
        "literature_f_RR": "2 alpha_literature=-2 alpha_packet",
        "literature_matter_stability_condition": "f_RR_literature>0",
        "translated_packet_condition": "alpha_packet<0",
        "packet_scalar_mass_squared": accepted["scalar_mass_squared"],
        "packet_non_tachyonic_condition": "alpha_packet<0",
        "sign_tension_resolved": (
            accepted["scalar_mass_squared"] == "-1/(6 alpha)"
            and accepted["non_tachyonic_scalar_stratum"].startswith("alpha<0")
        ),
        "binding_rule": (
            "Every literature comparison must record signature, Riemann/Ricci, "
            "Box, total-action/source sign, curvature-variable, and alpha/f_RR "
            "translations before importing a stability inequality."
        ),
    }


def _constant_curvature_audit() -> dict[str, Any]:
    return {
        "model": "f(R)=R+alpha R^2",
        "vacuum_constant_curvature_equation": "f_R(R0) R0-2 f(R0)=0",
        "f_R_R0": "1+2 alpha R0",
        "expanded_left_hand_side": (
            "(1+2 alpha R0)R0-2(R0+alpha R0^2)=-R0"
        ),
        "solution_set": ["R0=0"],
        "nonzero_vacuum_de_Sitter_or_anti_de_Sitter_admitted": False,
        "cosmological_constant_added": False,
        "background_existence_gate_passed": True,
        "stability_analysis_executed": False,
        "binding_rule": (
            "Treat the constant-curvature vacuum row as an existence/no-nonzero-root "
            "control. A non-Minkowski stability test requires an explicitly supplied "
            "matter-supported background or a fresh action target."
        ),
    }


def _matter_background_rule() -> dict[str, Any]:
    return {
        "primary_source_status": "EXTERNALLY_SUPPLIED_COMPARISON_SOURCE",
        "flat_source_conservation": "partial_mu T^mu_nu=0",
        "curved_background_source_requirements": [
            "EXPLICITLY_SUPPLIED_MATTER_OR_SOURCE_MODEL",
            "BACKGROUND_COVARIANT_CONSERVATION",
            "ON_SHELL_OR_OFF_SHELL_STATUS",
            "JORDAN_OR_EINSTEIN_FRAME_TRACE_DEFINITION",
            "BACKGROUND_EXISTENCE_SOLUTION",
        ],
        "requirements_satisfied_now": False,
        "matter_supported_analysis_executed": False,
        "fail_closed_outcome_if_missing": "BLOCKED_MATTER_TRACE_COUPLING_UNDEFINED",
        "toe_matter_action_inferred": False,
    }


def _review_gates(
    packet: dict[str, Any],
    convention: dict[str, Any],
    constant_curvature: dict[str, Any],
    matter_rule: dict[str, Any],
) -> list[dict[str, Any]]:
    branch = packet["comparison_branch"]
    domain = packet["parameter_domain"]
    scalar_tensor = packet["scalar_tensor_equivalence"]
    matter = packet["matter_trace_contract"]
    backgrounds = packet["background_contract"]
    screening = packet["screening_contract"]
    observable = packet["observable_channel_map"]
    native = packet["native_relevance_contract"]
    packages = packet["work_packages"]
    questions = packet["decision_questions"]
    outcomes = packet["outcome_contract"]
    scope = packet["scope"]
    strata_ids = {row["stratum_id"] for row in domain["rows"]}
    scalar_ids = {row["obligation_id"] for row in scalar_tensor["rows"]}
    background_ids = {row["background_id"] for row in backgrounds["rows"]}
    return [
        _gate(
            "G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY",
            packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "Five packet artifacts match frozen SHA-256 values and rotate to this review.",
        ),
        _gate(
            "G2_COMPARISON_ONLY_PROVENANCE_IMMUTABLE",
            branch["status"] == "SUPPLIED_QUADRATIC_GRAVITY_COMPARISON_SUBFAMILY"
            and branch["beta_zero_adopted"] is False
            and branch["alpha_selected"] is False
            and branch["toe_native"] is False,
            "beta=0 remains a supplied comparison restriction; alpha and the branch remain unselected.",
        ),
        _gate(
            "G3_SIX_PARAMETER_STRATA_DISJOINT_AND_UNSELECTED",
            domain["stratum_count"] == 6
            and len(strata_ids) == 6
            and {"FINITE_NON_TACHYONIC_SCALAR", "EINSTEIN_COMPARISON_LIMIT", "TACHYONIC_SCALAR", "INFINITE_MASS_DECOUPLING_PATH", "VERY_LIGHT_FINITE_SCALAR", "MASSLESS_OR_SINGULAR_LIMIT"} == strata_ids
            and domain["numerical_alpha_selected"] is False,
            "Finite signs, the Einstein point, decoupling, light-scalar, and singular limits remain separate.",
        ),
        _gate(
            "G4_EIGHT_SCALAR_TENSOR_OBLIGATIONS_UNEXECUTED",
            scalar_tensor["obligation_count"] == 8
            and scalar_tensor["derived_count"] == 0
            and all(row["status"] == "TO_BE_DERIVED" for row in scalar_tensor["rows"]),
            "No auxiliary-field, Jordan-frame, Einstein-frame, potential, normalization, or matter-map result is preloaded.",
        ),
        _gate(
            "G5_INVERTIBILITY_CONFORMAL_AND_SINGULAR_DOMAINS_REQUIRED",
            {"AUXILIARY_EQUATION_AND_EQUIVALENCE_DOMAIN", "LEGENDRE_VARIABLE_AND_INVERTIBILITY", "CONFORMAL_MAP_AND_DOMAIN"}.issubset(scalar_ids)
            and scalar_tensor["frame_transform_empirical_equivalence_preclaimed"] is False,
            "The future derivation must state alpha!=0, Legendre invertibility, effective-coupling sign, conformal domain, and singular surfaces.",
        ),
        _gate(
            "G6_ALPHA_F_RR_CONVENTION_TRANSLATION_RESOLVED",
            convention["sign_tension_resolved"] is True
            and convention["quadratic_coupling_map"] == "alpha_literature=-alpha_packet"
            and convention["literature_f_RR"] == "2 alpha_literature=-2 alpha_packet"
            and convention["translated_packet_condition"] == "alpha_packet<0",
            "The literature f_RR>0 condition and packet m0^2>0 condition agree after the complete signature/action map.",
        ),
        _gate(
            "G7_CONSTANT_CURVATURE_EXISTENCE_BEFORE_STABILITY",
            "CONSTANT_CURVATURE_VACUUM" in background_ids
            and constant_curvature["solution_set"] == ["R0=0"]
            and constant_curvature["nonzero_vacuum_de_Sitter_or_anti_de_Sitter_admitted"] is False
            and constant_curvature["stability_analysis_executed"] is False,
            "The pure branch has no nonzero vacuum constant-curvature root; no de Sitter/anti-de Sitter stability result is inferred.",
        ),
        _gate(
            "G8_MATTER_SUPPORTED_BACKGROUND_FAILS_CLOSED",
            "SIMPLE_MATTER_SUPPORTED_BACKGROUND" in background_ids
            and matter_rule["requirements_satisfied_now"] is False
            and matter_rule["fail_closed_outcome_if_missing"] == "BLOCKED_MATTER_TRACE_COUPLING_UNDEFINED",
            "A non-Minkowski test may proceed only after a controlled supplied background source is frozen.",
        ),
        _gate(
            "G9_FIVE_STABILITY_NOTIONS_CANNOT_SUBSTITUTE",
            backgrounds["background_count"] == 3
            and backgrounds["analyzed_count"] == 0
            and len(backgrounds["stability_notions"]) == 5
            and backgrounds["stability_notions_interchangeable"] is False,
            "Existence, kinetic sign, tachyon absence, matter stability, and runaway timescale remain distinct.",
        ),
        _gate(
            "G10_MATTER_TRACE_REMAINS_SUPPLIED_AND_DERIVATION_BOUND",
            matter["source_status"] == "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE"
            and matter["trace_coupling_status"] == "TO_BE_DERIVED"
            and matter["toe_matter_action_claimed"] is False
            and matter_rule["toe_matter_action_inferred"] is False,
            "The future execution must state conservation, shell status, frame, and exact trace coupling without manufacturing ToE matter.",
        ),
        _gate(
            "G11_FINITE_MASS_IS_NOT_SCREENING",
            screening["screening_mechanism_claimed"] is False
            and screening["screening_model_to_be_built"] is False
            and "FINITE_MASS_SUPPRESSION_ONLY" in screening["allowed_future_findings"],
            "Yukawa suppression and nonlinear environmental screening remain different findings.",
        ),
        _gate(
            "G12_00_0I_MAP_REMAINS_LINEAR_STATIONARY_ONLY",
            observable["static_mass_or_trace_channel"].startswith("DIRECTLY_SENSITIVE")
            and observable["stationary_conserved_current_channel"].startswith("NO_DIRECT_SCALAR_CONTRIBUTION")
            and observable["empirical_analysis_authorized"] is False
            and observable["metric_to_orbit_transport_authorized"] is False,
            "No claim about nonlinear rotating systems, orbital observables, or data is licensed.",
        ),
        _gate(
            "G13_SEVEN_FIELD_NATIVE_BRIDGE_FIREWALL",
            native["bridge_identified_count"] == 0
            and len(native["required_bridge_fields"]) == 7
            and native["all_bridge_fields_required"] is True
            and native["resemblance_or_shared_name_sufficient"] is False
            and native["candidate_outcome_requires_separate_seam_packet"] is True,
            "No project scalar is identified; all seven mathematical fields and a separate seam packet remain mandatory.",
        ),
        _gate(
            "G14_VIABILITY_CANNOT_CREATE_NATIVE_RELEVANCE",
            packet["accepted_input"]["full_viability_established"] is False
            and packet["accepted_input"]["native_relevance_established"] is False
            and outcomes["native_bridge_candidate_is_not_adoption"] is True,
            "Comparison viability and ToE-native relevance remain independent reporting axes.",
        ),
        _gate(
            "G15_SIX_PACKAGES_AND_EIGHT_QUESTIONS_REMAIN_ZERO",
            packages["work_package_count"] == 6
            and packages["executed_count"] == 0
            and questions["question_count"] == 8
            and questions["answered_count"] == 0,
            "The packet is prepared but no scientific work package or decision question has been executed.",
        ),
        _gate(
            "G16_TWO_STAGE_OUTCOMES_EXCLUSIVE",
            set(outcomes["packet_review_outcomes"]).isdisjoint(outcomes["future_execution_outcomes"])
            and outcomes["packet_review_outcome_now"] is None
            and outcomes["future_execution_outcome_now"] is None,
            "This review issues the packet outcome only; future scientific outcomes remain unavailable.",
        ),
        _gate(
            "G17_ONE_EXECUTION_ONLY_AFTER_ACCEPTANCE",
            packet["review_contract"]["maximum_authority_after_acceptance"] == "ONE_BOUNDED_SCALAR_ONLY_COMPARISON_EXECUTION"
            and scope["scientific_execution_authorized"] is False
            and scope["scientific_execution_executed"] is False,
            "Acceptance can rotate once to execution and then must stop for independent result review.",
        ),
        _gate(
            "G18_NO_ADOPTION_OR_DOWNSTREAM_PROMOTION",
            all(scope[key] is False for key in (
                "beta_zero_adopted", "alpha_sign_or_value_adopted", "scalar_branch_adopted",
                "native_principle_identified", "gravitational_action_selected",
                "empirical_fitting_executed", "metric_to_orbit_transport_executed",
                "frame_dragging_resumed", "master_action_mutated",
            )),
            "No condition, branch, principle, action, fit, orbital result, frame-dragging result, or master-action change is selected.",
        ),
    ]


def build_review() -> dict[str, Any]:
    custody, packet = _validate_packet()
    human_path = REPO_ROOT / HUMAN_REVIEW_RELATIVE_PATH
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not human_path.is_file() or not test_path.is_file():
        raise ValueError("scalar-only review human record or focused test missing")

    convention = _convention_translation_audit(packet)
    constant_curvature = _constant_curvature_audit()
    matter_rule = _matter_background_rule()
    gates = _review_gates(packet, convention, constant_curvature, matter_rule)
    failures = [row["gate_id"] for row in gates if row["status"] != "PASS"]
    if failures:
        raise ValueError(f"scalar-only packet review gate failed: {failures}")

    return {
        "schema_id": "toe.scalar_only_quadratic_gravity_viability_and_native_relevance.packet_review.v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_packet_review_outcome": PRINCIPAL_OUTCOME,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifact_count": len(custody),
            "frozen_packet_artifacts": custody,
            "human_review": {
                "relative_path": HUMAN_REVIEW_RELATIVE_PATH,
                "sha256": _sha256(human_path),
            },
            "generator": {
                "relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(Path(__file__).resolve()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path),
            },
        },
        "independent_convention_translation_audit": convention,
        "independent_constant_curvature_audit": constant_curvature,
        "binding_matter_supported_background_rule": matter_rule,
        "binding_execution_rules": [
            "Complete and record the convention translation before every literature stability comparison.",
            "Treat R0=0 as the only vacuum constant-curvature solution of the frozen pure branch.",
            "Do not call a background non-Minkowski unless it solves the frozen sourced equations.",
            "Freeze an explicitly supplied covariantly conserved background source or fail closed.",
            "Derive all eight scalar-tensor obligations under the frozen conventions.",
            "Keep background existence, kinetic sign, tachyon absence, matter stability, and runaway timescale separate.",
            "Derive trace coupling and state shell and frame status; infer no ToE matter action.",
            "Distinguish finite-mass Yukawa suppression from nonlinear environmental screening.",
            "Keep the accepted 00/0i map within linear stationary conserved-source scope.",
            "Require all seven bridge fields and a separate seam packet for any native bridge candidate.",
            "Report comparison viability and native relevance as independent axes.",
            f"Stop at {RESULT_REVIEW_TARGET} after one execution or a localized block.",
        ],
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(row["status"] == "PASS" for row in gates),
            "failure_count": sum(row["status"] != "PASS" for row in gates),
            "rows": gates,
        },
        "authorized_execution": {
            "execution_count": 1,
            "work_package_count": 6,
            "executed_work_package_count_now": 0,
            "decision_question_count": 8,
            "answered_decision_question_count_now": 0,
            "scalar_tensor_obligation_count": 8,
            "derived_scalar_tensor_obligation_count_now": 0,
            "background_count_cap": 3,
            "backgrounds_analyzed_now": 0,
            "native_bridge_identified_count_now": 0,
            "result_review_target": RESULT_REVIEW_TARGET,
        },
        "scientific_oracle_spot_checks": [
            {"source": "https://arxiv.org/abs/0805.1726", "role": "POST_DERIVATION_SCALAR_TENSOR_EQUIVALENCE_AND_DOMAIN_ORACLE"},
            {"source": "https://arxiv.org/abs/astro-ph/0610734", "role": "POST_TRANSLATION_MATTER_STABILITY_ORACLE"},
            {"source": "https://arxiv.org/abs/gr-qc/0703044", "role": "BACKGROUND_EXISTENCE_THEN_CONSTANT_CURVATURE_STABILITY_ORACLE"},
            {"source": "https://arxiv.org/abs/1002.4928", "role": "FINITE_MASS_VERSUS_MODEL_DEPENDENT_SCREENING_ORACLE"},
        ],
        "scope": {
            "independent_packet_review_executed": True,
            "packet_accepted": True,
            "one_scalar_only_execution_authorized": True,
            "scientific_execution_executed": False,
            "work_package_executed": False,
            "decision_question_answered": False,
            "scalar_tensor_derivation_executed": False,
            "background_stability_analysis_executed": False,
            "matter_trace_coupling_derived": False,
            "screening_mechanism_identified": False,
            "empirical_constraint_derived": False,
            "native_scalar_bridge_identified": False,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "metric_to_orbit_transport_authorized": False,
            "frame_dragging_reopened": False,
            "master_action_mutation_authorized": False,
        },
        "current_posture": {
            "packet_review": "ACCEPTED_18_OF_18_GATES",
            "principal_outcome": PRINCIPAL_OUTCOME,
            "authorized_executions": 1,
            "work_packages_executed": "0_OF_6",
            "decision_questions_answered": "0_OF_8",
            "scalar_tensor_obligations_derived": "0_OF_8",
            "backgrounds_analyzed": "0_OF_3",
            "native_scalar_bridges": 0,
            "beta_zero": "NOT_ADOPTED",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "The packet contract is accepted for one supplied scalar-only comparison "
            "execution with binding convention, background-existence, source, stability, "
            "screening, observable, and native-bridge rules. No viability result, native "
            "bridge, beta or alpha condition, scalar branch, gravitational principle, "
            "gravitational action, matter sector, empirical result, orbital transport, "
            "frame-dragging result, or master-action change is established or adopted."
        ),
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
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("scalar-only packet review is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "authorized_executions": report["authorized_execution"]["execution_count"],
            "gates": report["review_gates"]["pass_count"],
            "outcome": report["principal_packet_review_outcome"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
