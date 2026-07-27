from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_"
    "20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_scalar_only_quadratic_gravity_viability_and_native_relevance_packet_v0.py"
)
TARGET = "prepare_scalar_only_quadratic_gravity_viability_and_native_relevance_packet_v0"
VERDICT = "PREPARED_PENDING_INDEPENDENT_REVIEW"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_quadratic_gravity_viability_and_native_relevance_"
    "packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_SCALAR_ONLY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_REVIEW_ONLY"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/POST_QUADRATIC_GRAVITY_CONDITIONAL_MODE_SELECTION_ENVELOPE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md":
        "370550b372a911bdcc44723403b3ca819b60d7612ea07012fed4336bc3a3fd20",
    "formal/docs/release/POST_QUADRATIC_GRAVITY_CONDITIONAL_MODE_SELECTION_ENVELOPE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json":
        "cdb23e4c929cfa15fa143cd8f8df08652b5d6111d68120d1e576f66719f70262",
    "formal/python/tools/post_quadratic_gravity_conditional_mode_selection_envelope_scientific_response_selection_v0.py":
        "1940fd3e6a6b0ef8eedac86d97cb99366e67cb6b714702344b323720eb5e9c79",
    "formal/python/tests/test_post_quadratic_gravity_conditional_mode_selection_envelope_scientific_response_selection_v0.py":
        "d3b4f1ff1743bc66724a715d76e1dd27bee75ad5832d9e6e70a905f9e78526f3",
    "formal/toe_formal/ToeFormal/Derivation/PostQuadraticGravityConditionalModeSelectionEnvelopeScientificResponseSelectionV0.lean":
        "344724d0b208e052754d77b08442389b4e20efd8f51516b80f009dfd7f7f3d1d",
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_RESULT_REVIEW_20260718_v0.json":
        "69f59eba7c17f102a539e43b3155905772bad84dc2794a8d1a85129d112ba925",
    "formal/docs/release/TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_RESULT_REVIEW_20260618_v0.json":
        "4553c2aba75a81982088d4f095ebf3c4a681b0cff84f34e743dbf605fdd25533",
    "formal/docs/release/TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_20260618_v0.json":
        "5aa84d6daf3d50e9a46eb96b635ad77e90770cca1b62a2b20bcb8d8f077000ae",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json":
        "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    "formal/docs/release/PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_20260619_v0.json":
        "d1ed87df8e76bbe4e216a307d620f8131692760b106516a3567cac1f7bdbb437",
}

PACKET_REVIEW_OUTCOMES = (
    "SCALAR_ONLY_VIABILITY_CONTRACT_READY",
    "BLOCKED_BACKGROUND_STABILITY_CONTRACT",
    "BLOCKED_MATTER_TRACE_COUPLING_UNDEFINED",
    "BLOCKED_SCOPE_OR_NATIVE_FIREWALL",
)
FUTURE_EXECUTION_OUTCOMES = (
    "SCALAR_BRANCH_COMPARISON_VIABLE_NATIVE_RELEVANCE_UNESTABLISHED",
    "SCALAR_BRANCH_VIABILITY_OBSTRUCTED",
    "NATIVE_SCALAR_BRIDGE_CANDIDATE_IDENTIFIED",
    "SCALAR_BRANCH_ASSESSMENT_INCONCLUSIVE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in AUTHORITY_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"scalar-only packet authority drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})

    selection = _load_json(
        "formal/docs/release/POST_QUADRATIC_GRAVITY_CONDITIONAL_MODE_SELECTION_"
        "ENVELOPE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
    )
    if selection.get("verdict") != (
        "SELECTED_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_"
        "RELEVANCE_PACKET_PREPARATION"
    ):
        raise ValueError("scalar-only response selection verdict mismatch")
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("response selection did not authorize this packet")
    if selection.get("selected_candidate_id") != (
        "SCALAR_ONLY_VIABILITY_AND_NATIVE_RELEVANCE"
    ):
        raise ValueError("scalar-only response candidate mismatch")

    comparison = _load_json(
        "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
        "SPECTRUM_COMPARISON_RESULT_REVIEW_20260718_v0.json"
    )
    if comparison.get("verdict") != (
        "ACCEPTED_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_COMPARISON_RESULT"
    ):
        raise ValueError("accepted quadratic comparison result missing")

    phi = _load_json(
        "formal/docs/release/TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_"
        "POLICY_RESULT_REVIEW_20260618_v0.json"
    )
    if not phi.get("native_generation_blocked"):
        raise ValueError("native phi generation is no longer blocked")
    if phi.get("phi_variation_derived_as_toe_native") is not False:
        raise ValueError("phi variation unexpectedly native")
    if phi.get("phi_stress_energy_derived_as_toe_native") is not False:
        raise ValueError("phi stress energy unexpectedly native")

    phi_ck = _load_json(
        "formal/docs/release/TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_"
        "20260618_v0.json"
    )
    if phi_ck.get("ck_variational_content_blocked") is not True:
        raise ValueError("phi/Ck variational block unexpectedly removed")

    scalar_source = _load_json(
        "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_"
        "PACKET_RESULT_REVIEW_20260618_v0.json"
    )
    if scalar_source.get("provisional_classical_sandbox_route_only") is not True:
        raise ValueError("scalar-source route is no longer provisional")
    if scalar_source.get("toe_native_matter_derivation_claimed") is not False:
        raise ValueError("scalar source unexpectedly became native matter")

    rule_family = _load_json(
        "formal/docs/release/PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_"
        "SYNTHESIS_RESULT_REVIEW_20260619_v0.json"
    )
    for key in (
        "all_three_rules_admissibility_only",
        "all_three_rules_not_dynamical_laws",
        "none_of_three_rules_derives_phi",
        "none_of_three_rules_derives_v_phi",
    ):
        if rule_family.get(key) is not True:
            raise ValueError(f"phi/Ck rule-family boundary drift: {key}")
    return custody, selection


def _parameter_strata() -> list[dict[str, Any]]:
    return [
        {
            "stratum_id": "FINITE_NON_TACHYONIC_SCALAR",
            "condition": "alpha<0",
            "mass_statement": "m0_squared=-1/(6 alpha)>0 under frozen conventions",
            "status": "TO_BE_TESTED_BEYOND_ACCEPTED_MINKOWSKI_LINEARIZATION",
            "qualification": "non-tachyonic is not full viability",
        },
        {
            "stratum_id": "EINSTEIN_COMPARISON_LIMIT",
            "condition": "alpha=0",
            "mass_statement": "scalar pole absent in the finite-parameter action",
            "status": "ACCEPTED_COMPARISON_LIMIT_ONLY",
            "qualification": "not a ToE action selection",
        },
        {
            "stratum_id": "TACHYONIC_SCALAR",
            "condition": "alpha>0",
            "mass_statement": "m0_squared<0 under frozen conventions",
            "status": "BOUNDED_LINEARIZED_OBSTRUCTION_TO_BE_RETAINED",
            "qualification": "does not generalize outside the frozen conventions",
        },
        {
            "stratum_id": "INFINITE_MASS_DECOUPLING_PATH",
            "condition": "alpha approaches 0 from below",
            "mass_statement": "m0_squared tends to positive infinity",
            "status": "LIMIT_CONTROL_TO_BE_DERIVED",
            "qualification": "limit is not ordinary substitution into a singular formula",
        },
        {
            "stratum_id": "VERY_LIGHT_FINITE_SCALAR",
            "condition": "finite alpha<0 with abs(m0) small on the tested scale",
            "mass_statement": "long-range trace response may be exposed",
            "status": "NO_EMPIRICAL_BOUND_OR_VALUE_SELECTED",
            "qualification": "requires declared scale source and future data authority",
        },
        {
            "stratum_id": "MASSLESS_OR_SINGULAR_LIMIT",
            "condition": "unbounded-coupling or operator-rank-changing limit",
            "mass_statement": "not established by the accepted finite-alpha formulas",
            "status": "FRESH_DOMAIN_AND_DERIVATION_REQUIRED",
            "qualification": "no automatic transport from the generic stratum",
        },
    ]


def _scalar_tensor_obligations() -> list[dict[str, Any]]:
    names = [
        ("AUXILIARY_FIELD_INTRODUCTION", "introduce an auxiliary curvature variable without assuming equivalence"),
        ("AUXILIARY_EQUATION_AND_EQUIVALENCE_DOMAIN", "vary the auxiliary field and prove the exact domain of equivalence"),
        ("LEGENDRE_VARIABLE_AND_INVERTIBILITY", "define the Legendre variable and establish invertibility conditions"),
        ("JORDAN_FRAME_ACTION_AND_POTENTIAL", "derive the Jordan-frame scalar-tensor action and potential"),
        ("CONFORMAL_MAP_AND_DOMAIN", "derive the conformal transformation and its sign/domain restrictions"),
        ("CANONICAL_SCALAR_NORMALIZATION", "derive the scalar normalization under the frozen signature and units"),
        ("EINSTEIN_FRAME_POTENTIAL", "derive the Einstein-frame potential without importing a convention-mismatched formula"),
        ("MATTER_TRANSFORMATION_AND_OBSERVABLE_CAVEAT", "derive matter coupling in both frames and state the observable-identification caveat"),
    ]
    return [
        {
            "obligation_id": obligation_id,
            "obligation": obligation,
            "status": "TO_BE_DERIVED",
            "literature_formula_may_replace_derivation": False,
        }
        for obligation_id, obligation in names
    ]


def _backgrounds() -> list[dict[str, Any]]:
    return [
        {
            "background_id": "MINKOWSKI_CONTROL",
            "role": "reproduce the accepted linear scalar pole and residue as a shared-path control",
            "existence_gate": "ALREADY_ACCEPTED_FOR_THE_COMPARISON_ACTION",
            "analysis_status": "NOT_EXECUTED_IN_THIS_PACKET",
        },
        {
            "background_id": "CONSTANT_CURVATURE_VACUUM",
            "role": "derive the algebraic background condition before perturbing",
            "existence_gate": "TO_BE_DERIVED_WITHOUT_ADDING_A_COSMOLOGICAL_TERM",
            "analysis_status": "NOT_EXECUTED",
        },
        {
            "background_id": "SIMPLE_MATTER_SUPPORTED_BACKGROUND",
            "role": "test bounded matter stability only if a supplied source model is explicitly frozen",
            "existence_gate": "BLOCK_IF_NO_CONTROLLED_SUPPLIED_MATTER_MODEL",
            "analysis_status": "NOT_EXECUTED",
        },
    ]


def _work_packages() -> list[dict[str, Any]]:
    rows = [
        ("WP_SCALAR_TENSOR_EQUIVALENCE", "derive the local scalar-tensor representation and domains"),
        ("WP_BACKGROUND_STABILITY", "test background existence and distinct stability notions on at most three backgrounds"),
        ("WP_TRACE_COUPLING", "derive which supplied source trace excites the scalar"),
        ("WP_SCREENING_AND_NONLINEAR_RELEVANCE", "test whether suppression beyond finite mass exists in the pure branch"),
        ("WP_OBSERVABLE_CHANNEL_MAP", "retain and delimit the accepted 00/0i channel comparison"),
        ("WP_NATIVE_BRIDGE_AUDIT", "test project scalar surfaces against the seven-field bridge contract"),
    ]
    return [
        {"work_package_id": package_id, "obligation": obligation, "status": "NOT_EXECUTED"}
        for package_id, obligation in rows
    ]


def _decision_questions() -> list[dict[str, Any]]:
    questions = [
        "Does the scalar-only branch have a healthy isolated linearized scalar over a nonempty parameter domain?",
        "Does the scalar remain stable on one bounded non-Minkowski background?",
        "What exact supplied source trace excites the scalar?",
        "Does the pure branch contain suppression beyond simple finite mass?",
        "Which theoretical or observational limit would most strongly constrain its range?",
        "Can any accepted ToE-native object be identified with the scalar without inventing a bridge?",
        "Does the branch add explanatory or predictive value beyond supplied metric f(R) gravity?",
        "Would a bounded viability obstruction justify prioritizing the minimal-mode route next?",
    ]
    return [
        {"question_id": f"DQ{i}", "question": question, "status": "UNANSWERED"}
        for i, question in enumerate(questions, start=1)
    ]


def _native_candidates() -> list[dict[str, Any]]:
    return [
        {
            "candidate_id": "NATIVE_PHI_ALIGNMENT_WITNESS",
            "authority_status": "ACCEPTED_ALIGNMENT_WITNESS_WITH_NATIVE_GENERATION_BLOCKED",
            "bridge_status": "NOT_IDENTIFIED",
            "disqualifying_shortcut": "field-name or equation-shape resemblance",
        },
        {
            "candidate_id": "PROVISIONAL_CLASSICAL_SCALAR_SOURCE_SANDBOX",
            "authority_status": "SUPPLIED_PROVISIONAL_ON_SHELL_SOURCE_NOT_NATIVE_MATTER",
            "bridge_status": "NOT_IDENTIFIED",
            "disqualifying_shortcut": "using a supplied source as a native matter derivation",
        },
        {
            "candidate_id": "PHI_CK_ADMISSIBILITY_RULE_FAMILY",
            "authority_status": "ARCHITECTURAL_ADMISSIBILITY_ONLY_NOT_DYNAMICAL",
            "bridge_status": "NOT_IDENTIFIED",
            "disqualifying_shortcut": "promoting an admissibility rule into a scalar equation",
        },
    ]


def _preparation_controls(value: dict[str, Any]) -> dict[str, Any]:
    scope = value["scope"]
    rows = [
        ("PREP_EXACT_AUTHORITY_CUSTODY", len(value["authority"]["frozen_artifacts"]) == 10),
        ("PREP_EXACT_SELECTED_TARGET", value["target"] == TARGET),
        ("PREP_COMPARISON_ONLY_PROVENANCE", value["comparison_branch"]["status"] == "SUPPLIED_QUADRATIC_GRAVITY_COMPARISON_SUBFAMILY"),
        ("PREP_BETA_NOT_ADOPTED", value["comparison_branch"]["beta_zero_adopted"] is False),
        ("PREP_ALPHA_NOT_SELECTED", value["comparison_branch"]["alpha_selected"] is False),
        ("PREP_SIX_PARAMETER_STRATA", value["parameter_domain"]["stratum_count"] == 6),
        ("PREP_EIGHT_SCALAR_TENSOR_OBLIGATIONS", value["scalar_tensor_equivalence"]["obligation_count"] == 8),
        ("PREP_INVERTIBILITY_AND_DOMAIN_EXPLICIT", {"AUXILIARY_EQUATION_AND_EQUIVALENCE_DOMAIN", "LEGENDRE_VARIABLE_AND_INVERTIBILITY", "CONFORMAL_MAP_AND_DOMAIN"}.issubset({row["obligation_id"] for row in value["scalar_tensor_equivalence"]["rows"]})),
        ("PREP_EXTERNAL_SOURCE_FIREWALL", value["matter_trace_contract"]["source_status"] == "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE"),
        ("PREP_TRACE_COUPLING_TO_BE_DERIVED", value["matter_trace_contract"]["trace_coupling_status"] == "TO_BE_DERIVED"),
        ("PREP_THREE_BACKGROUND_CAP", value["background_contract"]["background_count"] == 3),
        ("PREP_STABILITY_NOTIONS_DISJOINT", value["background_contract"]["stability_notions_interchangeable"] is False),
        ("PREP_SCREENING_NOT_PRELOADED", value["screening_contract"]["screening_mechanism_claimed"] is False),
        ("PREP_OBSERVABLE_MAP_BOUNDED", value["observable_channel_map"]["empirical_analysis_authorized"] is False),
        ("PREP_NATIVE_BRIDGE_FIREWALL", value["native_relevance_contract"]["all_bridge_fields_required"] is True and value["native_relevance_contract"]["bridge_identified_count"] == 0),
        ("PREP_EIGHT_DECISION_QUESTIONS", value["decision_questions"]["question_count"] == 8 and value["decision_questions"]["answered_count"] == 0),
        ("PREP_TWO_STAGE_OUTCOMES_DISJOINT", set(value["outcome_contract"]["packet_review_outcomes"]).isdisjoint(value["outcome_contract"]["future_execution_outcomes"])),
        ("PREP_ZERO_EXECUTION_AND_ROTATE", value["work_packages"]["executed_count"] == 0 and all(item is False for key, item in scope.items() if key != "packet_preparation_executed") and value["selected_next_target"] == SELECTED_NEXT_TARGET),
    ]
    return {
        "control_count": len(rows),
        "pass_count": sum(passed for _, passed in rows),
        "failure_count": sum(not passed for _, passed in rows),
        "rows": [{"control_id": control_id, "passed": passed} for control_id, passed in rows],
    }


def build_packet() -> dict[str, Any]:
    custody, selection = _validate_authority()
    for relative_path in (HUMAN_RELATIVE_PATH, TEST_RELATIVE_PATH):
        if not (REPO_ROOT / relative_path).is_file():
            raise ValueError(f"packet companion missing: {relative_path}")

    scalar_tensor = _scalar_tensor_obligations()
    backgrounds = _backgrounds()
    work_packages = _work_packages()
    questions = _decision_questions()
    candidates = _native_candidates()
    value: dict[str, Any] = {
        "schema_id": "toe.scalar_only_quadratic_gravity_viability_and_native_relevance.packet.v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "frozen_artifact_count": len(custody),
            "frozen_artifacts": custody,
            "consumed_response_selection_verdict": selection["verdict"],
            "consumed_candidate_id": selection["selected_candidate_id"],
        },
        "comparison_branch": {
            "status": "SUPPLIED_QUADRATIC_GRAVITY_COMPARISON_SUBFAMILY",
            "motivation": "CONDITIONALLY_REACHED_THROUGH_SUPPLIED_GHOST_AVOIDANCE",
            "action": "(c^3/(16 pi G)) integral d4x sqrt(-g) (R+alpha R^2)",
            "beta_restriction": "beta=0 FOR_COMPARISON_ONLY",
            "beta_zero_adopted": False,
            "alpha_selected": False,
            "toe_native": False,
            "candidate_action": False,
        },
        "accepted_input": {
            "massless_spin2_retained": True,
            "scalar_mass_squared": "-1/(6 alpha)",
            "non_tachyonic_scalar_stratum": "alpha<0 under frozen conventions",
            "stationary_00_scalar_sensitive": True,
            "stationary_conserved_0i_scalar_contribution": "ZERO_AT_ACCEPTED_LINEAR_ORDER",
            "full_viability_established": False,
            "native_relevance_established": False,
        },
        "parameter_domain": {
            "stratum_count": 6,
            "rows": _parameter_strata(),
            "numerical_alpha_selected": False,
            "parameter_bound_inferred": False,
        },
        "scalar_tensor_equivalence": {
            "obligation_count": len(scalar_tensor),
            "derived_count": 0,
            "rows": scalar_tensor,
            "frame_transform_empirical_equivalence_preclaimed": False,
        },
        "matter_trace_contract": {
            "source_status": "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE",
            "source_conservation": "SUPPLIED_NOT_DERIVED_FROM_A_TOE_MATTER_ACTION",
            "optional_supplied_matter_model_selected": False,
            "trace_coupling_status": "TO_BE_DERIVED",
            "required_source_controls": ["T_NOT_EQUAL_ZERO", "CLASSICALLY_TRACELESS_SOURCE"],
            "toe_matter_action_claimed": False,
        },
        "background_contract": {
            "background_count": len(backgrounds),
            "analyzed_count": 0,
            "rows": backgrounds,
            "stability_notions": [
                "BACKGROUND_EXISTENCE",
                "POSITIVE_KINETIC_SIGN",
                "NO_TACHYONIC_LINEAR_MODE",
                "MATTER_STABILITY",
                "NO_RAPID_RUNAWAY_ON_DECLARED_TIMESCALE",
            ],
            "stability_notions_interchangeable": False,
            "arbitrary_background_stability_claimed": False,
        },
        "screening_contract": {
            "question": "Does the pure R+alpha R^2 branch suppress scalar response beyond finite mass?",
            "screening_mechanism_claimed": False,
            "screening_model_to_be_built": False,
            "allowed_future_findings": [
                "FINITE_MASS_SUPPRESSION_ONLY",
                "BOUNDED_NONLINEAR_SUPPRESSION_DERIVED",
                "SCREENING_QUESTION_UNRESOLVED",
            ],
        },
        "observable_channel_map": {
            "static_mass_or_trace_channel": "DIRECTLY_SENSITIVE_TO_SCALAR_AT_ACCEPTED_LINEAR_ORDER",
            "stationary_conserved_current_channel": "NO_DIRECT_SCALAR_CONTRIBUTION_AT_ACCEPTED_LINEAR_ORDER",
            "combined_channel_role": "POTENTIAL_SCALAR_VERSUS_SPIN2_COMPARISON_DISCRIMINATOR",
            "empirical_analysis_authorized": False,
            "metric_to_orbit_transport_authorized": False,
        },
        "native_relevance_contract": {
            "candidate_count": len(candidates),
            "bridge_identified_count": 0,
            "rows": candidates,
            "required_bridge_fields": [
                "FIELD_DEFINITION",
                "TRANSFORMATION_LAW",
                "DIMENSIONS",
                "COUPLINGS",
                "EQUATION_OF_MOTION",
                "DOMAIN",
                "OBSERVABLE_ROLE",
            ],
            "all_bridge_fields_required": True,
            "resemblance_or_shared_name_sufficient": False,
            "candidate_outcome_requires_separate_seam_packet": True,
        },
        "work_packages": {
            "work_package_count": len(work_packages),
            "executed_count": 0,
            "rows": work_packages,
        },
        "decision_questions": {
            "question_count": len(questions),
            "answered_count": 0,
            "rows": questions,
        },
        "outcome_contract": {
            "packet_review_outcomes": list(PACKET_REVIEW_OUTCOMES),
            "packet_review_outcome_now": None,
            "future_execution_outcomes": list(FUTURE_EXECUTION_OUTCOMES),
            "future_execution_outcome_now": None,
            "exactly_one_outcome_per_stage": True,
            "native_bridge_candidate_is_not_adoption": True,
        },
        "post_derivation_oracles": [
            {"source": "https://arxiv.org/abs/0805.1726", "role": "F_R_EQUIVALENCE_VIABILITY_REVIEW_ORACLE"},
            {"source": "https://arxiv.org/abs/gr-qc/0703044", "role": "CONSTANT_CURVATURE_STABILITY_EQUIVALENCE_ORACLE"},
            {"source": "https://arxiv.org/abs/astro-ph/0610734", "role": "METRIC_F_R_MATTER_STABILITY_ORACLE"},
            {"source": "https://arxiv.org/abs/1002.4928", "role": "LOCAL_CONSTRAINT_AND_SCREENING_REVIEW_ORACLE"},
            {"source": "https://arxiv.org/abs/1402.4469", "role": "R_SQUARED_MATTER_SUPPORTED_BACKGROUND_ORACLE"},
        ],
        "review_contract": {
            "gate_count": 18,
            "independent_review_required": True,
            "scientific_execution_authorized_before_acceptance": False,
            "maximum_authority_after_acceptance": "ONE_BOUNDED_SCALAR_ONLY_COMPARISON_EXECUTION",
            "result_review_required_after_execution": True,
        },
        "scope": {
            "packet_preparation_executed": True,
            "independent_review_executed": False,
            "scientific_execution_authorized": False,
            "scientific_execution_executed": False,
            "scalar_tensor_derivation_executed": False,
            "background_stability_analysis_executed": False,
            "trace_coupling_derived": False,
            "screening_mechanism_claimed": False,
            "native_scalar_bridge_identified": False,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_action_imported": False,
            "empirical_fitting_executed": False,
            "metric_to_orbit_transport_executed": False,
            "frame_dragging_resumed": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "quadratic_comparison": "ACCEPTED",
            "conditional_envelope": "ACCEPTED",
            "selected_research_response": "SCALAR_ONLY_VIABILITY_AND_NATIVE_RELEVANCE",
            "packet": VERDICT,
            "work_packages": "0_OF_6_EXECUTED",
            "decision_questions": "0_OF_8_ANSWERED",
            "alpha": "NOT_SELECTED",
            "beta_zero": "NOT_ADOPTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "Preparation only for one supplied scalar-only comparison investigation. "
            "No scalar-tensor equivalence, background stability, matter-trace coupling, "
            "screening mechanism, empirical constraint, native scalar bridge, beta or "
            "alpha condition, scalar branch, gravitational principle, gravitational "
            "action, matter sector, orbital transport, frame-dragging result, or master-"
            "action change is derived, selected, adopted, or authorized by this packet."
        ),
    }
    controls = _preparation_controls(value)
    if controls["failure_count"]:
        failed = [row["control_id"] for row in controls["rows"] if not row["passed"]]
        raise ValueError(f"scalar-only packet preparation failed: {failed}")
    value["preparation_controls"] = controls
    return value


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("scalar-only viability packet is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "controls": report["preparation_controls"]["pass_count"],
            "questions_answered": report["decision_questions"]["answered_count"],
            "status": "CHECKED",
            "verdict": report["verdict"],
            "work_packages_executed": report["work_packages"]["executed_count"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
