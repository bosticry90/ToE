from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import scalar_only_quadratic_gravity_viability_and_native_relevance_packet_v0 as packet


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _rows(section: str, id_key: str) -> dict[str, dict[str, object]]:
    return {row[id_key]: row for row in _report()[section]["rows"]}


def test_packet_regenerates_exactly_and_preserves_authority_bytes() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    packet.build_packet()
    after = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    assert before == after == packet.AUTHORITY_HASHES


def test_exact_selection_authority_is_consumed_and_review_is_next() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["authority"]["consumed_response_selection_verdict"] == (
        "SELECTED_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_"
        "RELEVANCE_PACKET_PREPARATION"
    )
    assert report["authority"]["consumed_candidate_id"] == (
        "SCALAR_ONLY_VIABILITY_AND_NATIVE_RELEVANCE"
    )
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == packet.SELECTED_NEXT_TARGET_KIND


def test_comparison_branch_is_frozen_without_beta_or_alpha_adoption() -> None:
    branch = _report()["comparison_branch"]
    assert branch["status"] == "SUPPLIED_QUADRATIC_GRAVITY_COMPARISON_SUBFAMILY"
    assert branch["motivation"] == (
        "CONDITIONALLY_REACHED_THROUGH_SUPPLIED_GHOST_AVOIDANCE"
    )
    assert branch["beta_restriction"] == "beta=0 FOR_COMPARISON_ONLY"
    assert branch["beta_zero_adopted"] is False
    assert branch["alpha_selected"] is False
    assert branch["toe_native"] is branch["candidate_action"] is False


def test_accepted_input_retains_only_bounded_comparison_facts() -> None:
    accepted = _report()["accepted_input"]
    assert accepted["scalar_mass_squared"] == "-1/(6 alpha)"
    assert accepted["non_tachyonic_scalar_stratum"].startswith("alpha<0")
    assert accepted["stationary_00_scalar_sensitive"] is True
    assert accepted["stationary_conserved_0i_scalar_contribution"] == (
        "ZERO_AT_ACCEPTED_LINEAR_ORDER"
    )
    assert accepted["full_viability_established"] is False
    assert accepted["native_relevance_established"] is False


def test_six_parameter_strata_keep_limits_and_finite_values_distinct() -> None:
    domain = _report()["parameter_domain"]
    strata = _rows("parameter_domain", "stratum_id")
    assert domain["stratum_count"] == len(strata) == 6
    assert strata["FINITE_NON_TACHYONIC_SCALAR"]["condition"] == "alpha<0"
    assert strata["EINSTEIN_COMPARISON_LIMIT"]["condition"] == "alpha=0"
    assert strata["TACHYONIC_SCALAR"]["condition"] == "alpha>0"
    assert "limit" in strata["INFINITE_MASS_DECOUPLING_PATH"]["qualification"]
    assert strata["MASSLESS_OR_SINGULAR_LIMIT"]["status"] == (
        "FRESH_DOMAIN_AND_DERIVATION_REQUIRED"
    )
    assert domain["numerical_alpha_selected"] is False
    assert domain["parameter_bound_inferred"] is False


def test_scalar_tensor_equivalence_has_eight_unexecuted_derivation_obligations() -> None:
    contract = _report()["scalar_tensor_equivalence"]
    rows = _rows("scalar_tensor_equivalence", "obligation_id")
    assert contract["obligation_count"] == len(rows) == 8
    assert contract["derived_count"] == 0
    assert all(row["status"] == "TO_BE_DERIVED" for row in rows.values())
    assert all(
        row["literature_formula_may_replace_derivation"] is False
        for row in rows.values()
    )
    for obligation_id in (
        "AUXILIARY_FIELD_INTRODUCTION",
        "AUXILIARY_EQUATION_AND_EQUIVALENCE_DOMAIN",
        "LEGENDRE_VARIABLE_AND_INVERTIBILITY",
        "CONFORMAL_MAP_AND_DOMAIN",
        "MATTER_TRANSFORMATION_AND_OBSERVABLE_CAVEAT",
    ):
        assert obligation_id in rows


def test_frame_equivalence_does_not_preclaim_empirical_equivalence() -> None:
    assert _report()["scalar_tensor_equivalence"][
        "frame_transform_empirical_equivalence_preclaimed"
    ] is False


def test_matter_trace_contract_is_external_supplied_and_uncomputed() -> None:
    matter = _report()["matter_trace_contract"]
    assert matter["source_status"] == (
        "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE"
    )
    assert matter["source_conservation"] == (
        "SUPPLIED_NOT_DERIVED_FROM_A_TOE_MATTER_ACTION"
    )
    assert matter["trace_coupling_status"] == "TO_BE_DERIVED"
    assert matter["required_source_controls"] == [
        "T_NOT_EQUAL_ZERO",
        "CLASSICALLY_TRACELESS_SOURCE",
    ]
    assert matter["optional_supplied_matter_model_selected"] is False
    assert matter["toe_matter_action_claimed"] is False


def test_background_contract_is_capped_and_stability_notions_are_disjoint() -> None:
    backgrounds = _report()["background_contract"]
    rows = _rows("background_contract", "background_id")
    assert backgrounds["background_count"] == len(rows) == 3
    assert backgrounds["analyzed_count"] == 0
    assert set(rows) == {
        "MINKOWSKI_CONTROL",
        "CONSTANT_CURVATURE_VACUUM",
        "SIMPLE_MATTER_SUPPORTED_BACKGROUND",
    }
    assert "WITHOUT_ADDING_A_COSMOLOGICAL_TERM" in rows[
        "CONSTANT_CURVATURE_VACUUM"
    ]["existence_gate"]
    assert rows["SIMPLE_MATTER_SUPPORTED_BACKGROUND"]["existence_gate"] == (
        "BLOCK_IF_NO_CONTROLLED_SUPPLIED_MATTER_MODEL"
    )
    assert backgrounds["stability_notions_interchangeable"] is False
    assert backgrounds["arbitrary_background_stability_claimed"] is False
    assert len(backgrounds["stability_notions"]) == 5


def test_screening_mechanism_is_a_question_not_a_preloaded_result() -> None:
    screening = _report()["screening_contract"]
    assert screening["screening_mechanism_claimed"] is False
    assert screening["screening_model_to_be_built"] is False
    assert screening["allowed_future_findings"] == [
        "FINITE_MASS_SUPPRESSION_ONLY",
        "BOUNDED_NONLINEAR_SUPPRESSION_DERIVED",
        "SCREENING_QUESTION_UNRESOLVED",
    ]


def test_observable_channel_map_retains_00_0i_distinction_without_data_work() -> None:
    observable = _report()["observable_channel_map"]
    assert observable["static_mass_or_trace_channel"].startswith("DIRECTLY_SENSITIVE")
    assert observable["stationary_conserved_current_channel"].startswith(
        "NO_DIRECT_SCALAR_CONTRIBUTION"
    )
    assert observable["empirical_analysis_authorized"] is False
    assert observable["metric_to_orbit_transport_authorized"] is False


def test_native_candidates_are_audited_but_no_bridge_is_identified() -> None:
    native = _report()["native_relevance_contract"]
    rows = _rows("native_relevance_contract", "candidate_id")
    assert native["candidate_count"] == len(rows) == 3
    assert native["bridge_identified_count"] == 0
    assert set(rows) == {
        "NATIVE_PHI_ALIGNMENT_WITNESS",
        "PROVISIONAL_CLASSICAL_SCALAR_SOURCE_SANDBOX",
        "PHI_CK_ADMISSIBILITY_RULE_FAMILY",
    }
    assert all(row["bridge_status"] == "NOT_IDENTIFIED" for row in rows.values())
    assert "NATIVE_GENERATION_BLOCKED" in rows[
        "NATIVE_PHI_ALIGNMENT_WITNESS"
    ]["authority_status"]
    assert "NOT_NATIVE_MATTER" in rows[
        "PROVISIONAL_CLASSICAL_SCALAR_SOURCE_SANDBOX"
    ]["authority_status"]
    assert "NOT_DYNAMICAL" in rows[
        "PHI_CK_ADMISSIBILITY_RULE_FAMILY"
    ]["authority_status"]


def test_native_bridge_requires_all_seven_fields_and_a_separate_seam_packet() -> None:
    native = _report()["native_relevance_contract"]
    assert native["required_bridge_fields"] == [
        "FIELD_DEFINITION",
        "TRANSFORMATION_LAW",
        "DIMENSIONS",
        "COUPLINGS",
        "EQUATION_OF_MOTION",
        "DOMAIN",
        "OBSERVABLE_ROLE",
    ]
    assert native["all_bridge_fields_required"] is True
    assert native["resemblance_or_shared_name_sufficient"] is False
    assert native["candidate_outcome_requires_separate_seam_packet"] is True


def test_six_work_packages_and_eight_questions_are_prepared_but_unexecuted() -> None:
    report = _report()
    packages = report["work_packages"]
    questions = report["decision_questions"]
    assert packages["work_package_count"] == len(packages["rows"]) == 6
    assert packages["executed_count"] == 0
    assert all(row["status"] == "NOT_EXECUTED" for row in packages["rows"])
    assert questions["question_count"] == len(questions["rows"]) == 8
    assert questions["answered_count"] == 0
    assert all(row["status"] == "UNANSWERED" for row in questions["rows"])


def test_packet_review_and_future_execution_outcomes_are_disjoint_and_empty() -> None:
    outcomes = _report()["outcome_contract"]
    assert tuple(outcomes["packet_review_outcomes"]) == packet.PACKET_REVIEW_OUTCOMES
    assert tuple(outcomes["future_execution_outcomes"]) == packet.FUTURE_EXECUTION_OUTCOMES
    assert set(outcomes["packet_review_outcomes"]).isdisjoint(
        outcomes["future_execution_outcomes"]
    )
    assert outcomes["packet_review_outcome_now"] is None
    assert outcomes["future_execution_outcome_now"] is None
    assert outcomes["exactly_one_outcome_per_stage"] is True
    assert outcomes["native_bridge_candidate_is_not_adoption"] is True


def test_review_can_authorize_only_one_bounded_execution() -> None:
    review = _report()["review_contract"]
    assert review["gate_count"] == 18
    assert review["independent_review_required"] is True
    assert review["scientific_execution_authorized_before_acceptance"] is False
    assert review["maximum_authority_after_acceptance"] == (
        "ONE_BOUNDED_SCALAR_ONLY_COMPARISON_EXECUTION"
    )
    assert review["result_review_required_after_execution"] is True


def test_eighteen_preparation_controls_pass() -> None:
    controls = _report()["preparation_controls"]
    assert controls["control_count"] == controls["pass_count"] == 18
    assert controls["failure_count"] == 0
    assert all(row["passed"] for row in controls["rows"])


def test_scope_stops_before_science_adoption_and_downstream_work() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_executed"] is True
    for key, value in scope.items():
        if key != "packet_preparation_executed":
            assert value is False, key


def test_human_packet_exposes_provenance_obligations_firewalls_and_stop() -> None:
    text = (REPO_ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "SUPPLIED_QUADRATIC_GRAVITY_COMPARISON_SUBFAMILY",
        "0 / 6",
        "0 / 8",
        "AUXILIARY_EQUATION_AND_EQUIVALENCE_DOMAIN",
        "CONSTANT_CURVATURE_VACUUM",
        "CLASSICALLY_TRACELESS_SOURCE",
        "FINITE_MASS_SUPPRESSION_ONLY",
        "NATIVE_PHI_ALIGNMENT_WITNESS",
        "FIELD_DEFINITION",
        "SCALAR_ONLY_VIABILITY_CONTRACT_READY",
        "NATIVE_SCALAR_BRIDGE_CANDIDATE_IDENTIFIED",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
