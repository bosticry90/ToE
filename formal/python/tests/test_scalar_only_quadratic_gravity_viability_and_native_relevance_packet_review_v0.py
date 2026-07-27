from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import scalar_only_quadratic_gravity_viability_and_native_relevance_packet_review_v0 as review


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _gates() -> dict[str, dict[str, object]]:
    return {row["gate_id"]: row for row in _report()["review_gates"]["rows"]}


def test_review_regenerates_exactly_and_preserves_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    review.build_review()
    after = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    assert before == after == review.PACKET_HASHES


def test_review_consumes_exact_packet_target_and_authorizes_one_execution() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["principal_packet_review_outcome"] == review.PRINCIPAL_OUTCOME
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND
    assert report["authorized_execution"]["execution_count"] == 1


def test_complete_convention_map_resolves_alpha_fRR_sign_tension() -> None:
    audit = _report()["independent_convention_translation_audit"]
    assert audit["metric_map"] == "g_literature=-g_packet"
    assert audit["Levi_Civita_connection_map"] == "Gamma_literature=Gamma_packet"
    assert audit["lower_Ricci_map"] == "Ricci_literature=Ricci_packet"
    assert audit["Ricci_scalar_map"] == "R_literature=-R_packet"
    assert audit["quadratic_coupling_map"] == "alpha_literature=-alpha_packet"
    assert audit["literature_f_RR"] == "2 alpha_literature=-2 alpha_packet"
    assert audit["literature_matter_stability_condition"] == "f_RR_literature>0"
    assert audit["translated_packet_condition"] == "alpha_packet<0"
    assert audit["packet_scalar_mass_squared"] == "-1/(6 alpha)"
    assert audit["sign_tension_resolved"] is True


def test_convention_rule_requires_more_than_printed_alpha_sign() -> None:
    rule = _report()["independent_convention_translation_audit"]["binding_rule"]
    for token in ("signature", "Riemann/Ricci", "Box", "source sign", "alpha/f_RR"):
        assert token in rule


def test_pure_vacuum_constant_curvature_has_only_zero_root() -> None:
    audit = _report()["independent_constant_curvature_audit"]
    assert audit["model"] == "f(R)=R+alpha R^2"
    assert audit["vacuum_constant_curvature_equation"] == "f_R(R0) R0-2 f(R0)=0"
    assert audit["expanded_left_hand_side"].endswith("=-R0")
    assert audit["solution_set"] == ["R0=0"]
    assert audit["nonzero_vacuum_de_Sitter_or_anti_de_Sitter_admitted"] is False
    assert audit["cosmological_constant_added"] is False
    assert audit["stability_analysis_executed"] is False


def test_non_minkowski_background_requires_controlled_supplied_source() -> None:
    matter = _report()["binding_matter_supported_background_rule"]
    assert matter["requirements_satisfied_now"] is False
    assert matter["matter_supported_analysis_executed"] is False
    assert matter["fail_closed_outcome_if_missing"] == (
        "BLOCKED_MATTER_TRACE_COUPLING_UNDEFINED"
    )
    assert matter["curved_background_source_requirements"] == [
        "EXPLICITLY_SUPPLIED_MATTER_OR_SOURCE_MODEL",
        "BACKGROUND_COVARIANT_CONSERVATION",
        "ON_SHELL_OR_OFF_SHELL_STATUS",
        "JORDAN_OR_EINSTEIN_FRAME_TRACE_DEFINITION",
        "BACKGROUND_EXISTENCE_SOLUTION",
    ]
    assert matter["toe_matter_action_inferred"] is False


def test_all_eighteen_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 18
    assert gates["failure_count"] == 0
    assert len(_gates()) == 18
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scalar_tensor_map_and_domains_remain_unexecuted_obligations() -> None:
    report = _report()
    gates = _gates()
    assert gates["G4_EIGHT_SCALAR_TENSOR_OBLIGATIONS_UNEXECUTED"]["status"] == "PASS"
    assert gates["G5_INVERTIBILITY_CONFORMAL_AND_SINGULAR_DOMAINS_REQUIRED"]["status"] == "PASS"
    assert report["authorized_execution"]["scalar_tensor_obligation_count"] == 8
    assert report["authorized_execution"]["derived_scalar_tensor_obligation_count_now"] == 0
    assert report["scope"]["scalar_tensor_derivation_executed"] is False


def test_five_stability_notions_cannot_substitute_for_one_another() -> None:
    gate = _gates()["G9_FIVE_STABILITY_NOTIONS_CANNOT_SUBSTITUTE"]
    assert gate["status"] == "PASS"
    assert "remain distinct" in gate["finding"]
    rules = " ".join(_report()["binding_execution_rules"])
    for token in ("background existence", "kinetic sign", "tachyon absence", "matter stability", "runaway timescale"):
        assert token in rules


def test_finite_mass_and_nonlinear_screening_remain_different() -> None:
    gate = _gates()["G11_FINITE_MASS_IS_NOT_SCREENING"]
    assert gate["status"] == "PASS"
    assert "Yukawa" in gate["finding"]
    assert _report()["scope"]["screening_mechanism_identified"] is False


def test_accepted_00_0i_map_is_not_extended_to_orbits_or_nonlinear_rotation() -> None:
    gate = _gates()["G12_00_0I_MAP_REMAINS_LINEAR_STATIONARY_ONLY"]
    assert gate["status"] == "PASS"
    assert "No claim about nonlinear rotating systems" in gate["finding"]
    assert _report()["scope"]["metric_to_orbit_transport_authorized"] is False
    assert _report()["scope"]["frame_dragging_reopened"] is False


def test_native_bridge_still_requires_seven_fields_and_separate_seam_packet() -> None:
    gate = _gates()["G13_SEVEN_FIELD_NATIVE_BRIDGE_FIREWALL"]
    assert gate["status"] == "PASS"
    assert "all seven" in gate["finding"]
    assert _report()["authorized_execution"]["native_bridge_identified_count_now"] == 0
    assert _report()["scope"]["native_scalar_bridge_identified"] is False


def test_viability_and_native_relevance_are_independent_axes() -> None:
    gate = _gates()["G14_VIABILITY_CANNOT_CREATE_NATIVE_RELEVANCE"]
    assert gate["status"] == "PASS"
    assert "independent reporting axes" in gate["finding"]


def test_six_packages_eight_questions_and_three_backgrounds_remain_zero() -> None:
    execution = _report()["authorized_execution"]
    assert execution["work_package_count"] == 6
    assert execution["executed_work_package_count_now"] == 0
    assert execution["decision_question_count"] == 8
    assert execution["answered_decision_question_count_now"] == 0
    assert execution["background_count_cap"] == 3
    assert execution["backgrounds_analyzed_now"] == 0


def test_execution_rules_bind_sign_background_source_and_stop() -> None:
    report = _report()
    rules = report["binding_execution_rules"]
    assert len(rules) == 12
    text = " ".join(rules)
    for token in (
        "convention translation",
        "R0=0",
        "covariantly conserved",
        "trace coupling",
        "finite-mass Yukawa",
        "all seven bridge fields",
        review.RESULT_REVIEW_TARGET,
    ):
        assert token in text


def test_scope_authorizes_reviewed_execution_but_performs_no_science_or_adoption() -> None:
    scope = _report()["scope"]
    assert scope["independent_packet_review_executed"] is True
    assert scope["packet_accepted"] is True
    assert scope["one_scalar_only_execution_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "independent_packet_review_executed",
            "packet_accepted",
            "one_scalar_only_execution_authorized",
        }:
            assert value is False, key


def test_human_review_exposes_sign_background_bridge_and_execution_boundaries() -> None:
    text = (REPO_ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        review.PRINCIPAL_OUTCOME,
        "alpha_literature  = -alpha_packet",
        "f_RR_literature   = 2 alpha_literature",
        "                  = -2 alpha_packet",
        "R_0=0",
        "BLOCKED_MATTER_TRACE_COUPLING_UNDEFINED",
        "G6_ALPHA_F_RR_CONVENTION_TRANSLATION_RESOLVED",
        "G7_CONSTANT_CURVATURE_EXISTENCE_BEFORE_STABILITY",
        "FINITE-MASS YUKAWA SUPPRESSION",
        "FIELD_DEFINITION",
        "0 / 6",
        "0 / 8",
        review.SELECTED_NEXT_TARGET,
        review.RESULT_REVIEW_TARGET,
    ):
        assert token in text
