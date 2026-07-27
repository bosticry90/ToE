from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_result_review_v0 as review,
)
from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_v0 as survey,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_result_review_regenerates_exactly_and_freezes_survey() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["authority"]["consumed_survey_verdict"] == survey.VERDICT
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_survey_artifacts"]
    } == review.SURVEY_ARTIFACT_HASHES


def test_all_twelve_independent_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 12
    assert gates["failure_count"] == 0
    assert [row["gate"] for row in gates["rows"]] == list(range(1, 13))
    assert all(row["passed"] for row in gates["rows"])


def test_review_reproduces_questions_cells_and_real_blanks() -> None:
    report = _report()
    result = report["survey_result"]
    assert result["decision_critical_questions_answered"] == 8
    assert result["surveyed_provisional_cells"] == 22
    assert result["NOT_SURVEYED_cells"] == 48
    assert result["incomplete_entries"] == 0
    assert result["authoritative_V2_matrix_cells"] == 0
    dispositions = report["review_gates"]["structural_disposition_tally"]
    assert dispositions == {
        "VALID_PROVISIONAL_ENTRY": 22,
        "VALID_NOT_SURVEYED": 48,
        "INCOMPLETE_SURVEY_ENTRY": 0,
    }


def test_every_surveyed_cell_is_question_support_or_explicit_scope_context() -> None:
    gates = _report()["review_gates"]
    surveyed = set(gates["surveyed_cell_ids"])
    support = set(gates["question_support_cell_ids"])
    contextual = set(gates["contextual_scope_cell_ids"])
    assert surveyed == support | contextual
    assert contextual == {
        "EXP_R2_METRIC_ONLY__F_EXTRA_FIELD",
        "EXP_R2_METRIC_ONLY__F_CONNECTION_TORSION",
        "EXP_R3_LOCALITY__F_NONLOCAL",
    }


def test_scientific_spot_checks_are_limited_and_non_self_certifying() -> None:
    checks = _report()["scientific_source_spot_checks"]
    assert checks["check_count"] == 8
    assert checks["all_supported_in_limited_scope"] is True
    assert checks["custody_substitutes_for_scientific_relevance"] is False
    assert checks["family_scope_generalization_permitted"] is False
    for row in checks["rows"]:
        assert row["reference"].startswith("https://")
        assert row["reviewed_claim"]
        assert row["finding"].startswith("SUPPORTED")
        assert row["scope_limit"]


def test_review_keeps_quadratic_warning_and_fr_stability_scoped() -> None:
    checks = {row["check_id"]: row for row in _report()["scientific_source_spot_checks"]["rows"]}
    quadratic = checks["SRC_QUADRATIC_MODE_CONTENT"]
    assert "GENERIC_LOCAL_METRIC_FLAT_SPACE" in quadratic["finding"]
    assert "nonlocal" in quadratic["scope_limit"]
    fr = checks["SRC_FR_STABILITY_CONDITION"]
    assert "MODEL" not in fr["finding"] or "METRIC_FR" in fr["finding"]
    assert "Matter instability is not identical" in fr["scope_limit"]


def test_next_packet_contract_has_all_ten_binding_obligations() -> None:
    contract = _report()["next_packet_preparation_contract"]
    assert contract["obligation_count"] == 10
    assert [row["obligation_id"] for row in contract["rows"]] == [
        "O1_COMPARISON_STATUS_AND_PROVENANCE",
        "O2_FOUR_DIMENSIONAL_QUADRATIC_BASIS",
        "O3_EXTERNAL_CONSERVED_COMPARISON_SOURCE",
        "O4_BACKGROUND_COORDINATES_SIGNATURE_UNITS",
        "O5_NORMALIZATION_AND_ANALYTIC_CONVENTIONS",
        "O6_LINEARIZED_EQUATION_DERIVATION",
        "O7_MODES_POLES_RESIDUES",
        "O8_SOURCE_CHANNEL_GREEN_FUNCTIONS",
        "O9_SHARED_PATH_CONTROLS",
        "O10_STOP_BOUNDARY",
    ]
    assert contract["packet_preparation_only"] is True
    assert contract["comparison_execution_authorized"] is False
    assert contract["independent_packet_review_required"] is True
    assert all(row["required"] for row in contract["rows"])


def test_comparison_status_and_gauss_bonnet_scope_are_binding() -> None:
    rows = {
        row["obligation_id"]: row["required"]
        for row in _report()["next_packet_preparation_contract"]["rows"]
    }
    status = rows["O1_COMPARISON_STATUS_AND_PROVENANCE"]
    for token in (
        "COMPARISON ACTION FAMILY",
        "NOT A TOE CANDIDATE",
        "NOT A SUCCESSOR MASTER ACTION",
        "NOT A NATIVE POSTULATE",
    ):
        assert token in status
    basis = rows["O2_FOUR_DIMENSIONAL_QUADRATIC_BASIS"]
    assert "Riemann-squared included before basis reduction" in basis
    assert "four-dimensional Gauss-Bonnet identity" in basis
    assert "compact-support local-bulk equivalence domain" in basis
    assert "no transport to boundary observables topology or global charges" in basis


def test_external_source_background_and_normalization_are_frozen_next() -> None:
    rows = {
        row["obligation_id"]: row["required"]
        for row in _report()["next_packet_preparation_contract"]["rows"]
    }
    source = rows["O3_EXTERNAL_CONSERVED_COMPARISON_SOURCE"]
    assert "externally supplied T_mn" in source
    assert "partial_mu T^mu_nu = 0" in source
    assert "S_m notation does not select a ToE matter action" in source
    background = rows["O4_BACKGROUND_COORDINATES_SIGNATURE_UNITS"]
    for token in ("g_mn = eta_mn + h_mn", "x^0 = c t", "signature (+,-,-,-)"):
        assert token in background
    normalization = rows["O5_NORMALIZATION_AND_ANALYTIC_CONVENTIONS"]
    for token in (
        "Einstein-Hilbert normalization", "dimensions and signs of alpha beta",
        "Fourier convention", "pole prescription", "gauge fixing",
    ):
        assert token in normalization


def test_modes_green_functions_and_controls_are_complete() -> None:
    rows = {
        row["obligation_id"]: row["required"]
        for row in _report()["next_packet_preparation_contract"]["rows"]
    }
    modes = rows["O7_MODES_POLES_RESIDUES"]
    for token in (
        "massless spin-2", "massive scalar", "generic massive spin-2",
        "pole locations", "residue signs", "tachyon conditions",
        "trace and transverse source couplings",
    ):
        assert token in modes
    green = rows["O8_SOURCE_CHANNEL_GREEN_FUNCTIONS"]
    assert "stationary h_00 for mass density" in green
    assert "stationary h_0i for conserved current" in green
    controls = rows["O9_SHARED_PATH_CONTROLS"]
    assert "alpha=beta=0 Einstein control" in controls
    assert "beta=0 no generic massive spin-2 correction" in controls
    assert "T_0i=0 no current-sourced stationary h_0i" in controls
    assert "T_0i sign reversal implies h_0i sign reversal" in controls
    assert "no coefficient fitting" in controls


def test_acceptance_authorizes_preparation_only() -> None:
    report = _report()
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND
    boundary = report["authorization_boundary"]
    assert boundary["comparison_packet_preparation_authorized"] is True
    for key, value in boundary.items():
        if key != "comparison_packet_preparation_authorized":
            assert value is False, key


def test_no_scientific_execution_or_promotion_occurred() -> None:
    scope = _report()["scope"]
    assert scope["independent_survey_result_review_executed"] is True
    assert scope["survey_accepted"] is True
    for key, value in scope.items():
        if key not in {
            "independent_survey_result_review_executed",
            "survey_accepted",
            "authoritative_V2_matrix_cells_computed",
        }:
            assert value is False, key
    assert scope["authoritative_V2_matrix_cells_computed"] == 0


def test_human_review_records_verdict_gates_contract_and_stop() -> None:
    text = (REPO_ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "12 / 12 PASSED",
        "G1",
        "G12",
        "Forty-eight real blanks",
        "four-dimensional Gauss–Bonnet identity",
        "externally supplied conserved comparison source",
        "ghost, tachyon, classical runaway",
        "alpha = beta = 0",
        "It does not authorize the comparison execution",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
