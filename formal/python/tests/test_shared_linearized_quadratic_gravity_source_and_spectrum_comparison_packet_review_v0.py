from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_review_v0 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_freezes_packet_custody() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {row["relative_path"]: row["sha256"] for row in report["authority"]["frozen_packet_artifacts"]} == review.PACKET_HASHES


def test_all_fifteen_independent_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 15
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_dimensions_are_independently_reproduced() -> None:
    audit = _report()["independent_normalization_audit"]
    assert audit["dimension_order"] == ["M", "L", "T"]
    assert audit["A_EH"] == [1, 0, -1]
    assert audit["gravity_action"] == audit["source_action"] == [1, 2, -1]
    assert audit["alpha_dimension"] == audit["beta_dimension"] == [0, 2, 0]
    assert audit["passed"] is True


def test_source_sign_and_kappa_are_reproduced() -> None:
    audit = _report()["independent_normalization_audit"]
    assert audit["derived_rhs_sign"] == "POSITIVE"
    assert audit["derived_rhs_coefficient"] == "8 pi G/c^4"
    assert audit["source_stationarity"].startswith("A_EH H_mu_nu-(1/(2c))")


def test_gauss_bonnet_and_minkowski_gates_are_bounded() -> None:
    rows = {row["gate_id"]: row for row in _report()["review_gates"]["rows"]}
    assert rows["G5_FOUR_DIMENSIONAL_GAUSS_BONNET_SCOPE"]["status"] == "PASS"
    assert "local-bulk" in rows["G5_FOUR_DIMENSIONAL_GAUSS_BONNET_SCOPE"]["finding"]
    assert rows["G6_MINKOWSKI_ADMISSIBLE_BUT_EXECUTION_GATED"]["status"] == "PASS"
    assert "D4 remains unexecuted" in rows["G6_MINKOWSKI_ADMISSIBLE_BUT_EXECUTION_GATED"]["finding"]


def test_alpha_beta_remain_exact_and_conventions_are_frozen() -> None:
    rows = {row["gate_id"]: row for row in _report()["review_gates"]["rows"]}
    assert rows["G7_LINEARIZATION_EXACT_IN_ALPHA_BETA"]["status"] == "PASS"
    assert rows["G8_CONVENTIONS_AND_BOUNDARY_PRESCRIPTIONS_FROZEN"]["status"] == "PASS"


def test_no_mode_or_physical_output_is_preloaded() -> None:
    posture = _report()["current_posture"]
    assert posture["derivation_stages_completed"] == "0/10"
    assert posture["mode_judgments"] == "0/3"
    assert posture["physical_outputs"] == "0/11"
    assert posture["shared_path_controls_executed"] == "0/10"


def test_residue_rule_is_operational_and_does_not_label_degenerate_poles() -> None:
    rule = _report()["binding_residue_rule"]
    for phrase in (
        "conserved-source saturated amplitude",
        "spin-2 or scalar projector channel",
        "positive Einstein massless-spin-2 reference",
        "Repeated, merged, or non-diagonalizable poles receive no sign",
    ):
        assert phrase in rule


def test_00_and_0i_must_come_from_one_operator() -> None:
    rows = {row["gate_id"]: row for row in _report()["review_gates"]["rows"]}
    assert rows["G12_ONE_OPERATOR_SUPPLIES_00_AND_0I"]["status"] == "PASS"
    assert "one inverted, saturated operator" in rows["G12_ONE_OPERATOR_SUPPLIES_00_AND_0I"]["finding"]


def test_exactly_one_execution_is_authorized_with_twelve_clauses() -> None:
    authorization = _report()["authorized_execution"]
    assert authorization["execution_count"] == 1
    assert authorization["derivation_step_count"] == 10
    assert authorization["shared_path_control_count"] == 10
    assert authorization["required_output_count"] == 11
    assert len(authorization["clauses"]) == 12
    assert authorization["result_review_target"] == review.RESULT_REVIEW_TARGET


def test_authorization_does_not_execute_or_promote_the_comparison() -> None:
    scope = _report()["scope"]
    assert scope["independent_packet_review_executed"] is True
    assert scope["packet_accepted"] is True
    assert scope["one_comparison_execution_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "independent_packet_review_executed",
            "packet_accepted",
            "one_comparison_execution_authorized",
        }:
            assert value is False, key


def test_literature_is_oracle_only() -> None:
    roles = {row["role"] for row in _report()["scientific_oracle_spot_checks"]}
    assert len(roles) == 4
    assert all(role.endswith("ONLY") for role in roles)


def test_human_review_records_verdict_algebra_residue_rule_and_stop() -> None:
    text = (REPO_ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "15 / 15 PASSED",
        "(8 pi G/c^4) T_mu_nu",
        "G11 — Pole and residue semantics",
        "repeated, merged, or non-diagonalizable",
        review.RESULT_REVIEW_TARGET,
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
