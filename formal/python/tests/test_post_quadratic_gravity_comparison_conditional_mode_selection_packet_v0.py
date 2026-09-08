from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import post_quadratic_gravity_comparison_conditional_mode_selection_packet_v0 as packet


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _selectors() -> dict[str, dict[str, object]]:
    return {
        row["selector_id"]: row
        for row in _report()["selector_register"]["rows"]
    }


def _strata() -> dict[str, dict[str, object]]:
    return {
        row["stratum_id"]: row
        for row in _report()["parameter_strata"]["rows"]
    }


def test_packet_regenerates_exactly_and_preserves_authority_bytes() -> None:
    assert packet.artifact_bytes() == packet.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    packet.build_packet()
    after = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    assert before == after == packet.AUTHORITY_HASHES


def test_exact_selection_authority_is_consumed_and_review_is_next() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["authority"]["consumed_response_selection_verdict"] == (
        "SELECTED_CONDITIONAL_MODE_SELECTION_ENVELOPE_PACKET_PREPARATION"
    )
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == packet.SELECTED_NEXT_TARGET_KIND


def test_accepted_comparison_input_is_frozen_without_condition_selection() -> None:
    accepted = _report()["accepted_comparison_input"]
    assert accepted["Sigma"] == "3 alpha+beta"
    assert accepted["m0_squared"] == "-1/(2 Sigma)"
    assert accepted["m2_squared"] == "1/beta"
    assert accepted["scalar_residue"].startswith("POSITIVE")
    assert accepted["additional_spin2_residue"].startswith("NEGATIVE")
    assert accepted["stationary_0i"].endswith("SCALAR_ZERO")
    assert accepted["condition_selected_by_comparison"] is False


def test_authority_classes_are_exact_and_exclusive() -> None:
    contract = _report()["authority_class_contract"]
    assert tuple(contract["classes"]) == packet.AUTHORITY_CLASSES
    assert contract["exactly_one_class_per_selector"] is True
    assert contract["class_changes_conditional_algebra"] is False
    assert contract["catalog_project_requirement_count"] == 10
    assert contract["catalog_supplied_assumption_count"] == 3
    assert all(
        row["authority_class"] in packet.AUTHORITY_CLASSES
        for row in _selectors().values()
    )


def test_native_R9_and_R10_are_not_strengthened_into_branch_selectors() -> None:
    selectors = _selectors()
    r9 = selectors["SEL_NATIVE_R9_CURRENT_REPRESENTABILITY"]
    r10 = selectors["SEL_NATIVE_R10_STABILITY_EVALUATION"]
    assert r9["authority_class"] == "PROJECT_BOUND_NATIVE_PRINCIPLE"
    assert r9["parameter_restriction"] == "NONE_BY_ITSELF"
    assert r10["authority_class"] == "PROJECT_BOUND_NATIVE_PRINCIPLE"
    assert r10["parameter_restriction"] == "NONE_WITHOUT_AN_ACCEPTANCE_THRESHOLD"


def test_tachyon_freedom_does_not_cure_negative_residue() -> None:
    selector = _selectors()["SEL_NO_TACHYONIC_POLES"]
    assert selector["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"
    assert selector["parameter_restriction"] == (
        "Sigma<0 and beta>0 when both extra poles are present"
    )
    assert "NEGATIVE_RESIDUE_SPIN2" in selector["remaining_spectrum"]
    stratum = _strata()["BOTH_EXTRA_POLES_NON_TACHYONIC"]
    assert "residue negative" in stratum["spectrum"]
    assert stratum["qualification"] == "non-tachyonic is not healthy"


def test_standard_ghost_avoidance_leaves_scalar_branch_open() -> None:
    selector = _selectors()["SEL_NO_NEGATIVE_RESIDUE_SPIN2"]
    assert selector["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"
    assert selector["parameter_restriction"] == "beta=0"
    assert selector["remaining_spectrum"] == "MASSLESS_SPIN2_PLUS_POSSIBLE_SCALAR"


def test_minimal_mode_content_is_supplied_and_conditionally_collapses_to_EH() -> None:
    selectors = _selectors()
    scalar = selectors["SEL_NO_EXTRA_SCALAR"]
    minimal = selectors["SEL_MINIMAL_SPECTRUM"]
    assert scalar["parameter_restriction"] == "Sigma=0"
    assert minimal["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"
    assert minimal["authority_binding"] == "S3_NO_EXTRA_GRAVITATIONAL_MODES"
    assert minimal["parameter_restriction"] == (
        "beta=0 and Sigma=0 implies alpha=beta=0"
    )
    assert minimal["condition_adopted"] is False


def test_exact_and_empirical_current_conditions_remain_disjoint() -> None:
    selectors = _selectors()
    exact = selectors["SEL_EXACT_EINSTEIN_0I"]
    empirical = selectors["SEL_FINITE_PRECISION_0I"]
    assert exact["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"
    assert exact["parameter_restriction"] == "beta=0"
    assert empirical["authority_class"] == "EMPIRICAL_CONSTRAINT"
    assert "not logically inferred" in empirical["parameter_restriction"]
    assert exact["authority_binding"] != empirical["authority_binding"]


def test_long_range_recovery_does_not_select_an_action() -> None:
    row = _selectors()["SEL_LONG_RANGE_EINSTEIN"]
    assert row["parameter_restriction"] == (
        "broad finite positive-mass or decoupling regions remain"
    )
    assert row["remaining_spectrum"] == "EXTRA_FINITE_RANGE_MODES_MAY_REMAIN"


def test_hypothetical_postulate_is_classified_but_not_created() -> None:
    row = _selectors()["SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE"]
    assert row["authority_class"] == "PROPOSED_NEW_POSTULATE"
    assert row["authority_binding"] == "HYPOTHETICAL_ONLY_NOT_AUTHORIZED_OR_ADOPTED"
    assert row["condition_adopted"] is False
    assert row["native_selection_weight_now"] is False


def test_all_three_positions_are_open_and_unselected() -> None:
    paths = _report()["logical_paths"]
    assert [row["position"] for row in paths] == [
        "A_EXCLUDE_NEGATIVE_RESIDUE_SPIN2_ONLY",
        "B_REQUIRE_MINIMAL_MODE_CONTENT",
        "C_CHANGE_THEORY_CLASS",
    ]
    assert all(row["selected_now"] is False for row in paths)
    assert paths[0]["parameter_restriction"] == "beta=0"
    assert "alpha=beta=0" in paths[1]["parameter_restriction"]
    assert paths[2]["parameter_restriction"] == "NONE_IN_FAMILY"


def test_exact_approximate_meanings_cannot_be_interchanged() -> None:
    contract = _report()["exact_approximate_meaning_contract"]
    assert contract["meaning_count"] == len(contract["rows"]) == 6
    assert contract["interchange_allowed"] is False
    assert {row["status"] for row in contract["rows"]} == {
        "POLE_ABSENT_FINITE_PARAMETER_STRATUM",
        "INFINITE_MASS_DECOUPLING_LIMIT",
        "FINITE_RANGE_YUKAWA_SUPPRESSION",
        "EMPIRICAL_AGREEMENT_WITHIN_TOLERANCE",
        "SOURCE_NOT_EXCITING_MODE",
        "MODE_ABSENT_FROM_SPECTRUM",
    }


def test_nine_parameter_strata_include_all_special_surfaces() -> None:
    strata = _strata()
    assert len(strata) == 9
    for stratum_id in (
        "GENERIC_THREE_SECTOR",
        "SCALAR_ONLY",
        "SPIN2_ONLY",
        "EINSTEIN_BASELINE",
        "COINCIDENT_MASSES",
        "TACHYONIC_REGIONS",
        "HEAVY_MODE_LIMITS",
        "SINGULAR_OR_EXTRA_MASSLESS_LIMITS",
    ):
        assert stratum_id in strata
    assert "no double pole" in strata["COINCIDENT_MASSES"]["qualification"]
    assert "no" not in strata["COINCIDENT_MASSES"]["spectrum"].lower()


def test_scope_firewall_blocks_automatic_theory_family_transport() -> None:
    firewall = _report()["scope_firewall"]
    assert firewall["dimension"] == 4
    assert firewall["local_metric_quadratic_only"] is True
    assert firewall["outside_family_transport_allowed"] is False
    for token in (
        "nonlocal gravity",
        "torsion",
        "independent connection",
        "additional gauge symmetry",
    ):
        assert token in firewall["excluded_automatic_transports"]


def test_principal_outcomes_are_exclusive_and_subordinates_nonadopting() -> None:
    outcomes = _report()["outcome_contract"]
    assert tuple(outcomes["principal_outcomes"]) == packet.PRINCIPAL_OUTCOMES
    assert outcomes["exactly_one_principal_required_after_execution"] is True
    assert outcomes["principal_outcome_now"] is None
    assert tuple(outcomes["subordinate_findings"]) == packet.SUBORDINATE_FINDINGS
    assert outcomes["subordinate_findings_now"] == []
    assert outcomes["subordinate_findings_adopt_conditions"] is False


def test_selector_register_is_prepared_but_unexecuted() -> None:
    register = _report()["selector_register"]
    assert register["selector_count"] == 10
    assert register["adjudicated_count"] == register["adopted_count"] == 0
    assert all(row["selector_adjudication_status"] == "NOT_EXECUTED" for row in register["rows"])
    assert all(row["condition_adopted"] is False for row in register["rows"])


def test_sixteen_preparation_controls_pass() -> None:
    controls = _report()["preparation_controls"]
    assert controls["control_count"] == controls["pass_count"] == 16
    assert controls["failure_count"] == 0
    assert all(row["passed"] for row in controls["rows"])


def test_scope_stops_before_execution_adoption_and_downstream_work() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_executed"] is True
    for key, value in scope.items():
        if key != "packet_preparation_executed":
            assert value is False, key


def test_human_packet_exposes_authority_logic_strata_and_stop() -> None:
    text = (REPO_ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "R9_MOMENTUM_CURRENT",
        "R10_STABILITY_NO_FIT",
        "S3_NO_EXTRA_GRAVITATIONAL_MODES",
        "SEL_NO_NEGATIVE_RESIDUE_SPIN2",
        "POLE_ABSENT_FINITE_PARAMETER_STRATUM",
        "COINCIDENT_MASSES",
        "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE",
        "selector adjudications:         0 / 10",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text

