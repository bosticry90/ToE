from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import gr_field_equation_surface_failure_response_selection_v0 as selection


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_exactly_and_deterministically() -> None:
    assert selection.artifact_bytes() == selection.artifact_bytes() == REPORT_PATH.read_bytes()


def test_selection_preserves_all_frozen_authority_bytes() -> None:
    before = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    selection.build_selection()
    after = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    assert before == after == selection.AUTHORITY_HASHES


def test_selection_consumes_terminal_gr_failure_response_target() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == "SELECTED_GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE_PREPARATION"
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "PREPARATION_ONLY_NATIVE_GR_VARIATIONAL_SURFACE_EXISTENCE_OR_NO_GO"
    )


def test_native_variational_surface_route_ranks_first() -> None:
    ranking = _report()["ranking"]
    assert len(ranking["rows"]) == 3
    assert ranking["selected_candidate_id"] == "GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE"
    assert ranking["selected_score"] == 94
    assert ranking["runner_up_candidate_id"] == "GR_SUPPLIED_STANDARD_COMPARATOR"
    assert ranking["runner_up_score"] == 67


def test_selection_is_stable_in_all_twenty_four_weight_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == "GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE"
        for row in sensitivity["rows"]
    )


def test_terminal_gr_obstruction_is_retained_without_overstatement() -> None:
    obstruction = _report()["retained_gr_obstruction"]
    assert obstruction == {
        "GR01_bounded_discrete_Newton_Poisson_route": "RETAINED",
        "continuum_metric_tensor_field_equation": "NOT_DERIVED",
        "rotating_source_recovery": "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE",
        "stages_2_through_7_evaluated": False,
        "standard_GR_refuted": False,
        "ToE_native_gravitomagnetism_established": False,
    }


def test_packet_contract_covers_the_seven_required_native_surface_questions() -> None:
    obligation = _report()["selected_scientific_obligation"]
    assert obligation["pillar"] == "GR"
    assert obligation["obligation_class"] == (
        "NATIVE_CONTINUUM_VARIATIONAL_SURFACE_EXISTENCE_OR_NO_GO"
    )
    assert len(obligation["packet_must_freeze"]) == 7
    joined = "\n".join(obligation["packet_must_freeze"])
    for token in (
        "exactly one candidate action source",
        "one gravitational variable",
        "metric-dependence ledger",
        "boundary terms",
        "stress-energy definition",
        "C_k firewall",
        "Rep32 relationship",
    ):
        assert token in joined


def test_packet_has_four_scientifically_distinct_allowed_outcomes() -> None:
    outcomes = _report()["selected_scientific_obligation"]["allowed_outcomes"]
    assert outcomes == [
        "NATIVE_VARIATIONAL_SURFACE_EXISTS_PENDING_SEPARATE_CALCULATION",
        "SUPPLIED_STANDARD_GR_VARIATIONAL_COMPARATOR_ONLY",
        "NO_NATIVE_CONTINUUM_METRIC_ACTION_SURFACE",
        "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
    ]


def test_candidate_action_and_ck_postures_remain_nonpromotional() -> None:
    posture = _report()["candidate_action_posture"]
    assert posture["document_master_action"] == "WORKING_FORM_NONCANONICAL_NONPROMOTED"
    assert posture["ActionRep32"] == (
        "STRUCTURAL_FIRST_VARIATION_SCAFFOLD_NOT_ANALYTIC_METRIC_VARIATION"
    )
    assert posture["C_k"] == "ADMISSIBILITY_AUDIT_ONLY_NOT_VARIED"


def test_selection_authorizes_preparation_only() -> None:
    scope = _report()["scope_and_authorization"]
    assert scope == {
        "selection_executed": True,
        "packet_preparation_authorized": True,
        "packet_prepared_now": False,
        "metric_variation_executed": False,
        "tensor_field_equation_derived": False,
        "Einstein_equation_imported": False,
        "standard_GR_comparator_authorized": False,
        "rotating_source_lane_reopened": False,
        "gravitomagnetic_calculation_authorized": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_authorized": False,
        "master_action_promoted": False,
        "GR_pillar_completed": False,
        "seam_closed": False,
        "simulation_executed": False,
        "empirical_analysis_executed": False,
        "automation_created": False,
    }


def test_stopping_rule_forbids_downstream_derivation_and_tooling() -> None:
    stop = _report()["selected_scientific_obligation"]["stopping_rule"]
    for token in (
        "stop for independent review",
        "do not execute metric variation",
        "import the Einstein equation",
        "reactivate gravitomagnetism",
        "general symbolic tooling",
    ):
        assert token in stop
