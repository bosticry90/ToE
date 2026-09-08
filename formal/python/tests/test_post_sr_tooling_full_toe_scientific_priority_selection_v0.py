from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import post_sr_tooling_full_toe_scientific_priority_selection_v0 as selection


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_exactly_and_deterministically() -> None:
    first = selection.artifact_bytes()
    second = selection.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_selection_preserves_every_frozen_authority_byte() -> None:
    before = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    selection.build_selection()
    after = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    assert before == after == selection.AUTHORITY_HASHES


def test_selection_consumes_exact_full_priority_target() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == "SELECTED_DIRECT_GR_KNOWN_LIMIT_RECOVERY_PREPARATION"
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == "PREPARATION_ONLY_DIRECT_GR_PILLAR_RECOVERY"


def test_sr_convention_is_retained_as_policy_while_tooling_stays_closed() -> None:
    sr = _report()["sr_policy_closeout"]
    assert sr == {
        "physical_convention": "x^0=c t; g=diag(+1,-1,-1,-1); dimensionful target SI",
        "policy_status": "RETAINED_AS_BOUNDED_POLICY",
        "automated_restoration": "BLOCKED_SR_RESTORATION_TOOLING_CONTRACT",
        "equation_specific_review_required": True,
        "migration_executed": False,
        "v4_authorized": False,
    }


def test_scoring_policy_has_five_required_scientific_properties() -> None:
    policy = _report()["selection_policy"]
    assert policy["criterion_scale"] == "0..5"
    assert policy["maximum_weighted_score"] == 100
    assert len(policy["weights"]) == 8
    assert len(policy["required_target_properties"]) == 5
    assert "requires no new general-purpose tool or governance system" in policy["required_target_properties"]


def test_gr_rotating_source_recovery_ranks_first() -> None:
    ranking = _report()["ranking"]
    assert ranking["eligible_candidate_count"] == 6
    assert ranking["selected_candidate_id"] == "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY"
    assert ranking["selected_score"] == 93
    assert ranking["runner_up_candidate_id"] == "MASTER_ACTION_DISTINCTIVE_PREDICTION_FEASIBILITY_NO_GO"
    assert ranking["runner_up_score"] == 83
    assert ranking["rows"][0]["target"] == selection.SELECTED_NEXT_TARGET


def test_gr_selection_is_stable_under_all_weight_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY"
        for row in sensitivity["rows"]
    )


def test_closed_and_infrastructure_lanes_are_excluded() -> None:
    excluded = _report()["excluded_target_classes"]
    ids = {row["target_class"] for row in excluded}
    assert ids == {
        "R13_OR_MAXWELL_DIRAC_MECHANISM_CONTINUATION",
        "SR_RESTORATION_TOOLING_V4",
        "GENERAL_UNITS_REGISTRY_OR_CONVENTION_MIGRATION",
        "GFE_OR_OTHER_DORMANT_COMPARATOR_ADOPTION",
    }


def test_selected_obligation_has_direct_analytic_endpoints_and_negative_controls() -> None:
    obligation = _report()["selected_scientific_obligation"]
    assert obligation["pillar"] == "GR"
    assert obligation["obligation_class"] == "KNOWN_PHYSICS_RECOVERY"
    assert len(obligation["required_derivation_endpoints"]) == 5
    joined = "\n".join(obligation["required_derivation_endpoints"])
    for token in (
        "linearized stationary 0i field equation",
        "exterior g_0i",
        "without fitting its coefficient",
        "J=0",
        "J reversal",
        "supplied boundary, gauge, source, and approximation assumption",
    ):
        assert token in joined
    assert obligation["failure_result"] == "BOUNDED_NO_GO_OR_EXACT_SUPPLIED_ASSUMPTION_BLOCKER"


def test_stopping_rule_forbids_expansion_into_another_toolchain() -> None:
    stop = _report()["selected_scientific_obligation"]["stopping_rule"]
    assert "Prepare one derivation contract" in stop
    assert "stop for independent review" in stop
    assert "general symbolic framework" in stop


def test_lares_benchmark_is_reference_bound_without_empirical_activation() -> None:
    posture = _report()["benchmark_posture"]
    assert posture["GR-WEAK-ROTATING-SOURCE-BENCHMARK"] == (
        "REFERENCE_BOUND_FOR_SELECTED_GR_PREPARATION_ONLY"
    )
    assert posture["LARES_2_data_analysis_authorized"] is False
    assert posture["empirical_fit_authorized"] is False
    assert posture["modified_gravity_constraint_claim_authorized"] is False
    assert posture["other_external_comparators_remain_dormant"] is True


def test_selection_executes_no_derivation_simulation_or_empirical_analysis() -> None:
    scope = _report()["scope_and_authorization"]
    assert scope == {
        "selected_derivation_executed_now": False,
        "packet_preparation_authorized": True,
        "simulation_authorized": False,
        "empirical_analysis_authorized": False,
        "R13_reopened": False,
        "SR_tooling_reopened": False,
        "v4_authorized": False,
        "repository_migration_authorized": False,
        "new_general_purpose_tool_authorized": False,
        "pillar_completion_claimed": False,
        "seam_closure_claimed": False,
        "master_action_promoted": False,
        "automation_created": False,
    }
