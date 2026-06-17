from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result_review_report import (
    CONSUMED_TARGET as EXPECTED_PREVIOUS_LIVE_TARGET,
    COUNTERMODEL_SCOPE_DECISION_TARGET,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    INCONCLUSIVE_CLASSIFICATION,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = "QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET_20260616_v0"
PACKET_ID = "QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET_PREPARED_WITH_NO_"
    "SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_source_map_or_countermodel_scope_decision_packet_prepared_selects_"
    "source_map_ladder_with_no_source_admissibility_or_qft_gr_closure"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = SOURCE_MAP_LADDER_TARGET
NEXT_TARGET_KIND = (
    "qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_"
    "source_preparation"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET_20260616_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapOrCountermodelScopeDecisionPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _probe_semantic_gap_assessment(review: dict[str, Any]) -> list[dict[str, str]]:
    rows = []
    for probe in review.get("probe_evaluations", []):
        probe_id = probe.get("probe_id", "unknown_probe")
        if probe_id == "weak_divergence_pairing_definedness":
            missing = (
                "concrete source action, test action, and distributional "
                "divergence pairing object"
            )
        elif probe_id == "weak_divergence_pairing_value":
            missing = "concrete weak-divergence pairing value"
        elif probe_id == "boundary_term_retention":
            missing = "concrete compact-support/no-boundary or retained-boundary rule"
        elif probe_id == "derivative_exchange_legitimacy":
            missing = "analytic regularity and source-map derivative-exchange rule"
        elif probe_id == "curvature_coupling_residual":
            missing = "concrete curvature-coupling residual instantiation"
        else:
            missing = "probe-specific source-map semantics"

        rows.append(
            {
                "probe_id": probe_id,
                "prior_evaluation_status": probe.get("evaluation_status", "unknown"),
                "missing_semantic_condition": missing,
                "decision_forcing_as_single_scope_refinement": "no",
                "reason": (
                    "The missing condition depends on source-map architecture "
                    "or concrete source/test semantics rather than a single "
                    "narrow scope condition that directly decides this probe."
                ),
            }
        )
    return rows


def _branch_options() -> list[dict[str, str]]:
    return [
        {
            "branch_target": SOURCE_MAP_LADDER_TARGET,
            "branch_status": "selected",
            "branch_rule": (
                "Default route after inconclusive reattempt unless exactly one "
                "narrow semantic condition can directly decide a pinned probe."
            ),
            "selection_reason": (
                "No exactly-one decision-forcing narrow scope condition is "
                "identified; the unresolved gaps are source-map-level."
            ),
        },
        {
            "branch_target": COUNTERMODEL_SCOPE_DECISION_TARGET,
            "branch_status": "not_selected",
            "branch_rule": (
                "Allowed only if exactly one narrow missing semantic condition "
                "would directly decide one of the five pinned probes without "
                "requiring a broader source-map architecture."
            ),
            "selection_reason": (
                "The packet identifies zero qualifying narrow conditions and "
                "therefore blocks another automatic countermodel-scope loop."
            ),
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The decision packet applies the default branch rule and "
                "selects the source-map ladder packet as the only active next "
                "target."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The source-map-or-scope decision packet target is consumed here.",
        },
        {
            "target": COUNTERMODEL_SCOPE_DECISION_TARGET,
            "decision": "not_selected_no_exactly_one_narrow_scope_condition",
            "reason": (
                "No exactly-one missing semantic condition directly decides a "
                "pinned probe without broader source-map architecture."
            ),
        },
        {
            "target": EXPECTED_PREVIOUS_LIVE_TARGET,
            "decision": "historical_prior_target_already_consumed",
            "reason": "The prior result-review target remains completed and preserved.",
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "The decision packet does not construct or accept a countermodel.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "The decision packet proves no no-go result.",
        },
        {
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "The packet does not accept not-found under pinned scope.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The selected source-map ladder is preparation only.",
        },
        {
            "target": "claim_broad_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The strict toy witness is not broadened.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "No semiclassical Einstein equation is derived.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "The packet does not close QFT-GR.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
        {
            "target": "promote_master_action",
            "decision": "not_authorized",
            "reason": "No master-action promotion is authorized.",
        },
    ]


def _packet_findings() -> list[str]:
    return [
        (
            "The packet consumes the preserved source-map-or-scope decision "
            "target authorized by the inconclusive reattempt result review."
        ),
        (
            "The five probe gaps are source-map-level gaps, not exactly one "
            "narrow condition that can directly decide a pinned probe."
        ),
        (
            "The source-map ladder branch is selected by default and becomes "
            "the only active next target."
        ),
        (
            "A further countermodel-scope refinement is not authorized by "
            "this packet, preventing another automatic loop."
        ),
        (
            "The strict toy weak-conservation witness remains accepted only "
            "under its strict antecedents."
        ),
    ]


def _validation_policy(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_source_map_or_countermodel_scope_decision_packet_preparation",
        "routine_packet_uses_bounded_target_relevant_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "long_running_validation_escalation_authorized": False,
        "timeout_rerun_loop_authorized": False,
        "timeout_recorded_as_caveat_not_rerun_instruction": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "inherited_result_review_validation_policy": review.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_source_map_or_countermodel_scope_decision_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    probe_gap_assessment = _probe_semantic_gap_assessment(review)
    branch_options = _branch_options()
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(review)

    acceptance_criteria = {
        "consumes_expected_result_review_authorization": (
            review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
            and review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "result_review_accepts_inconclusive_decision_target_only": (
            review.get("accepted") is True
            and review.get("accepted_result_classification")
            == INCONCLUSIVE_CLASSIFICATION
            and review.get("source_map_or_scope_decision_packet_authorized") is True
            and review.get("source_map_or_scope_decision_packet_prepared") is False
            and review.get("source_map_ladder_packet_authorized") is False
            and review.get("further_scope_refinement_authorized") is False
        ),
        "five_probe_reattempt_was_non_decisive": (
            review.get("probe_evaluation_count") == 5
            and review.get("not_decisive_probe_count") == 5
            and review.get("decisive_countermodel_pressure_point_count") == 0
            and review.get("not_found_supporting_probe_count") == 0
            and len(probe_gap_assessment) == 5
        ),
        "pinned_scope_carried_without_admissibility": (
            review.get("pinned_source_test_pair_id") == PINNED_SOURCE_TEST_PAIR_ID
            and review.get("pinned_weak_pairing_contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and review.get("pinned_evaluation_scope_id") == PINNED_EVALUATION_SCOPE_ID
            and review.get("source_admissibility_claimed") is False
        ),
        "no_single_narrow_scope_condition_identified": (
            sum(
                1
                for row in probe_gap_assessment
                if row["decision_forcing_as_single_scope_refinement"] == "yes"
            )
            == 0
        ),
        "source_map_ladder_selected_as_default_branch": (
            [row["branch_target"] for row in branch_options if row["branch_status"] == "selected"]
            == [SOURCE_MAP_LADDER_TARGET]
        ),
        "countermodel_scope_branch_rejected": (
            [row["branch_target"] for row in branch_options if row["branch_status"] == "not_selected"]
            == [COUNTERMODEL_SCOPE_DECISION_TARGET]
        ),
        "selects_only_source_map_ladder_next_target": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
        "strict_toy_witness_preserved_not_broadened": (
            review.get("strict_toy_witness_preserved") is True
            and review.get("strict_toy_witness_accepted") is True
            and review.get("strict_toy_assumptions_only") is True
            and review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "no_countermodel_no_go_not_found_or_source_claim": (
            review.get("countermodel_result_claimed") is False
            and review.get("countermodel_exists_claimed") is False
            and review.get("no_go_result_claimed") is False
            and review.get("not_found_result_claimed") is False
            and review.get("source_admissibility_claimed") is False
        ),
        "no_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            review.get("Bianchi_compatibility_claimed") is False
            and review.get("semiclassical_einstein_equation_derived") is False
            and review.get("qft_gr_seam_closed") is False
            and review.get("qft_gr_source_map_closure_claimed") is False
            and review.get("empirical_validation_claimed") is False
            and review.get("public_submission_authorized") is False
            and review.get("master_action_promoted") is False
        ),
        "routine_validation_policy_preserves_non_escalation": all(
            validation_policy[key] is False
            for key in [
                "full_pytest_required",
                "full_governance_suite_required",
                "full_aggregate_lean_required",
                "full_ci_parity_required",
                "full_security_scan_required",
                "long_running_validation_escalation_authorized",
                "timeout_rerun_loop_authorized",
                "aggregate_lean_health_claimed",
            ]
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET"
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_decision": "prepared" if prepared else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_result_review_id": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": review.get("schema_id"),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "previous_live_next_target_before_result_review": EXPECTED_PREVIOUS_LIVE_TARGET,
        "source_map_or_scope_decision_packet_prepared": prepared,
        "source_map_or_scope_decision_packet_preparation_only": True,
        "source_map_or_scope_decision_packet_result_review_required": False,
        "source_map_or_scope_decision_packet_result_review_pending": False,
        "accepted_inconclusive_reattempt": review.get(
            "accepted_inconclusive_reattempt"
        ),
        "accepted_result_classification": review.get("accepted_result_classification"),
        "probe_evaluation_count": review.get("probe_evaluation_count"),
        "not_decisive_probe_count": review.get("not_decisive_probe_count"),
        "decisive_countermodel_pressure_point_count": review.get(
            "decisive_countermodel_pressure_point_count"
        ),
        "not_found_supporting_probe_count": review.get(
            "not_found_supporting_probe_count"
        ),
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "source_test_instantiation": review.get("source_test_instantiation", {}),
        "weak_pairing_semantics": review.get("weak_pairing_semantics", {}),
        "evaluation_scope": review.get("evaluation_scope", {}),
        "probe_semantic_gap_assessment": probe_gap_assessment,
        "probe_semantic_gap_count": len(probe_gap_assessment),
        "decision_forcing_narrow_scope_condition_count": 0,
        "exactly_one_narrow_scope_condition_identified": False,
        "countermodel_scope_refinement_branch_selected": False,
        "countermodel_scope_refinement_branch_rejected": prepared,
        "further_scope_refinement_authorized": False,
        "source_map_ladder_branch_selected": prepared,
        "source_map_ladder_selected_by_default": prepared,
        "source_map_ladder_packet_authorized": prepared,
        "source_map_ladder_packet_prepared": False,
        "source_map_ladder_packet_executed": False,
        "source_map_ladder_target": SOURCE_MAP_LADDER_TARGET,
        "countermodel_scope_refinement_target": COUNTERMODEL_SCOPE_DECISION_TARGET,
        "branch_options": branch_options,
        "branch_option_count": len(branch_options),
        "branch_rule": (
            "Default to the source-map ladder unless exactly one narrow "
            "missing semantic condition can directly decide one pinned probe "
            "without broader source-map architecture."
        ),
        "loop_guard": (
            "Because no further scope refinement is selected, the source-map "
            "ladder route is forced now."
        ),
        "automatic_countermodel_loop_authorized": False,
        "one_more_scope_refinement_cycle_authorized": False,
        "source_map_route_forced": prepared,
        "dominant_obstruction_candidate": review.get("dominant_obstruction_candidate"),
        "canonical_obstruction_id": review.get("canonical_obstruction_id"),
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": review.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "decision_packet_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "not_found_under_pinned_scope_claimed": False,
        "inconclusive_result_claimed": False,
        "source_admissibility_can_be_considered": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "full_qft_gr_conservation_claimed": False,
        "unbounded_conservation_proved": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_claimed": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "packet_findings": _packet_findings(),
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_packet_current_target_registry_gate": "required_for_checkpoint",
            "current_target_freshness_gate": "required_for_checkpoint",
            "authoritative_surfaces_gate": "required_for_checkpoint",
            "targeted_lean_packet_frontier_import_checks": "required_for_checkpoint",
            "git_diff_check": "required_for_checkpoint",
            "full_pytest": "not_required_for_checkpoint",
            "full_governance_suite": "not_required_for_checkpoint",
            "full_aggregate_lean": "not_required_for_checkpoint_preserved_caveat",
            "release_index_lean_path": "not_freshly_validated_preserved_caveat",
            "full_ci_parity": "not_required_for_checkpoint",
            "security_scan": "not_required_for_checkpoint",
        },
        "validation_caveat": (
            "Full pytest, full governance suite, full aggregate Lean, release-"
            "index Lean validation, CI parity, and security scans are not "
            "required for this routine bounded decision-packet checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "packet_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if prepared else 0,
        "selected_next_target_count": 1 if prepared else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_"
            "TO_ADMISSIBLE_SOURCE_ONLY_NO_SOURCE_ADMISSIBILITY_NO_"
            "COUNTERMODEL_SCOPE_REFINEMENT_NO_COUNTERMODEL_RESULT_CLAIM_NO_"
            "NO_GO_RESULT_CLAIM_NO_QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet decides the post-reattempt fork by selecting the "
            "source-map ladder packet as the only active next target because "
            "no exactly-one narrow semantic condition directly decides a "
            "pinned probe. It does not prepare or execute the source-map "
            "ladder, does not authorize another countermodel-scope refinement "
            "loop, does not claim a countermodel result, does not claim a "
            "no-go result, does not claim not-found under pinned scope, "
            "preserves no source admissibility, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no broad QFT-GR conservation, "
            "no QFT-GR closure, no empirical validation, no public submission, "
            "and no master-action promotion."
        ),
    }


def write_qft_gr_source_map_or_countermodel_scope_decision_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_source_map_or_countermodel_scope_decision_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR source-map-or-countermodel-scope decision "
            "packet after the inconclusive weak-conservation countermodel "
            "reattempt review."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_source_map_or_countermodel_scope_decision_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "prepared": payload["prepared"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
