from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_maturation_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_20260614_v0"
)
PACKET_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_PREPARED_WITH_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction_prepared_with_no_source_admissibility_or_qft_gr_closure"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction_result_review"
)
COUNTERMODEL_ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_"
    "obstruction"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_20260614_v0.json"
    )
)
DEFAULT_MARKDOWN_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_REPORT_v0.md"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelCountermodelPacketForWeakConservationObstruction.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _countermodel_pressure_scope() -> list[dict[str, str]]:
    return [
        {
            "scope_id": "strict_toy_witness_preservation",
            "status": "preserved_not_refuted",
            "description": (
                "The accepted strict toy witness remains valid only under its "
                "explicit assumptions and is not undone by this packet."
            ),
        },
        {
            "scope_id": "broader_candidate_family_pressure",
            "status": "selected_for_countermodel_definition",
            "description": (
                "The packet asks where the broader candidate family fails or "
                "remains insufficient once strict toy assumptions are relaxed."
            ),
        },
        {
            "scope_id": "weak_pairing_obstruction_pressure",
            "status": "dominant_obstruction_candidate_not_resolved",
            "description": (
                "The retained weak-pairing obstruction is pressure-tested as a "
                "candidate obstruction, not treated as solved mathematics."
            ),
        },
    ]


def _countermodel_or_no_go_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion_id": "candidate_pairing_domain_undefined",
            "result_kind": "countermodel",
            "would_count_if": (
                "A broader candidate source/test pair is allowed by the packet "
                "scope but the weak pairing is undefined or non-total on that "
                "pair."
            ),
        },
        {
            "criterion_id": "allowed_test_exposes_nonzero_weak_divergence",
            "result_kind": "countermodel",
            "would_count_if": (
                "An allowed broader test object yields a nonzero weak "
                "divergence pairing for the candidate source while the strict "
                "toy antecedents are not available."
            ),
        },
        {
            "criterion_id": "derivative_exchange_not_justified",
            "result_kind": "no_go_pressure",
            "would_count_if": (
                "The candidate requires moving derivatives or limits across "
                "the weak pairing, but the broader regularity assumptions do "
                "not justify that exchange."
            ),
        },
        {
            "criterion_id": "boundary_term_survives_without_compact_support",
            "result_kind": "countermodel_or_no_go_pressure",
            "would_count_if": (
                "Relaxing compact support/no-boundary assumptions leaves an "
                "uncontrolled boundary contribution that blocks weak "
                "conservation."
            ),
        },
        {
            "criterion_id": "divergence_identity_not_derivable",
            "result_kind": "no_go_pressure",
            "would_count_if": (
                "The candidate source definition is too weak to derive the "
                "divergence identity that the positive toy witness supplied "
                "as an antecedent."
            ),
        },
        {
            "criterion_id": "test_vector_class_mismatch",
            "result_kind": "countermodel_or_no_go_pressure",
            "would_count_if": (
                "The candidate is conserved only against the strict toy test "
                "class and fails or becomes undefined for the broader intended "
                "test-vector class."
            ),
        },
        {
            "criterion_id": "curvature_coupling_leaves_uncancelled_term",
            "result_kind": "countermodel_or_no_go_pressure",
            "would_count_if": (
                "Adding the intended curvature-coupling context creates a term "
                "that is not cancelled by the current candidate source "
                "definition."
            ),
        },
    ]


def _attempt_classifications() -> list[dict[str, str]]:
    return [
        {
            "classification": (
                "qft_gr_minimal_model_countermodel_for_weak_conservation_"
                "obstruction_achieved_pending_result_review"
            ),
            "meaning": (
                "An explicit allowed broader candidate/test configuration "
                "shows nonzero weak divergence, undefined pairing, or another "
                "declared countermodel criterion."
            ),
        },
        {
            "classification": (
                "qft_gr_minimal_model_no_go_pressure_for_weak_conservation_"
                "obstruction_identified_pending_result_review"
            ),
            "meaning": (
                "The attempt does not produce a concrete counterexample but "
                "identifies a precise insufficiency such as unjustified "
                "derivative exchange or non-derivable divergence identity."
            ),
        },
        {
            "classification": (
                "qft_gr_minimal_model_countermodel_attempt_inconclusive_"
                "requires_assumption_or_source_map_stabilization"
            ),
            "meaning": (
                "The attempt cannot decide the broader candidate family "
                "because the assumptions or source-map interfaces remain "
                "underspecified."
            ),
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "This checkpoint prepares the countermodel packet only, so the "
                "next action is bounded packet result review."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The countermodel packet preparation target is consumed here.",
        },
        {
            "target": COUNTERMODEL_ATTEMPT_TARGET,
            "decision": "not_authorized_until_packet_review",
            "reason": "No countermodel attempt is authorized by packet preparation alone.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected",
            "reason": "Source-map ladder work remains downstream of countermodel review.",
        },
        {
            "target": "execute_immediate_conservation_retest",
            "decision": "not_authorized",
            "reason": "The decision-forcing pivot still forbids another immediate retest.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The packet cannot establish source admissibility.",
        },
        {
            "target": "claim_broad_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The strict toy witness is not broadened by packet preparation.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "A countermodel packet is not QFT-GR closure.",
        },
        {
            "target": "promote_master_action",
            "decision": "not_authorized",
            "reason": "No master-action promotion is authorized.",
        },
    ]


def _validation_policy(result_review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "routine_qft_gr_minimal_model_countermodel_packet_preparation"
        ),
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
        "inherited_maturation_result_review_validation_policy": result_review.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(result_review)
    criteria = _countermodel_or_no_go_criteria()
    attempt_classifications = _attempt_classifications()
    pressure_scope = _countermodel_pressure_scope()

    acceptance_criteria = {
        "consumes_expected_maturation_result_review": (
            result_review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and result_review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and result_review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
            and result_review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "strict_toy_witness_preserved_not_refuted": (
            result_review.get("strict_toy_witness_accepted") is True
            and result_review.get("local_conservation_bridge_witness_accepted")
            is True
            and result_review.get("strict_toy_scope_accepted") is True
            and result_review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "countermodel_scope_targets_broader_candidate_family": (
            len(pressure_scope) == 3
            and pressure_scope[0]["status"] == "preserved_not_refuted"
            and pressure_scope[1]["status"]
            == "selected_for_countermodel_definition"
        ),
        "countermodel_or_no_go_criteria_defined": (
            len(criteria) == 7
            and {
                row["criterion_id"]
                for row in criteria
            }
            == {
                "candidate_pairing_domain_undefined",
                "allowed_test_exposes_nonzero_weak_divergence",
                "derivative_exchange_not_justified",
                "boundary_term_survives_without_compact_support",
                "divergence_identity_not_derivable",
                "test_vector_class_mismatch",
                "curvature_coupling_leaves_uncancelled_term",
            }
        ),
        "attempt_classifications_are_bounded": (
            len(attempt_classifications) == 3
            and all(
                any(
                    marker in row["classification"]
                    for marker in ["achieved", "no_go_pressure", "inconclusive"]
                )
                for row in attempt_classifications
            )
        ),
        "obstruction_candidate_carried_unresolved": (
            result_review.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and result_review.get("canonical_obstruction_id")
            == CANONICAL_OBSTRUCTION_ID
            and result_review.get("obstruction_status") == OBSTRUCTION_STATUS
            and result_review.get("dominant_obstruction_resolved") is False
            and result_review.get("mathematical_resolution_claimed") is False
        ),
        "selects_packet_review_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "does_not_execute_or_claim_countermodel": (
            result_review.get("countermodel_packet_authorized") is True
            and result_review.get("countermodel_packet_prepared") is False
        ),
        "no_source_admissibility_or_broad_conservation": (
            result_review.get("source_admissibility_claimed") is False
            and result_review.get("source_admissibility_can_be_considered") is False
            and result_review.get("conservation_claimed") is False
            and result_review.get("full_qft_gr_conservation_claimed") is False
            and result_review.get("unbounded_conservation_proved") is False
        ),
        "no_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            result_review.get("Bianchi_compatibility_claimed") is False
            and result_review.get("semiclassical_einstein_equation_derived")
            is False
            and result_review.get("qft_gr_seam_closed") is False
            and result_review.get("empirical_validation_claimed") is False
            and result_review.get("public_submission_authorized") is False
            and result_review.get("master_action_promoted") is False
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
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_OBSTRUCTION"
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "packet_prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
            "OBSTRUCTION_REQUIRES_REMEDIATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
            "obstruction_requires_remediation"
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumes_result_review_id": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "countermodel_packet_prepared": accepted,
        "countermodel_packet_scope": (
            "broader_candidate_family_weak_conservation_obstruction_pressure"
        ),
        "countermodel_packet_is_not_strict_toy_witness_refutation": True,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": result_review.get("strict_toy_witness_accepted"),
        "strict_toy_scope_accepted": result_review.get("strict_toy_scope_accepted"),
        "strict_toy_assumptions_only": True,
        "accepted_bridge_is_local_only": True,
        "local_conservation_bridge_witness_accepted": result_review.get(
            "local_conservation_bridge_witness_accepted"
        ),
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "countermodel_pressure_scope": pressure_scope,
        "countermodel_or_no_go_criteria": criteria,
        "countermodel_or_no_go_criteria_count": len(criteria),
        "attempt_classifications": attempt_classifications,
        "attempt_classification_count": len(attempt_classifications),
        "countermodel_attempt_authorized": False,
        "countermodel_attempt_executed": False,
        "countermodel_result_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "inconclusive_result_claimed": False,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_authorized": False,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
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
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_packet_current_target_registry_gate": "required_for_checkpoint",
            "adjacent_qft_gr_nonclaim_gates": "required_bounded_subset",
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
            "required for this routine bounded countermodel-packet checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "markdown_report": _ptr(DEFAULT_MARKDOWN_OUT),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "acceptance_criteria": acceptance_criteria,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_"
            "CONSERVATION_OBSTRUCTION_RESULT_ONLY_NO_COUNTERMODEL_ATTEMPT_NO_"
            "SOURCE_ADMISSIBILITY_NO_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_"
            "CLOSURE_EMPIRICAL_VALIDATION_PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "non_claim_boundary": (
            "This packet defines countermodel and no-go criteria for the "
            "broader QFT-GR minimal-model candidate family under the retained "
            "weak-conservation obstruction. It does not refute the accepted "
            "strict toy witness, does not execute a countermodel attempt, and "
            "does not claim a countermodel, source admissibility, Bianchi "
            "compatibility, semiclassical Einstein equation, broad QFT-GR "
            "conservation, QFT-GR closure, empirical validation, public "
            "submission, or master-action promotion."
        ),
    }


def render_markdown(packet: dict[str, Any]) -> str:
    lines = [
        "# QFT-GR Minimal Model Countermodel Packet For Weak Conservation Obstruction v0",
        "",
        f"- Outcome: `{packet['outcome_id']}`",
        f"- Selected next target: `{packet['selected_next_target']}`",
        f"- Obstruction candidate: `{packet['dominant_obstruction_candidate']}`",
        "",
        "## Scope",
    ]
    for row in packet["countermodel_pressure_scope"]:
        lines.append(f"- `{row['scope_id']}`: {row['description']}")

    lines.extend(["", "## Countermodel Or No-Go Criteria"])
    for row in packet["countermodel_or_no_go_criteria"]:
        lines.append(
            f"- `{row['criterion_id']}` ({row['result_kind']}): "
            f"{row['would_count_if']}"
        )

    lines.extend(["", "## Attempt Classifications"])
    for row in packet["attempt_classifications"]:
        lines.append(f"- `{row['classification']}`: {row['meaning']}")

    lines.extend(["", "## Boundary", packet["non_claim_boundary"], ""])
    return "\n".join(lines)


def write_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    markdown_out: Path = DEFAULT_MARKDOWN_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_out.parent.mkdir(parents=True, exist_ok=True)
    markdown_out.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal model countermodel packet for the "
            "weak-conservation obstruction."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--markdown-out", type=Path, default=DEFAULT_MARKDOWN_OUT)
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
    markdown_out = (
        ns.markdown_out
        if ns.markdown_out.is_absolute()
        else (REPO_ROOT / ns.markdown_out)
    )
    payload = write_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        out=out,
        markdown_out=markdown_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "markdown_out": _ptr(markdown_out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "packet_prepared": payload["packet_prepared"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
