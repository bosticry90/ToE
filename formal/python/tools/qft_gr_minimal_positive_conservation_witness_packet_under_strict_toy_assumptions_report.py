from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_obstruction_class_stabilization_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    POSITIVE_WITNESS_BRIDGE_LAW,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_20260614_v0"
)
PACKET_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_PREPARED_WITH_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_"
    "assumptions_prepared_no_source_admissibility_or_qft_gr_closure"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_positive_conservation_witness_packet_under_strict_"
    "toy_assumptions_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_"
    "assumptions_result_review"
)
ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_"
    "toy_assumptions"
)
IMMEDIATE_RETEST_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_"
    "post_retest_refinement_conservation_retest_refinement_refinement"
)
ORDINARY_REFINEMENT_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_refinement"
)
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction"
)
SOURCE_MAP_LADDER_TARGET = (
    "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
    "admissible_source"
)
OBSTRUCTION_STATUS = "stabilized_for_next_target_selection_not_resolved"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_20260614_v0.json"
    )
)
DEFAULT_MARKDOWN_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_REPORT_v0.md"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _toy_bridge_components() -> list[dict[str, Any]]:
    return [
        {
            "component": "allowed_weak_test_class",
            "component_id": "strict_toy_compact_support_smooth_test_vector_class_v0",
            "role": "Restricts weak conservation claims to a fixed compact-support smooth test-vector class.",
            "required_for_bridge": True,
            "status": "defined_for_packet_not_executed",
            "nonclaim": "Does not define a full QFT-GR test-object universe.",
        },
        {
            "component": "weak_pairing",
            "component_id": "strict_toy_source_test_pairing_v0",
            "role": "Supplies the toy bilinear pairing between the source object and allowed tests.",
            "required_for_bridge": True,
            "status": "defined_for_packet_not_executed",
            "nonclaim": "Does not resolve the broader weak-pairing-domain obstruction.",
        },
        {
            "component": "source_object",
            "component_id": "strict_toy_stress_energy_like_source_object_v0",
            "role": "Names the stress-energy-like object used only inside the strict toy witness lane.",
            "required_for_bridge": True,
            "status": "candidate_source_object_not_source_admissibility",
            "nonclaim": "Does not claim physical source admissibility.",
        },
        {
            "component": "divergence_pairing",
            "component_id": "strict_toy_weak_divergence_pairing_v0",
            "role": "Defines the weak-divergence pairing to be shown zero against allowed tests.",
            "required_for_bridge": True,
            "status": "defined_for_packet_not_executed",
            "nonclaim": "Does not prove weak conservation in this packet.",
        },
        {
            "component": "field_equation_residual",
            "component_id": "strict_toy_field_equation_residual_zero_v0",
            "role": "Records the residual-zero antecedent for the intended bridge implication.",
            "required_for_bridge": True,
            "status": "assumption_for_future_attempt",
            "nonclaim": "Does not derive a physical field equation.",
        },
        {
            "component": "divergence_identity",
            "component_id": "strict_toy_divergence_identity_assumption_v0",
            "role": "Records the divergence identity antecedent for the intended bridge implication.",
            "required_for_bridge": True,
            "status": "assumption_for_future_attempt",
            "nonclaim": "Does not prove the identity at full QFT-GR scope.",
        },
        {
            "component": "compact_support_no_boundary_condition",
            "component_id": "strict_toy_compact_support_no_boundary_condition_v0",
            "role": "Eliminates boundary terms inside the deliberately small witness scope.",
            "required_for_bridge": True,
            "status": "assumption_for_future_attempt",
            "nonclaim": "Does not discharge boundary terms outside the strict toy class.",
        },
        {
            "component": "pass_fail_inconclusive_criteria",
            "component_id": "strict_toy_positive_witness_decision_criteria_v0",
            "role": "Defines how the later witness attempt may pass, fail, or remain inconclusive.",
            "required_for_bridge": True,
            "status": "criteria_defined_for_future_attempt",
            "nonclaim": "Does not execute or adjudicate the witness attempt.",
        },
    ]


def _bridge_law_steps() -> list[dict[str, str]]:
    return [
        {
            "step": "field_equation_residual_zero",
            "role": "antecedent",
            "statement": "The toy field-equation residual is zero under the strict assumptions.",
        },
        {
            "step": "divergence_identity",
            "role": "antecedent",
            "statement": "The toy source object satisfies the supplied divergence identity.",
        },
        {
            "step": "allowed_weak_pairing",
            "role": "antecedent",
            "statement": "All pairings are restricted to the allowed weak test class.",
        },
        {
            "step": "no_boundary_compact_support_condition",
            "role": "antecedent",
            "statement": "Compact support/no-boundary conditions remove boundary terms.",
        },
        {
            "step": "weak_conservation_against_allowed_tests",
            "role": "consequence_for_future_attempt",
            "statement": "The weak-divergence pairing vanishes against every allowed test.",
        },
    ]


def _decision_criteria() -> dict[str, str]:
    return {
        "pass": (
            "The later witness attempt proves that residual zero plus the "
            "divergence identity plus allowed weak pairing plus compact-support/"
            "no-boundary assumptions imply zero weak-divergence pairing for "
            "every allowed test."
        ),
        "fail": (
            "The later witness attempt produces an explicit strict-toy "
            "counterexample, nonzero weak-divergence pairing, missing required "
            "identity, or invalid pairing under the stated assumptions."
        ),
        "inconclusive": (
            "The later witness attempt cannot complete the implication because "
            "the pairing, test class, source object, divergence identity, or "
            "no-boundary assumptions remain insufficiently specified."
        ),
    }


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The prepared packet must be result-reviewed before any witness attempt.",
        },
        {
            "target": ATTEMPT_TARGET,
            "decision": "not_authorized_until_packet_review",
            "reason": "This packet prepares the strict toy witness lane but does not execute it.",
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "retained_follow_on_after_positive_witness_work",
            "reason": "Countermodel pressure remains a follow-on after the positive witness packet path.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_after_countermodel_pressure",
            "reason": "Source-map ladder reconstruction remains later follow-on work.",
        },
        {
            "target": IMMEDIATE_RETEST_TARGET,
            "decision": "not_authorized",
            "reason": "The decision-forcing pivot forbids another immediate conservation retest.",
        },
        {
            "target": ORDINARY_REFINEMENT_TARGET,
            "decision": "not_authorized",
            "reason": "The decision-forcing pivot forbids ordinary same-shaped refinement.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The packet is a strict toy witness packet, not a source admissibility claim.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The packet prepares a future witness attempt but proves no conservation theorem.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized_by_packet",
            "reason": "Witness construction is reserved for a later execution target if review authorizes it.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains outside the strict toy packet.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The packet does not derive or invoke a semiclassical Einstein equation.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains out of scope.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def render_markdown(payload: dict[str, Any]) -> str:
    component_lines = [
        (
            f"| {row['component']} | {row['component_id']} | "
            f"{row['status']} |"
        )
        for row in payload["strict_toy_bridge_components"]
    ]
    law_lines = [
        f"| {row['step']} | {row['role']} | {row['statement']} |"
        for row in payload["law_shaped_bridge_steps"]
    ]
    criteria = payload["pass_fail_inconclusive_criteria"]
    return (
        "# QFT-GR Minimal Positive Conservation Witness Packet Under Strict Toy Assumptions\n\n"
        f"- Packet: `{payload['packet_id']}`\n"
        f"- Outcome: `{payload['outcome_id']}`\n"
        f"- Consumed target: `{payload['consumed_target']}`\n"
        f"- Selected next target: `{payload['selected_next_target']}`\n"
        f"- Bridge law scope: `{payload['positive_witness_bridge_law_scope']}`\n\n"
        "## Strict Toy Bridge Components\n\n"
        "| Component | Component ID | Status |\n"
        "|---|---|---|\n"
        + "\n".join(component_lines)
        + "\n\n"
        "## Law-Shaped Bridge\n\n"
        "| Step | Role | Statement |\n"
        "|---|---|---|\n"
        + "\n".join(law_lines)
        + "\n\n"
        "## Decision Criteria For Future Attempt\n\n"
        f"- Pass: {criteria['pass']}\n"
        f"- Fail: {criteria['fail']}\n"
        f"- Inconclusive: {criteria['inconclusive']}\n\n"
        "## Nonclaim Boundary\n\n"
        f"{payload['non_claim_boundary']}\n"
    )


def build_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    components = _toy_bridge_components()
    criteria = _decision_criteria()
    candidate_next_targets = _candidate_next_targets()

    required_components = {
        "allowed_weak_test_class",
        "weak_pairing",
        "source_object",
        "divergence_pairing",
        "field_equation_residual",
        "divergence_identity",
        "compact_support_no_boundary_condition",
        "pass_fail_inconclusive_criteria",
    }
    component_names = {row["component"] for row in components}

    acceptance_criteria = {
        "consumes_expected_obstruction_result_review": (
            review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
        ),
        "result_review_selected_this_packet": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "result_review_authorized_positive_witness_packet_only": (
            review.get("positive_witness_packet_authorized") is True
            and review.get("positive_witness_attempt_authorized") is False
            and review.get("immediate_retest_authorized") is False
            and review.get("ordinary_model_refinement_authorized") is False
        ),
        "obstruction_candidate_carried_unresolved": (
            review.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and review.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and review.get("obstruction_status") == OBSTRUCTION_STATUS
            and review.get("dominant_obstruction_resolved") is False
            and review.get("mathematical_resolution_claimed") is False
        ),
        "strict_toy_bridge_components_complete": required_components
        == component_names
        and all(row["required_for_bridge"] is True for row in components),
        "bridge_law_scope_matches_authorized_scope": (
            review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "pass_fail_inconclusive_criteria_defined": set(criteria) == {
            "pass",
            "fail",
            "inconclusive",
        }
        and all(criteria.values()),
        "packet_selects_result_review_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "witness_attempt_not_executed_or_authorized_by_packet": True,
        "no_immediate_retest_or_ordinary_refinement": True,
        "nonclaims_preserved": True,
    }
    prepared = all(acceptance_criteria.values())

    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_TOY_ASSUMPTIONS_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_model_obstruction_class_stabilization_packet_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_model_obstruction_class_stabilization_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "strict_toy_assumptions_only": True,
        "packet_preparation_only": True,
        "positive_witness_packet_prepared": prepared,
        "positive_witness_attempt_authorized_by_packet": False,
        "positive_witness_attempt_executed": False,
        "conservation_retest_rerun_authorized": False,
        "immediate_retest_authorized": False,
        "ordinary_model_refinement_authorized": False,
        "countermodel_lane_retained_as_follow_on": True,
        "countermodel_packet_prepared": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_prepared": False,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "strict_toy_bridge_components": components,
        "strict_toy_bridge_component_count": len(components),
        "law_shaped_bridge_steps": _bridge_law_steps(),
        "law_shaped_bridge_summary": (
            "field-equation residual zero + divergence identity + allowed weak "
            "pairing + compact-support/no-boundary condition implies weak "
            "conservation against allowed tests, but only as the law-shaped "
            "target for a future strict toy witness attempt."
        ),
        "allowed_weak_test_class_id": (
            "strict_toy_compact_support_smooth_test_vector_class_v0"
        ),
        "weak_pairing_id": "strict_toy_source_test_pairing_v0",
        "source_object_id": "strict_toy_stress_energy_like_source_object_v0",
        "divergence_pairing_id": "strict_toy_weak_divergence_pairing_v0",
        "field_equation_residual_id": "strict_toy_field_equation_residual_zero_v0",
        "divergence_identity_id": "strict_toy_divergence_identity_assumption_v0",
        "no_boundary_condition_id": "strict_toy_compact_support_no_boundary_condition_v0",
        "pass_fail_inconclusive_criteria": criteria,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
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
        "aggregate_lean_timeout_caveat_preserved": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": {
            "checkpoint_type": "routine_positive_conservation_witness_packet_preparation_under_strict_toy_assumptions",
            "full_pytest_required": False,
            "full_governance_suite_required": False,
            "full_aggregate_lean_required": False,
            "full_ci_parity_required": False,
            "full_security_scan_required": False,
            "aggregate_lean_health_claimed": False,
        },
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET if prepared else "requires_remediation",
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if prepared else 0,
        "selection_count": 1 if prepared else 0,
        "packet_report_markdown": _ptr(DEFAULT_MARKDOWN_OUT),
        "acceptance_criteria": acceptance_criteria,
        "why_this_is_not_source_admissibility": [
            "The toy source object is not certified as a physical or semiclassical source.",
            "The unresolved weak-pairing-domain obstruction is carried as unresolved.",
            "Bianchi compatibility, known-limit recovery, and source-map admissibility are not claimed.",
        ],
        "why_this_is_not_qft_gr_closure": [
            "The packet prepares only a strict toy witness lane.",
            "No witness attempt is executed here.",
            "No conservation proof object, source admissibility proof, or Einstein-like equation is constructed.",
        ],
        "non_claim_boundary": (
            "This packet prepares only a strict toy positive conservation witness "
            "packet. It defines the allowed weak test class, weak pairing, "
            "source object, divergence pairing, field-equation residual, "
            "divergence identity, compact-support/no-boundary condition, and "
            "future pass/fail/inconclusive criteria. It does not execute the "
            "witness attempt, does not construct a conservation proof object or "
            "conservation witness, does not claim source admissibility, does "
            "not claim Bianchi compatibility, does not derive a semiclassical "
            "Einstein equation, does not close QFT-GR, does not validate "
            "empirically, does not authorize public submission, and does not "
            "promote the master action."
        ),
    }
    return payload


def write_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    markdown_out: Path = DEFAULT_MARKDOWN_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions(
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
            "Generate the QFT-GR minimal positive conservation witness packet "
            "under strict toy assumptions."
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
    payload = write_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions(
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
                "prepared": payload["prepared"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
