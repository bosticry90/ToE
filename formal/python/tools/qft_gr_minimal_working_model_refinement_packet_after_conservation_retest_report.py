from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SELECTED_REFINEMENT_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-13T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_AFTER_CONSERVATION_RETEST_PACKET_"
    "20260613_v0"
)
PACKET_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_AFTER_CONSERVATION_RETEST_PACKET_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_AFTER_CONSERVATION_RETEST_PACKET_"
    "PREPARED_WITH_NO_SOURCE_ADMISSIBILITY_OR_CONSERVATION_PROOF"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_working_model_refinement_after_conservation_retest_packet_"
    "prepared_pending_result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_packet_after_conservation_"
    "retest_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_refinement_after_conservation_retest_packet_"
    "result_review"
)
REFINEMENT_OBJECTIVE = SELECTED_REFINEMENT_TARGET
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_AFTER_CONSERVATION_RETEST_"
        "PACKET_20260613_v0.json"
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


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The post-retest refinement packet must be reviewed before any "
                "refinement attempt, conservation rerun, countermodel packet, "
                "source-admissibility claim, or model promotion is authorized."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This post-retest refinement packet preparation target is consumed here.",
        },
        {
            "target": "execute_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest",
            "decision": "not_authorized_before_packet_result_review",
            "reason": "The packet identifies refinement dimensions only; it does not execute refinement.",
        },
        {
            "target": "retry_qft_gr_minimal_working_model_conservation_retest",
            "decision": "not_authorized_before_refinement_attempt",
            "reason": "The packet does not rerun or convert the inconclusive retest.",
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_countermodel_packet_after_conservation_retest",
            "decision": "not_selected_no_failed_retest_obstruction",
            "reason": "No explicit failed-conservation obstruction was recorded by the retest review.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains a candidate only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The packet contains no conservation proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains outside this packet.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _refinement_dimensions() -> list[dict[str, Any]]:
    return [
        {
            "dimension_id": "post_retest_weak_pairing_domain",
            "scope": "weak_pairing_domain",
            "attempted_refinement": (
                "Move from the recorded toy_weak_pairing_domain_v1 context to "
                "an explicitly stated candidate pairing domain for weak "
                "covariant-divergence pairings, without asserting source-domain "
                "membership."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "post_retest_regular_context",
            "scope": "regularity_assumptions",
            "attempted_refinement": (
                "Separate derivative-exchange, boundary-term, and limit/"
                "interchange assumptions needed by the toy weak pairings, "
                "without treating them as discharged."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "post_retest_test_function_class",
            "scope": "test_function_class",
            "attempted_refinement": (
                "Name the admissible test-vector or compact-support class "
                "against which the toy candidate can be paired in a later "
                "attempt."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "post_retest_candidate_source_definition",
            "scope": "candidate_source_definition",
            "attempted_refinement": (
                "Clarify the toy source-candidate definition as a candidate "
                "object only, preserving the distinction between candidate "
                "existence and admissible conserved source status."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "post_retest_scope_restriction",
            "scope": "scope_restriction",
            "attempted_refinement": (
                "Restrict any later attempt to the bounded toy weak-pairing "
                "setting unless a reviewed packet authorizes a broader scope."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "post_retest_obstruction_accounting",
            "scope": "obstruction_accounting",
            "attempted_refinement": (
                "Preserve the inconclusive retest as an obstruction map rather "
                "than converting it into a conservation pass or failure."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "post_retest_nonpromotion_gate",
            "scope": "governance_boundary",
            "attempted_refinement": (
                "Require packet result review before any refinement attempt, "
                "conservation retest, countermodel packet, source-admissibility "
                "claim, or promotion."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
    ]


def _review_gate_requirements() -> list[str]:
    return [
        "consume this post-retest refinement packet artifact",
        "confirm the selected refinement objective exactly",
        "confirm the packet is preparation only",
        "confirm the weak pairing domain dimension is identified but not discharged",
        "confirm the regularity assumptions are identified but not discharged",
        "confirm the test-function class is identified but not used as a conservation proof",
        "confirm the candidate source definition remains candidate-only",
        "confirm the scope restriction remains bounded to the toy weak-pairing setting",
        "confirm no conservation retest is rerun",
        "confirm no conservation proof object or witness is constructed",
        "confirm no source admissibility is claimed",
        "confirm no Bianchi compatibility is claimed",
        "confirm no semiclassical Einstein equation is derived",
        "confirm no QFT-GR closure, empirical validation, public submission, or master-action promotion is authorized",
    ]


def build_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    candidate_next_targets = _candidate_next_targets()
    refinement_dimensions = _refinement_dimensions()
    selected_refinement_objectives = [REFINEMENT_OBJECTIVE]
    dimension_scopes = {row["scope"] for row in refinement_dimensions}

    acceptance_criteria = {
        "consumes_expected_conservation_retest_attempt_result_review": review.get(
            "schema_id"
        )
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID
        and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID,
        "result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "result_review_selected_this_packet": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "consumed_retest_classification_preserved": review.get(
            "consumed_attempt_classification"
        )
        == "qft_gr_minimal_working_model_conservation_retest_inconclusive_requires_model_refinement",
        "inconclusive_retest_not_converted": review.get(
            "accepted_inconclusive_result"
        )
        is True
        and review.get("retest_inconclusive") is True
        and review.get("retest_passed") is False
        and review.get("retest_failed") is False,
        "model_refinement_packet_authorized": review.get(
            "model_refinement_packet_authorized"
        )
        is True
        and review.get("model_refinement_packet_prepared_by_review") is False,
        "countermodel_not_selected": review.get("countermodel_packet_authorized")
        is False
        and review.get("countermodel_packet_prepared_by_review") is False,
        "selected_refinement_objective_matches_review": review.get(
            "selected_refinement_target"
        )
        == REFINEMENT_OBJECTIVE,
        "exactly_one_refinement_objective": selected_refinement_objectives
        == [REFINEMENT_OBJECTIVE],
        "post_retest_refinement_dimensions_recorded": dimension_scopes
        >= {
            "weak_pairing_domain",
            "regularity_assumptions",
            "test_function_class",
            "candidate_source_definition",
            "scope_restriction",
            "obstruction_accounting",
            "governance_boundary",
        },
        "review_gate_requirements_recorded": len(_review_gate_requirements()) >= 12,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed")
        is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": review.get(
            "conservation_claimed"
        )
        is False
        and review.get("conservation_proved") is False
        and review.get("conservation_proof_object_constructed") is False
        and review.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": review.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and review.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": review.get("qft_gr_seam_closed") is False
        and review.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": review.get(
            "empirical_validation_claimed"
        )
        is False
        and review.get("public_submission_authorized") is False,
        "no_master_action_promotion": review.get("master_action_promoted") is False
        and review.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_AFTER_"
            "CONSERVATION_RETEST_PACKET"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "packet_prepared": accepted,
        "packet_preparation_only": True,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_AFTER_CONSERVATION_"
            "RETEST_PACKET_REQUIRES_REMEDIATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_refinement_after_conservation_retest_"
            "packet_requires_remediation"
        ),
        "packet_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_retest_attempt_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_retest_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": review.get("schema_id"),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "consumed_retest_attempt_classification": review.get(
            "consumed_attempt_classification"
        ),
        "conservation_retest_attempt_result": review.get("retest_result"),
        "accepted_inconclusive_retest_result": review.get(
            "accepted_inconclusive_result"
        )
        is True,
        "inconclusive_retest_not_converted_to_pass": True,
        "inconclusive_retest_not_converted_to_failure": True,
        "refinement_objective": REFINEMENT_OBJECTIVE if accepted else "requires_remediation",
        "selected_refinement_target": (
            REFINEMENT_OBJECTIVE if accepted else "requires_remediation"
        ),
        "selected_refinement_target_count": 1 if accepted else 0,
        "refinement_focus": (
            "weak_pairing_domain_regular_context_test_function_class_"
            "candidate_definition_scope_restriction_after_inconclusive_retest"
        ),
        "refinement_dimensions": refinement_dimensions,
        "refinement_dimension_count": len(refinement_dimensions),
        "identified_refinement_scopes": sorted(dimension_scopes),
        "weak_pairing_domain_id": "toy_weak_pairing_domain_v1",
        "regularity_structure_id": "toy_regular_context_v1",
        "proposed_weak_pairing_domain_revision": "toy_weak_pairing_domain_v2_candidate",
        "proposed_regular_context_revision": "toy_regular_context_v2_candidate",
        "proposed_test_function_class": "toy_conservation_test_function_class_v1_candidate",
        "proposed_candidate_source_definition": "toy_source_candidate_definition_v2_candidate",
        "scope_restriction": "bounded_toy_candidate_weak_pairing_scope_only",
        "review_gate_requirements": _review_gate_requirements(),
        "model_refinement_packet_authorized": True,
        "model_refinement_packet_prepared": accepted,
        "model_refinement_packet_preparation_only": True,
        "model_refinement_executed": False,
        "refinement_attempt_executed": False,
        "countermodel_packet_authorized": False,
        "countermodel_packet_prepared": False,
        "conservation_retest_retried": False,
        "conservation_retest_executed_by_packet": False,
        "conservation_retest_result_claimed": False,
        "conservation_retest_pass_claimed": False,
        "conservation_retest_failure_claimed": False,
        "toy_source_candidate_status": "candidate_only_not_source_admissibility",
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
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
        "aggregate_lean_timeout_caveat_preserved": review.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": review.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_POST_RETEST_REFINEMENT_"
            "PACKET_RESULT_ONLY_NO_REFINEMENT_ATTEMPT_CONSERVATION_RETEST_"
            "COUNTERMODEL_PACKET_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_"
            "WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_"
            "EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only a post-retest refinement plan for the toy "
            "candidate after an inconclusive conservation retest. It identifies "
            "weak pairing domain, regularity assumptions, test-function class, "
            "candidate source definition, and scope restriction dimensions. It "
            "does not execute refinement, rerun conservation, claim "
            "conservation, construct a conservation proof object, construct a "
            "conservation witness, claim source admissibility, claim Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, authorize public submission, or "
            "promote the master action. Boundary shorthand: no source "
            "admissibility, no conservation proof object, no conservation "
            "witness, no Bianchi compatibility, no semiclassical Einstein "
            "equation, no QFT-GR closure, and no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest(
            result_review_path=result_review_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model post-retest refinement packet."
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
    payload = write_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_refinement_packet_after_conservation_retest_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
