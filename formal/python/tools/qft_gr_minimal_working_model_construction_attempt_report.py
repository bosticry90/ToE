from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_post_mr_assump004_governed_maturation_reports import (
    ACCEPTED_MR_ROWS,
    COMPLETED_FAMILIES_AFTER_MR,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-11T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_20260611_v0"
ATTEMPT_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_EXECUTED_WITH_NO_"
    "SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
RESULT_CLASSIFICATION = (
    "qft_gr_minimal_working_model_construction_attempt_executed_pending_result_review"
)
ALLOWED_RESULT_CLASSIFICATIONS = [
    "qft_gr_minimal_working_model_construction_attempt_executed_pending_result_review",
    "qft_gr_minimal_working_model_construction_obstruction_identified_requires_countermodel_or_scope_refinement",
    "qft_gr_minimal_working_model_construction_inconclusive_requires_model_scope_refinement",
]
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_working_model_construction_attempt_result"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_construction_attempt_result_review"
TOY_SOURCE_STATUS = "candidate_only_not_source_admissibility"
CONSTRUCTION_STATUS = "bounded_minimal_model_attempt_constructed_pending_result_review"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_20260611_v0.json"
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
                "The bounded construction attempt must be result-reviewed before "
                "any model interpretation, source-admissibility work, or closure "
                "claim."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The constructed object remains a toy source candidate only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The construction attempt records a conservation-test target but does not prove conservation.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by this attempt.",
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
            "reason": "QFT-GR closure remains outside this bounded construction attempt.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _bounded_minimal_model_attempt() -> dict[str, Any]:
    return {
        "attempt_model_id": "QFT_GR_MINIMAL_WORKING_MODEL_TOY_SOURCE_CANDIDATE_v0",
        "model_class": "free scalar-field stress-energy-like candidate",
        "background": {
            "geometry": "fixed smooth or distributionally controlled background",
            "backreaction": "excluded",
            "connection": "background-compatible derivative operator for weak tests",
        },
        "field_state_setup": {
            "field_object": "real scalar field placeholder on the controlled background",
            "state_object": "bounded state or expectation functional placeholder",
            "expectation_object": "finite expectation candidate under imported domain conditions",
        },
        "stress_energy_like_candidate": {
            "object": (
                "regularized_or_renormalized_expectation_of_scalar_"
                "stress_energy_like_tensor"
            ),
            "status": TOY_SOURCE_STATUS,
            "source_admissibility_claimed": False,
        },
        "imported_assumption_families": COMPLETED_FAMILIES_AFTER_MR,
        "imported_regularities": ACCEPTED_MR_ROWS,
        "construction_chain": [
            "field object",
            "state/expectation object",
            "stress-energy-like object",
            "regularized or renormalized candidate",
            "distributional pairing domain",
            "derivative/interchange conditions",
            "weak conservation test target",
            "source-admissibility candidate only",
        ],
        "weak_conservation_test_target": {
            "target": "weak tested divergence vanishing or explicit obstruction",
            "status": "test_target_recorded_not_proved",
            "conservation_claimed": False,
            "conservation_witness_constructed": False,
        },
        "candidate_only_boundary": {
            "source_admissibility_claimed": False,
            "physical_source_claimed": False,
            "source_map_closure_claimed": False,
        },
    }


def build_qft_gr_minimal_working_model_construction_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_result_review_path)
    candidate_next_targets = _candidate_next_targets()
    model_attempt = _bounded_minimal_model_attempt()
    classification_rows = [
        {
            "classification": ALLOWED_RESULT_CLASSIFICATIONS[0],
            "selected": True,
            "meaning": (
                "A bounded toy source-candidate construction attempt was "
                "recorded and must be result-reviewed before interpretation."
            ),
        },
        {
            "classification": ALLOWED_RESULT_CLASSIFICATIONS[1],
            "selected": False,
            "meaning": (
                "The construction route exposed an obstruction requiring a "
                "countermodel or scope refinement."
            ),
        },
        {
            "classification": ALLOWED_RESULT_CLASSIFICATIONS[2],
            "selected": False,
            "meaning": (
                "The construction route remained inconclusive and requires "
                "model-scope refinement."
            ),
        },
    ]
    acceptance_criteria = {
        "consumes_expected_packet_result_review": review.get("schema_id")
        == EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID
        and review.get("review_id") == EXPECTED_PACKET_RESULT_REVIEW_ID,
        "packet_result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
        "packet_result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
        "packet_result_review_selected_this_attempt": review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "construction_attempt_authorized": review.get(
            "bounded_model_construction_attempt_authorized"
        )
        is True,
        "review_did_not_execute_attempt": review.get(
            "bounded_model_construction_attempt_executed_by_review"
        )
        is False,
        "constructs_bounded_minimal_model_attempt_only": model_attempt["model_class"]
        == "free scalar-field stress-energy-like candidate"
        and model_attempt["background"]["backreaction"] == "excluded",
        "toy_source_candidate_remains_candidate_only": model_attempt[
            "stress_energy_like_candidate"
        ]["status"]
        == TOY_SOURCE_STATUS
        and model_attempt["stress_energy_like_candidate"][
            "source_admissibility_claimed"
        ]
        is False,
        "imports_completed_assumption_families": model_attempt[
            "imported_assumption_families"
        ]
        == COMPLETED_FAMILIES_AFTER_MR,
        "imports_mathematical_regularity_rows": model_attempt["imported_regularities"]
        == ACCEPTED_MR_ROWS,
        "classification_allowed": RESULT_CLASSIFICATION
        in ALLOWED_RESULT_CLASSIFICATIONS,
        "exactly_one_classification_selected": sum(
            1 for row in classification_rows if row["selected"]
        )
        == 1,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed")
        is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim": review.get("conservation_proved") is False,
        "no_conservation_witness": review.get("conservation_witness_constructed")
        is False,
        "no_bianchi_compatibility": review.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_equation": review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_closure": review.get("qft_gr_seam_closed") is False,
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
    executed = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": executed,
        "accepted": executed,
        "outcome_id": OUTCOME_ID
        if executed
        else "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_REQUIRES_REMEDIATION",
        "result_classification": RESULT_CLASSIFICATION
        if executed
        else "qft_gr_minimal_working_model_construction_attempt_requires_remediation",
        "result_classification_count": 1 if executed else 0,
        "allowed_result_classifications": ALLOWED_RESULT_CLASSIFICATIONS,
        "classification_rows": classification_rows,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_demonstration_packet_result_review": (
            EXPECTED_PACKET_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_demonstration_packet_result_review_pointer": _ptr(
            packet_result_review_path
        ),
        "consumed_packet_result_review_outcome_id": review.get("outcome_id"),
        "consumed_packet_result_review_classification": review.get(
            "result_review_classification"
        ),
        "bounded_minimal_model_attempt": model_attempt,
        "construction_status": CONSTRUCTION_STATUS,
        "construction_attempt_executed": executed,
        "construction_attempt_pending_result_review": executed,
        "bounded_model_construction_attempt_only": True,
        "toy_source_candidate_status": TOY_SOURCE_STATUS,
        "toy_source_candidate_remains_candidate_only": True,
        "model_execution_beyond_construction_attempt": False,
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
        "selected_next_target": NEXT_TARGET
        if executed
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT",
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if executed else 0,
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_RESULT_"
            "ONLY_NO_SOURCE_ADMISSIBILITY_CONSERVATION_BIANCHI_SEMICLASSICAL_"
            "EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This construction attempt records only a bounded toy "
            "stress-energy-like source candidate on a fixed controlled "
            "background. It preserves no source admissibility, no conservation "
            "claim, no conservation witness, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no QFT-GR closure, no empirical "
            "validation, no master-action promotion, no release assembly, and "
            "no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_construction_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_construction_attempt(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR minimal working model construction attempt."
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_PACKET_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_construction_attempt(
        packet_result_review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_construction_attempt_report: "
        f"executed={payload['executed']} "
        f"classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
