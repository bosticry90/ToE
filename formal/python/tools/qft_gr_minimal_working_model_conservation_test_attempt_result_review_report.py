from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as EXPECTED_RESULT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
    TEST_RESULT as EXPECTED_TEST_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-12T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_"
    "20260612_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_"
    "ACCEPTS_INCONCLUSIVE_TEST_AND_AUTHORIZES_MODEL_REFINEMENT_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_test_attempt_result_review_"
    "accepts_inconclusive_test_and_authorizes_model_refinement_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "prepare_qft_gr_minimal_working_model_refinement_packet"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_refinement_packet_preparation_only"
SELECTED_REFINEMENT_TARGET = (
    "refine_weak_pairing_domain_and_regularity_for_toy_candidate_without_"
    "source_admissibility"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_"
        "20260612_v0.json"
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
                "The conservation-test attempt is accepted as inconclusive, so "
                "the next bounded action may prepare only a model-refinement "
                "packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This conservation-test attempt result-review target is "
                "consumed here."
            ),
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_countermodel_packet",
            "decision": "not_selected_no_failure_obstruction",
            "reason": (
                "The attempt did not identify an explicit failure obstruction "
                "requiring a countermodel packet."
            ),
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_scope_refinement_packet",
            "decision": "not_selected_model_refinement_packet_selected",
            "reason": (
                "The inconclusive result is routed to one model-refinement "
                "packet rather than a separate scope-refinement packet."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains a candidate only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The accepted result is inconclusive, not a proof.",
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
            "reason": "QFT-GR closure remains outside this result review.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _refinement_target_rows() -> list[dict[str, Any]]:
    return [
        {
            "refinement_target": SELECTED_REFINEMENT_TARGET,
            "selected": True,
            "reason": (
                "The attempt's inconclusive branch is caused by insufficient "
                "weak pairing-domain and regularity support for the toy "
                "candidate, without source admissibility."
            ),
        },
        {
            "refinement_target": "construct_countermodel_for_failed_conservation_test",
            "selected": False,
            "reason": "No explicit failed conservation-test obstruction was recorded.",
        },
        {
            "refinement_target": "promote_toy_candidate_to_admissible_source",
            "selected": False,
            "reason": "Source admissibility is not claimed or authorized.",
        },
        {
            "refinement_target": "derive_bianchi_compatible_semiclassical_coupling",
            "selected": False,
            "reason": (
                "Bianchi compatibility and the semiclassical Einstein equation "
                "remain outside this review."
            ),
        },
    ]


def _attempt_nonclaim_keys() -> list[str]:
    return [
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "physical_source_claimed",
        "conservation_claimed",
        "conservation_proved",
        "conservation_proof_object_constructed",
        "conservation_witness_constructed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_claimed",
        "empirical_validation_claimed",
        "scientific_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "release_assembly_authorized",
        "release_packet_assembled",
        "public_submission_authorized",
        "publication_authorized",
    ]


def build_qft_gr_minimal_working_model_conservation_test_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_next_targets = _candidate_next_targets()
    refinement_target_rows = _refinement_target_rows()
    selected_refinement_targets = [
        row["refinement_target"] for row in refinement_target_rows if row["selected"]
    ]

    acceptance_criteria = {
        "consumes_expected_conservation_test_attempt": attempt.get("schema_id")
        == EXPECTED_ATTEMPT_SCHEMA_ID
        and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID,
        "attempt_outcome_expected": attempt.get("outcome_id")
        == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_classification_expected": attempt.get("result_classification")
        == EXPECTED_RESULT_CLASSIFICATION,
        "attempt_selected_this_result_review": attempt.get("selected_next_target")
        == CONSUMED_TARGET,
        "attempt_executed_inconclusive": attempt.get("attempt_executed") is True
        and attempt.get("test_result") == EXPECTED_TEST_RESULT
        and attempt.get("test_inconclusive") is True,
        "does_not_convert_inconclusive_to_pass": attempt.get("test_passed") is False
        and attempt.get("conservation_test_pass_claimed") is False,
        "does_not_convert_inconclusive_to_failure": attempt.get("test_failed") is False
        and attempt.get("conservation_test_failure_claimed") is False,
        "why_inconclusive_recorded": len(attempt.get("why_inconclusive", [])) >= 5,
        "no_source_admissibility_claim": attempt.get("source_admissibility_claimed")
        is False
        and attempt.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": attempt.get(
            "conservation_claimed"
        )
        is False
        and attempt.get("conservation_proved") is False
        and attempt.get("conservation_proof_object_constructed") is False
        and attempt.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": attempt.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and attempt.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": attempt.get("qft_gr_seam_closed") is False
        and attempt.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": attempt.get(
            "empirical_validation_claimed"
        )
        is False
        and attempt.get("public_submission_authorized") is False,
        "no_master_action_promotion": attempt.get("master_action_promoted") is False
        and attempt.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "exactly_one_refinement_target_selected": selected_refinement_targets
        == [SELECTED_REFINEMENT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_"
            "RESULT_REVIEW"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_conservation_test_attempt_result_"
            "review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_test_attempt": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_test_attempt_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "conservation_test_attempt_result_review_accepted": accepted,
        "conservation_test_attempt_consumed": accepted,
        "conservation_test_attempt_executed": attempt.get("attempt_executed") is True,
        "conservation_test_attempt_result": attempt.get("test_result"),
        "classification_confirmed": attempt.get("result_classification")
        == EXPECTED_RESULT_CLASSIFICATION,
        "accepted_inconclusive_result": accepted,
        "inconclusive_not_converted_to_pass": True,
        "conservation_test_passed": False,
        "conservation_test_failed": False,
        "conservation_test_inconclusive": accepted,
        "test_result": EXPECTED_TEST_RESULT if accepted else "requires_remediation",
        "test_passed": False,
        "test_failed": False,
        "test_inconclusive": accepted,
        "model_refinement_packet_authorized": accepted,
        "model_refinement_packet_prepared_by_review": False,
        "model_refinement_executed_by_review": False,
        "selected_refinement_target": (
            SELECTED_REFINEMENT_TARGET if accepted else "requires_remediation"
        ),
        "selected_refinement_target_count": 1 if accepted else 0,
        "refinement_target_rows": refinement_target_rows,
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
        "attempt_nonclaim_keys_checked": _attempt_nonclaim_keys(),
        "aggregate_lean_timeout_caveat_preserved": attempt.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": attempt.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if accepted else 0,
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_ONLY_NO_"
            "CONSERVATION_PROOF_WITNESS_SOURCE_ADMISSIBILITY_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_"
            "PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the bounded conservation-test attempt "
            "as inconclusive and authorizes only one model-refinement packet. "
            "It does not convert the inconclusive result into a pass or "
            "failure, does not claim conservation, does not construct a "
            "conservation proof object, constructs no conservation witness, "
            "does not claim source "
            "admissibility, does not claim Bianchi compatibility, does not "
            "derive the semiclassical Einstein equation, does not close QFT-GR, "
            "does not validate empirically, does not authorize public "
            "submission, and does not promote the master action."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_test_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_test_attempt_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model conservation-test "
            "attempt result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_conservation_test_attempt_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_test_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
