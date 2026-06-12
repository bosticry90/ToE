from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_construction_attempt_report import (
    DEFAULT_OUT as DEFAULT_CONSTRUCTION_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_CONSTRUCTION_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as EXPECTED_CONSTRUCTION_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_CONSTRUCTION_ATTEMPT_SCHEMA_ID,
    TOY_SOURCE_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-11T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_20260611_v0"
REVIEW_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_"
    "ACCEPTS_BOUNDED_MODEL_CONSTRUCTION_AND_AUTHORIZES_MODEL_ANALYSIS_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_construction_attempt_result_review_"
    "accepts_bounded_model_construction_and_authorizes_model_analysis_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "analyze_qft_gr_minimal_working_model_candidate_only"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_candidate_only_analysis"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_20260611_v0.json"
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
                "The construction attempt is accepted only as a bounded toy "
                "source-candidate construction, so the next action may analyze "
                "that candidate model without claiming source admissibility, "
                "conservation, Bianchi compatibility, or QFT-GR closure."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This construction-attempt result-review target is consumed here.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains candidate only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "No conservation claim or proof object is accepted by this review.",
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


def build_qft_gr_minimal_working_model_construction_attempt_result_review(
    *,
    construction_attempt_path: Path = DEFAULT_CONSTRUCTION_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(construction_attempt_path)
    model = attempt.get("bounded_minimal_model_attempt", {})
    candidate = model.get("stress_energy_like_candidate", {})
    weak_target = model.get("weak_conservation_test_target", {})
    candidate_next_targets = _candidate_next_targets()

    acceptance_criteria = {
        "consumes_expected_construction_attempt_artifact": attempt.get("schema_id")
        == EXPECTED_CONSTRUCTION_ATTEMPT_SCHEMA_ID,
        "construction_attempt_outcome_expected": attempt.get("outcome_id")
        == EXPECTED_CONSTRUCTION_ATTEMPT_OUTCOME,
        "construction_attempt_classification_expected": attempt.get(
            "result_classification"
        )
        == EXPECTED_CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "construction_attempt_selected_this_result_review": attempt.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "bounded_model_construction_confirmed": attempt.get(
            "construction_attempt_executed"
        )
        is True
        and attempt.get("bounded_model_construction_attempt_only") is True,
        "toy_source_candidate_remains_candidate_only": attempt.get(
            "toy_source_candidate_status"
        )
        == TOY_SOURCE_STATUS
        and candidate.get("status") == TOY_SOURCE_STATUS,
        "no_source_admissibility_claim": attempt.get("source_admissibility_claimed")
        is False
        and attempt.get("stress_energy_source_admissibility_claimed") is False
        and candidate.get("source_admissibility_claimed") is False,
        "no_conservation_claim_or_proof_object": attempt.get("conservation_claimed")
        is False
        and attempt.get("conservation_proved") is False
        and attempt.get("conservation_proof_object_constructed") is False
        and weak_target.get("conservation_claimed") is False,
        "no_conservation_witness": attempt.get("conservation_witness_constructed")
        is False
        and weak_target.get("conservation_witness_constructed") is False,
        "no_bianchi_compatibility": attempt.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_equation": attempt.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
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
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_RESULT_REVIEW"
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
        else "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_construction_attempt_result_review_requires_remediation",
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_construction_attempt": (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_v0"
        ),
        "consumes_qft_gr_minimal_working_model_construction_attempt_pointer": _ptr(
            construction_attempt_path
        ),
        "consumed_construction_attempt_schema_id": attempt.get("schema_id"),
        "consumed_construction_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_construction_attempt_classification": attempt.get(
            "result_classification"
        ),
        "bounded_model_construction_accepted": accepted,
        "model_analysis_only_authorized": accepted,
        "model_analysis_executed_by_review": False,
        "toy_source_candidate_status": attempt.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": accepted,
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
        "aggregate_lean_timeout_caveat_preserved": attempt.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": attempt.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "ANALYZE_QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ONLY_NO_SOURCE_"
            "ADMISSIBILITY_CONSERVATION_WITNESS_BIANCHI_SEMICLASSICAL_"
            "EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the bounded toy source-candidate "
            "construction attempt and authorizes candidate-only model analysis. "
            "It preserves no source admissibility, no conservation claim, no "
            "conservation proof object, no conservation witness, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, no empirical validation, no master-action promotion, no "
            "release assembly, and no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_construction_attempt_result_review(
    *,
    construction_attempt_path: Path = DEFAULT_CONSTRUCTION_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_construction_attempt_result_review(
        construction_attempt_path=construction_attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model construction attempt "
            "result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_CONSTRUCTION_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_construction_attempt_result_review(
        construction_attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_construction_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
