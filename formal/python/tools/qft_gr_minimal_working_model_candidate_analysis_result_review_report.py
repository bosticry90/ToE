from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_report import (
    ANALYSIS_CLASSIFICATION as EXPECTED_ANALYSIS_CLASSIFICATION,
    ANALYSIS_ID as EXPECTED_ANALYSIS_ID,
    DEFAULT_OUT as DEFAULT_CANDIDATE_ANALYSIS_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_ANALYSIS_OUTCOME,
    SCHEMA_ID as EXPECTED_ANALYSIS_SCHEMA_ID,
    TOY_SOURCE_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-12T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_RESULT_REVIEW_20260612_v0"
REVIEW_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_RESULT_REVIEW_"
    "ACCEPTS_CANDIDATE_ONLY_ANALYSIS_AND_AUTHORIZES_BOUNDED_CONSERVATION_"
    "TEST_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_candidate_analysis_result_review_"
    "accepts_candidate_only_analysis_and_authorizes_bounded_conservation_"
    "test_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "prepare_qft_gr_minimal_working_model_conservation_test_packet"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_conservation_test_packet_preparation"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_RESULT_REVIEW_20260612_v0.json"
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
                "The candidate-only analysis is accepted, so the next bounded "
                "action may prepare a conservation-test packet for the toy "
                "source candidate without claiming source admissibility, "
                "conservation, Bianchi compatibility, or QFT-GR closure."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This candidate-analysis result-review target is consumed here.",
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_countermodel_packet",
            "decision": "not_selected_by_this_review",
            "reason": (
                "Countermodel preparation remains a possible downstream route "
                "if the bounded conservation test produces an obstruction."
            ),
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_scope_refinement_packet",
            "decision": "not_selected_by_this_review",
            "reason": (
                "Scope refinement remains available later, but this review "
                "authorizes only the conservation-test packet preparation."
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
            "reason": "The accepted analysis records a test target, not a proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized by review.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains untested and unclaimed.",
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


def build_qft_gr_minimal_working_model_candidate_analysis_result_review(
    *,
    candidate_analysis_path: Path = DEFAULT_CANDIDATE_ANALYSIS_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    analysis = _read_json(candidate_analysis_path)
    status_map = analysis.get("candidate_status_map", {})
    candidate_next_targets = _candidate_next_targets()
    demonstrates = analysis.get("what_model_demonstrates", [])
    remains_supplied = analysis.get("what_remains_supplied", [])
    fails_or_untested = analysis.get("what_fails_or_remains_untested", [])

    acceptance_criteria = {
        "consumes_expected_candidate_analysis_artifact": analysis.get("schema_id")
        == EXPECTED_ANALYSIS_SCHEMA_ID,
        "candidate_analysis_id_expected": analysis.get("analysis_id")
        == EXPECTED_ANALYSIS_ID,
        "candidate_analysis_outcome_expected": analysis.get("outcome_id")
        == EXPECTED_ANALYSIS_OUTCOME,
        "candidate_analysis_classification_expected": analysis.get(
            "analysis_classification"
        )
        == EXPECTED_ANALYSIS_CLASSIFICATION,
        "candidate_analysis_selected_this_result_review": analysis.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "candidate_analysis_completed": analysis.get("analysis_completed") is True
        and analysis.get("accepted") is True,
        "toy_source_remains_candidate_only": analysis.get(
            "toy_source_candidate_status"
        )
        == TOY_SOURCE_STATUS
        and analysis.get("toy_source_candidate_remains_candidate_only") is True
        and analysis.get("toy_source_promoted_to_admissible_source") is False,
        "identifies_what_model_demonstrates": len(demonstrates) >= 3,
        "identifies_what_remains_supplied": len(remains_supplied) >= 5,
        "identifies_what_remains_untested_or_failed": len(fails_or_untested) >= 6,
        "maps_required_status_categories": set(status_map) == {
            "domain",
            "regularity",
            "pairing",
            "weak_conservation",
            "source_admissibility",
            "Bianchi_compatibility",
        },
        "domain_status_bounded": status_map.get("domain", {}).get("status")
        == "supplied_imported_domain_conditions_only",
        "regularity_status_imported": status_map.get("regularity", {}).get("status")
        == "imported_regularities_recorded_not_reproved",
        "pairing_status_imported": status_map.get("pairing", {}).get("status")
        == "distributional_pairing_domain_imported_not_validated_for_source",
        "weak_conservation_not_proved": status_map.get("weak_conservation", {}).get(
            "status"
        )
        == "test_target_recorded_not_proved",
        "source_admissibility_not_claimed": analysis.get("source_admissibility_claimed")
        is False
        and analysis.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_or_witness": analysis.get("conservation_claimed")
        is False
        and analysis.get("conservation_proved") is False
        and analysis.get("conservation_proof_object_constructed") is False
        and analysis.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": analysis.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and analysis.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": analysis.get("qft_gr_seam_closed") is False
        and analysis.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": analysis.get(
            "empirical_validation_claimed"
        )
        is False
        and analysis.get("public_submission_authorized") is False,
        "no_master_action_promotion": analysis.get("master_action_promoted") is False
        and analysis.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_RESULT_REVIEW"
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
        else "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_candidate_analysis_result_review_requires_remediation",
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_candidate_analysis": (
            EXPECTED_ANALYSIS_ID
        ),
        "consumes_qft_gr_minimal_working_model_candidate_analysis_pointer": _ptr(
            candidate_analysis_path
        ),
        "consumed_candidate_analysis_schema_id": analysis.get("schema_id"),
        "consumed_candidate_analysis_outcome_id": analysis.get("outcome_id"),
        "consumed_candidate_analysis_classification": analysis.get(
            "analysis_classification"
        ),
        "candidate_only_analysis_accepted": accepted,
        "bounded_conservation_test_packet_authorized": accepted,
        "conservation_test_packet_prepared_by_review": False,
        "toy_source_candidate_status": analysis.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": accepted,
        "toy_source_promoted_to_admissible_source": False,
        "what_model_demonstrates": demonstrates,
        "what_remains_supplied": remains_supplied,
        "what_fails_or_remains_untested": fails_or_untested,
        "candidate_status_map": status_map,
        "what_model_demonstrates_recorded": len(demonstrates) >= 3,
        "what_remains_supplied_recorded": len(remains_supplied) >= 5,
        "what_fails_or_remains_untested_recorded": len(fails_or_untested) >= 6,
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
        "aggregate_lean_timeout_caveat_preserved": analysis.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": analysis.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_"
            "ONLY_NO_SOURCE_ADMISSIBILITY_CONSERVATION_WITNESS_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_"
            "PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the candidate-only analysis and "
            "authorizes bounded conservation-test packet preparation. It "
            "preserves no source admissibility, no conservation claim, no "
            "conservation proof object, no conservation witness, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, no empirical validation, no master-action promotion, no "
            "release assembly, and no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_candidate_analysis_result_review(
    *,
    candidate_analysis_path: Path = DEFAULT_CANDIDATE_ANALYSIS_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_candidate_analysis_result_review(
        candidate_analysis_path=candidate_analysis_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model candidate analysis "
            "result review."
        )
    )
    parser.add_argument("--analysis", type=Path, default=DEFAULT_CANDIDATE_ANALYSIS_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    analysis_path = (
        ns.analysis if ns.analysis.is_absolute() else (REPO_ROOT / ns.analysis)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_candidate_analysis_result_review(
        candidate_analysis_path=analysis_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_candidate_analysis_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
