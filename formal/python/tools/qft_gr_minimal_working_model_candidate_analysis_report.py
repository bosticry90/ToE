from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_construction_attempt_report import (
    DEFAULT_OUT as DEFAULT_CONSTRUCTION_ATTEMPT_PATH,
    SCHEMA_ID as EXPECTED_CONSTRUCTION_ATTEMPT_SCHEMA_ID,
    TOY_SOURCE_STATUS,
)
from formal.python.tools.qft_gr_minimal_working_model_construction_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_CONSTRUCTION_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_CONSTRUCTION_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_CONSTRUCTION_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_CONSTRUCTION_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-12T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_20260612_v0"
ANALYSIS_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_COMPLETED_WITH_NO_"
    "SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
ANALYSIS_CLASSIFICATION = (
    "qft_gr_minimal_working_model_candidate_analysis_completed_pending_result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_working_model_candidate_analysis_result"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_candidate_analysis_result_review"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_20260612_v0.json"
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
                "The candidate-only analysis must be result-reviewed before "
                "any conservation-test packet, countermodel packet, or scope "
                "refinement packet is authorized."
            ),
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_conservation_test_packet",
            "decision": "not_authorized_before_analysis_result_review",
            "reason": (
                "The analysis records a weak-conservation test target, but no "
                "test packet is authorized until the analysis result is reviewed."
            ),
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_countermodel_packet",
            "decision": "not_authorized_before_analysis_result_review",
            "reason": (
                "Potential failure modes are identified only for later review; "
                "no countermodel packet is prepared here."
            ),
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_scope_refinement_packet",
            "decision": "not_authorized_before_analysis_result_review",
            "reason": (
                "Scope refinement remains a possible downstream route after "
                "analysis result review."
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
            "reason": "The analysis does not prove conservation.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by the analysis.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains outside the candidate-only analysis.",
        },
    ]


def _analysis_status_map(model: dict[str, Any]) -> dict[str, dict[str, Any]]:
    candidate = model.get("stress_energy_like_candidate", {})
    weak_target = model.get("weak_conservation_test_target", {})
    return {
        "domain": {
            "status": "supplied_imported_domain_conditions_only",
            "field_state_setup": model.get("field_state_setup", {}),
            "source_domain_membership_claimed": False,
            "admissible_source_domain_established": False,
        },
        "regularity": {
            "status": "imported_regularities_recorded_not_reproved",
            "imported_regularities": model.get("imported_regularities", []),
            "regularity_discharge_claimed": False,
        },
        "pairing": {
            "status": "distributional_pairing_domain_imported_not_validated_for_source",
            "pairing_test_executed": False,
            "pairing_witness_constructed": False,
        },
        "weak_conservation": {
            "status": weak_target.get("status"),
            "target": weak_target.get("target"),
            "conservation_claimed": False,
            "conservation_proof_object_constructed": False,
            "conservation_witness_constructed": False,
        },
        "source_admissibility": {
            "status": candidate.get("status"),
            "source_admissibility_claimed": False,
            "toy_source_promoted_to_admissible_source": False,
        },
        "Bianchi_compatibility": {
            "status": "not_tested_not_claimed",
            "Bianchi_compatibility_claimed": False,
            "semiclassical_einstein_equation_derived": False,
        },
    }


def build_qft_gr_minimal_working_model_candidate_analysis(
    *,
    construction_attempt_result_review_path: Path = (
        DEFAULT_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH
    ),
    construction_attempt_path: Path = DEFAULT_CONSTRUCTION_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(construction_attempt_result_review_path)
    attempt = _read_json(construction_attempt_path)
    model = attempt.get("bounded_minimal_model_attempt", {})
    candidate = model.get("stress_energy_like_candidate", {})
    weak_target = model.get("weak_conservation_test_target", {})
    candidate_next_targets = _candidate_next_targets()
    status_map = _analysis_status_map(model)

    what_model_demonstrates = [
        (
            "A bounded scalar-field stress-energy-like candidate can be "
            "organized on the fixed controlled background under imported "
            "operator-domain, renormalization, state-domain, and mathematical "
            "regularity assumptions."
        ),
        (
            "The construction identifies a concrete weak-conservation test "
            "target and source-admissibility decision surface for later work."
        ),
        (
            "The candidate can be inspected without promoting it to a physical "
            "source or closing the QFT-GR seam."
        ),
    ]
    what_remains_supplied = [
        "fixed background geometry and background-compatible derivative operator",
        "field, state, and expectation-object placeholders",
        "regularized or renormalized expectation-object availability",
        "operator-domain, renormalization, state-domain, and regularity assumptions",
        "distributional pairing and limit/interchange regularity support",
    ]
    what_fails_or_remains_untested = [
        "source admissibility is not established",
        "weak conservation is recorded only as a test target and is not proved",
        "no conservation proof object or witness is constructed",
        "Bianchi compatibility is not tested or claimed",
        "the semiclassical Einstein equation is not derived",
        "QFT-GR closure is not obtained",
    ]

    acceptance_criteria = {
        "consumes_expected_construction_attempt_result_review_artifact": (
            result_review.get("schema_id")
            == EXPECTED_CONSTRUCTION_RESULT_REVIEW_SCHEMA_ID
        ),
        "construction_result_review_outcome_expected": result_review.get(
            "outcome_id"
        )
        == EXPECTED_CONSTRUCTION_RESULT_REVIEW_OUTCOME,
        "construction_result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_CONSTRUCTION_RESULT_REVIEW_CLASSIFICATION,
        "construction_result_review_selected_this_analysis": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "construction_result_review_authorized_analysis_only": result_review.get(
            "model_analysis_only_authorized"
        )
        is True
        and result_review.get("model_analysis_executed_by_review") is False,
        "construction_attempt_available": attempt.get("schema_id")
        == EXPECTED_CONSTRUCTION_ATTEMPT_SCHEMA_ID,
        "analyzes_toy_source_candidate_only": result_review.get(
            "toy_source_candidate_status"
        )
        == TOY_SOURCE_STATUS
        and candidate.get("status") == TOY_SOURCE_STATUS,
        "identifies_what_model_demonstrates": len(what_model_demonstrates) >= 3,
        "identifies_what_remains_supplied": len(what_remains_supplied) >= 5,
        "identifies_what_fails_or_remains_untested": len(
            what_fails_or_remains_untested
        )
        >= 6,
        "maps_required_status_categories": set(status_map) == {
            "domain",
            "regularity",
            "pairing",
            "weak_conservation",
            "source_admissibility",
            "Bianchi_compatibility",
        },
        "no_source_admissibility_claim": candidate.get(
            "source_admissibility_claimed"
        )
        is False
        and result_review.get("source_admissibility_claimed") is False,
        "no_conservation_claim_or_witness": weak_target.get(
            "conservation_claimed"
        )
        is False
        and weak_target.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": result_review.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and result_review.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": result_review.get("qft_gr_seam_closed") is False
        and result_review.get("qft_gr_source_map_closure_claimed") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS"
    )

    return {
        "schema_id": SCHEMA_ID,
        "analysis_id": ANALYSIS_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "analysis_completed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_REQUIRES_REMEDIATION",
        "analysis_classification": ANALYSIS_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_candidate_analysis_requires_remediation",
        "analysis_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_construction_attempt_result_review": (
            EXPECTED_CONSTRUCTION_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_construction_attempt_result_review_pointer": _ptr(
            construction_attempt_result_review_path
        ),
        "consumed_construction_attempt_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "consumed_construction_attempt_result_review_outcome_id": result_review.get(
            "outcome_id"
        ),
        "consumed_construction_attempt_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "consumed_construction_attempt_pointer": _ptr(construction_attempt_path),
        "candidate_model_id": model.get("attempt_model_id"),
        "candidate_model_class": model.get("model_class"),
        "toy_source_candidate_status": candidate.get("status"),
        "toy_source_candidate_remains_candidate_only": accepted,
        "toy_source_promoted_to_admissible_source": False,
        "candidate_analysis_only": True,
        "model_execution_beyond_candidate_analysis": False,
        "what_model_demonstrates": what_model_demonstrates,
        "what_remains_supplied": what_remains_supplied,
        "what_fails_or_remains_untested": what_fails_or_remains_untested,
        "candidate_status_map": status_map,
        "conservation_test_packet_prepared": False,
        "countermodel_packet_prepared": False,
        "scope_refinement_packet_prepared": False,
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
        "aggregate_lean_timeout_caveat_preserved": result_review.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": result_review.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_RESULT_ONLY_"
            "NO_SOURCE_ADMISSIBILITY_CONSERVATION_WITNESS_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_"
            "PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This candidate-only analysis interprets only the bounded toy "
            "source candidate. It preserves no source admissibility, no "
            "conservation claim, no conservation proof object, no conservation "
            "witness, no Bianchi compatibility, no semiclassical Einstein "
            "equation, no QFT-GR closure, no empirical validation, no public "
            "submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_working_model_candidate_analysis(
    *,
    construction_attempt_result_review_path: Path = (
        DEFAULT_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH
    ),
    construction_attempt_path: Path = DEFAULT_CONSTRUCTION_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_candidate_analysis(
        construction_attempt_result_review_path=construction_attempt_result_review_path,
        construction_attempt_path=construction_attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR minimal working model candidate analysis."
    )
    parser.add_argument(
        "--result-review",
        type=Path,
        default=DEFAULT_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH,
    )
    parser.add_argument(
        "--attempt",
        type=Path,
        default=DEFAULT_CONSTRUCTION_ATTEMPT_PATH,
    )
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
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_candidate_analysis(
        construction_attempt_result_review_path=result_review_path,
        construction_attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_candidate_analysis_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
