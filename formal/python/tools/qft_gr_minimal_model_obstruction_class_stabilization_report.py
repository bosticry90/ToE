from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    PATTERN_STABILIZATION_SIGNAL,
    POSITIVE_WITNESS_TARGET,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_20260614_v0"
PACKET_ID = "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_PREPARED_WITH_"
    "DOMINANT_WEAK_PAIRING_OBSTRUCTION_CANDIDATE_AND_NO_SOURCE_ADMISSIBILITY_"
    "OR_CONSERVATION_PROOF"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_model_obstruction_class_stabilization_packet_prepared_"
    "dominant_weak_pairing_obstruction_candidate_not_resolved_no_source_"
    "admissibility_or_conservation_proof"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_model_obstruction_class_stabilization_packet_result"
NEXT_TARGET_KIND = "qft_gr_minimal_model_obstruction_class_stabilization_packet_result_review"
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction"
)
IMMEDIATE_RETEST_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_"
    "post_retest_refinement_conservation_retest_refinement_refinement"
)
ORDINARY_REFINEMENT_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_refinement"
)
STATUS = OBSTRUCTION_STATUS

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_20260614_v0.json"
)
DEFAULT_MARKDOWN_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_REPORT_v0.md"
)

ATTEMPT_CHAIN_PATHS = [
    (
        "initial_conservation_test",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_20260612_v0.json",
        "Initial bounded conservation test of the minimal toy stress-energy-like candidate.",
    ),
    (
        "first_conservation_retest",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_20260613_v0.json",
        "First bounded retest after the model had been refined from the initial inconclusive test.",
    ),
    (
        "post_refinement_conservation_retest",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_20260613_v0.json"
        ),
        "Post-retest-refinement retest under a narrower toy candidate and test scope.",
    ),
    (
        "post_retest_refinement_conservation_retest_refinement_v3_retest",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_20260614_v0.json"
        ),
        "V3 retest after repeated inconclusive results and a conservation-retest-refinement packet.",
    ),
    (
        "latest_v4_conservation_retest_after_latest_refinement",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_"
            "20260614_v0.json"
        ),
        "Latest v4 retest under v4 weak-pairing and regularity candidates.",
    ),
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _first_text(value: Any, default: str) -> str:
    if isinstance(value, list) and value:
        return str(value[0])
    if isinstance(value, str) and value:
        return value
    return default


def _retest_condition_id(payload: dict[str, Any]) -> str:
    condition = payload.get("retest_conservation_condition")
    if isinstance(condition, dict):
        return str(condition.get("condition_id", "not_recorded"))
    return "initial_conservation_condition"


def _attempt_chain_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for sequence, (label, path, change_summary) in enumerate(ATTEMPT_CHAIN_PATHS, 1):
        payload = _read_json(path)
        classification = str(payload.get("result_classification", ""))
        retest_result = str(payload.get("retest_result", "inconclusive"))
        rows.append(
            {
                "sequence": sequence,
                "label": label,
                "artifact": _ptr(path),
                "schema_id": payload.get("schema_id"),
                "outcome_id": payload.get("outcome_id"),
                "attempt_id": payload.get("attempt_id"),
                "what_changed": change_summary,
                "what_was_tested": _first_text(
                    payload.get("what_was_tested"),
                    "bounded weak conservation of the current toy candidate",
                ),
                "retest_condition_id": _retest_condition_id(payload),
                "result_recorded": retest_result,
                "result_classification": classification,
                "what_remained_undecided": _first_text(
                    payload.get("why_inconclusive"),
                    "weak divergence remained undecided under the current candidate scope",
                ),
                "why_not_conservation_proof": (
                    "No conservation proof object or witness was constructed, "
                    "and the result classification remained inconclusive."
                ),
                "why_not_failure": (
                    "No explicit nonzero weak-divergence pairing, undefined "
                    "required pairing, or blocked exchange step was recorded "
                    "as a failure witness."
                ),
                "local_validation_result": (
                    "bounded local/focused validation preserved by the consumed checkpoint"
                ),
                "inconclusive": (
                    payload.get("retest_inconclusive") is True
                    or retest_result == "inconclusive"
                    or "inconclusive" in classification
                ),
                "converted_to_pass": payload.get("retest_passed") is True,
                "converted_to_failure": payload.get("retest_failed") is True,
                "source_admissibility_claimed": payload.get(
                    "source_admissibility_claimed", False
                )
                is True,
                "conservation_proof_claimed": (
                    payload.get("conservation_proved", False) is True
                    or payload.get("conservation_proof_object_constructed", False) is True
                ),
            }
        )
    return rows


def _obstruction_rows() -> list[dict[str, Any]]:
    row_data = [
        (
            DOMINANT_OBSTRUCTION_CANDIDATE,
            CANONICAL_OBSTRUCTION_ID,
            "dominant_candidate",
            True,
            STATUS,
            "Repeated retests leave weak divergence undecided under the candidate weak-pairing domain.",
            POSITIVE_WITNESS_TARGET,
        ),
        (
            "regularity_obstruction",
            "regularity_context_does_not_force_weak_divergence_vanish_v0",
            "supporting",
            False,
            "supporting_obstruction_not_selected_as_dominant",
            "Regularity assumptions admit bounded operations but do not force the weak divergence to vanish.",
            POSITIVE_WITNESS_TARGET,
        ),
        (
            "limit_derivative_exchange_obstruction",
            "limit_derivative_exchange_not_globally_discharged_v0",
            "supporting",
            False,
            "supporting_obstruction_not_selected_as_dominant",
            "Derivative, regularization, and limit/interchange clauses remain bounded and candidate-level.",
            POSITIVE_WITNESS_TARGET,
        ),
        (
            "test_vector_class_obstruction",
            "test_vector_class_too_bounded_to_force_source_admissibility_v0",
            "supporting",
            False,
            "supporting_obstruction_not_selected_as_dominant",
            "The allowed test-vector class is useful for retesting but not enough to prove source admissibility.",
            POSITIVE_WITNESS_TARGET,
        ),
        (
            "candidate_source_definition_obstruction",
            "toy_source_candidate_definition_not_admissible_source_v0",
            "supporting",
            False,
            "supporting_obstruction_not_selected_as_dominant",
            "The stress-energy-like object remains a candidate definition, not an admissible source.",
            POSITIVE_WITNESS_TARGET,
        ),
        (
            "boundary_term_obstruction",
            "boundary_terms_not_disposed_by_general_source_proof_v0",
            "supporting",
            False,
            "supporting_obstruction_not_selected_as_dominant",
            "Boundary-term control remains assumed or scoped rather than proved at source level.",
            POSITIVE_WITNESS_TARGET,
        ),
        (
            "curvature_coupling_obstruction",
            "curvature_coupling_not_bound_to_bianchi_compatibility_v0",
            "supporting",
            False,
            "supporting_obstruction_not_selected_as_dominant",
            "The retests do not bind the candidate source to Bianchi compatibility or Einstein-like coupling.",
            SOURCE_MAP_LADDER_TARGET,
        ),
        (
            "formalization_insufficiency_obstruction",
            "marker_level_formalization_does_not_construct_conservation_proof_v0",
            "supporting",
            False,
            "supporting_obstruction_not_selected_as_dominant",
            "Current Lean artifacts are governance markers and do not construct a conservation proof object.",
            POSITIVE_WITNESS_TARGET,
        ),
    ]
    return [
        {
            "obstruction_candidate": row[0],
            "canonical_or_supporting_id": row[1],
            "priority": row[2],
            "selected": row[3],
            "status": row[4],
            "evidence_summary": row[5],
            "resolved": False,
            "claim_ceiling": "stabilization_for_next_target_selection_not_resolution",
            "recommended_follow_on": row[6],
        }
        for row in row_data
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "Prepared packet must be result-reviewed before witness work begins.",
        },
        {
            "target": POSITIVE_WITNESS_TARGET,
            "decision": "recommended_after_packet_review",
            "reason": "A small positive conservation witness is the preferred scientific fork after stabilization review.",
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "retained_follow_on",
            "reason": "Countermodel pressure remains useful after the positive witness packet.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on",
            "reason": "Source-map ladder reconstruction follows witness/countermodel pressure.",
        },
        {
            "target": IMMEDIATE_RETEST_TARGET,
            "decision": "not_authorized",
            "reason": "The stabilization packet explicitly forbids immediate retest.",
        },
        {
            "target": ORDINARY_REFINEMENT_TARGET,
            "decision": "not_authorized",
            "reason": "The pivot stops same-shaped ordinary refinement/retest cycling.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "Source admissibility is not claimed or authorized.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "No conservation proof is prepared or constructed.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains outside this packet.",
        },
    ]


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def render_markdown(payload: dict[str, Any]) -> str:
    chain_lines = [
        (
            f"| {row['sequence']} | {row['label']} | {row['result_recorded']} | "
            f"{row['retest_condition_id']} |"
        )
        for row in payload["attempt_chain_rows"]
    ]
    obstruction_lines = [
        (
            f"| {row['obstruction_candidate']} | {row['priority']} | "
            f"{row['status']} | {str(row['resolved']).lower()} |"
        )
        for row in payload["obstruction_map_rows"]
    ]
    return (
        "# QFT-GR Minimal Model Obstruction Class Stabilization\n\n"
        f"- Packet: `{payload['packet_id']}`\n"
        f"- Outcome: `{payload['outcome_id']}`\n"
        f"- Dominant obstruction candidate: `{payload['dominant_obstruction_candidate']}`\n"
        f"- Canonical obstruction id: `{payload['canonical_obstruction_id']}`\n"
        f"- Status: `{payload['obstruction_status']}`\n\n"
        f"{payload['pattern_stabilization_signal']}\n\n"
        "## Conservation Attempt Chain\n\n"
        "| # | Attempt | Result | Condition |\n"
        "|---|---|---|---|\n"
        + "\n".join(chain_lines)
        + "\n\n"
        "## Obstruction Map\n\n"
        "| Candidate | Priority | Status | Resolved |\n"
        "|---|---|---|---|\n"
        + "\n".join(obstruction_lines)
        + "\n\n"
        "## Next Routing\n\n"
        f"- Selected next target: `{payload['selected_next_target']}`\n"
        f"- Recommended lane after review: `{payload['recommended_next_lane_after_review']}`\n"
        "- Immediate retest: not authorized\n"
        "- Ordinary model refinement: not authorized\n\n"
        "## Nonclaim Boundary\n\n"
        f"{payload['non_claim_boundary']}\n"
    )


def build_qft_gr_minimal_model_obstruction_class_stabilization_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    attempt_rows = _attempt_chain_rows()
    obstruction_rows = _obstruction_rows()
    candidate_next_targets = _candidate_next_targets()
    dominant_rows = [row for row in obstruction_rows if row["selected"]]
    supporting_rows = [row for row in obstruction_rows if not row["selected"]]

    acceptance_criteria = {
        "consumes_expected_result_review": (
            review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
        ),
        "result_review_selected_this_packet": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "review_recorded_repeated_inconclusive_pattern": (
            review.get("repeated_inconclusive_pattern_recorded") is True
            and review.get("repeated_inconclusive_attempt_count") == 5
        ),
        "attempt_chain_complete_and_inconclusive": (
            len(attempt_rows) == 5
            and all(row["inconclusive"] for row in attempt_rows)
            and not any(row["converted_to_pass"] for row in attempt_rows)
            and not any(row["converted_to_failure"] for row in attempt_rows)
        ),
        "dominant_obstruction_candidate_matches_review": (
            review.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and review.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and review.get("obstruction_status") == STATUS
        ),
        "dominant_obstruction_candidate_not_resolved": (
            len(dominant_rows) == 1
            and dominant_rows[0]["obstruction_candidate"]
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and dominant_rows[0]["resolved"] is False
            and dominant_rows[0]["status"] == STATUS
        ),
        "supporting_obstructions_recorded": len(supporting_rows) == 7
        and all(row["resolved"] is False for row in supporting_rows),
        "stabilization_signal_recorded": PATTERN_STABILIZATION_SIGNAL
        == review.get("pattern_stabilization_signal"),
        "immediate_retest_forbidden": review.get(
            "immediate_conservation_retest_authorized"
        )
        is False,
        "ordinary_refinement_forbidden": review.get(
            "ordinary_model_refinement_packet_authorized"
        )
        is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "positive_witness_lane_recommended": POSITIVE_WITNESS_TARGET
        in [row["target"] for row in candidate_next_targets],
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
        else "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_retest_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_retest_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "attempt_chain_rows": attempt_rows,
        "attempt_chain_count": len(attempt_rows),
        "all_prior_conservation_attempts_consumed": prepared,
        "latest_result_marked_inconclusive": attempt_rows[-1]["inconclusive"],
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": STATUS,
        "dominant_obstruction_candidate_selected": True,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "obstruction_map_rows": obstruction_rows,
        "supporting_obstruction_count": len(supporting_rows),
        "pattern_stabilization_signal": PATTERN_STABILIZATION_SIGNAL,
        "repeated_inconclusive_pattern_is_stabilization_signal": True,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
        "positive_witness_lane_recommended": True,
        "recommended_next_lane_after_review": POSITIVE_WITNESS_TARGET,
        "countermodel_lane_retained_as_follow_on": True,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "countermodel_packet_prepared": False,
        "source_map_ladder_packet_prepared": False,
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
            "checkpoint_type": "routine_obstruction_class_stabilization_packet",
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
        "non_claim_boundary": (
            "This stabilization packet compresses the repeated inconclusive "
            "QFT-GR minimal-model conservation chain into an obstruction map. "
            "It selects weak_pairing_domain_obstruction only as a dominant "
            "obstruction candidate for next-target selection, not as solved "
            "mathematics. It authorizes no immediate retest, no ordinary model "
            "refinement, no conservation proof, no conservation proof object, "
            "no conservation witness, no source admissibility, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, no empirical validation, no public submission, and no "
            "master-action promotion."
        ),
    }
    return payload


def write_qft_gr_minimal_model_obstruction_class_stabilization_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    markdown_out: Path = DEFAULT_MARKDOWN_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_obstruction_class_stabilization_packet(
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
        description="Generate the QFT-GR minimal-model obstruction-class stabilization packet."
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
    payload = write_qft_gr_minimal_model_obstruction_class_stabilization_packet(
        result_review_path=result_review_path,
        out=out,
        markdown_out=markdown_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_model_obstruction_class_stabilization_report: "
        f"prepared={payload['prepared']} next={payload['selected_next_target']} "
        f"out={_ptr(out)} markdown={_ptr(markdown_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
