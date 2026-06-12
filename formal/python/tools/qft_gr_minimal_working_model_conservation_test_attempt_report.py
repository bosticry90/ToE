from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_report import (
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
    TOY_SOURCE_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-12T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_20260612_v0"
ATTEMPT_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_EXECUTED_WITH_NO_"
    "CONSERVATION_PROOF_OR_SOURCE_ADMISSIBILITY"
)
RESULT_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_test_inconclusive_requires_model_refinement"
)
ALLOWED_RESULT_CLASSIFICATIONS = [
    "qft_gr_minimal_working_model_conservation_test_passed_pending_result_review",
    "qft_gr_minimal_working_model_conservation_test_failed_requires_countermodel_or_scope_refinement",
    "qft_gr_minimal_working_model_conservation_test_inconclusive_requires_model_refinement",
]
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_working_model_conservation_test_attempt_result"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_conservation_test_attempt_result_review"
TEST_RESULT = "inconclusive"
TEST_STATUS = "bounded_conservation_test_attempt_executed_inconclusive_pending_result_review"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_20260612_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_repo_path(pointer: str) -> Path:
    path = Path(pointer)
    return path if path.is_absolute() else (REPO_ROOT / path)


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _classification_rows() -> list[dict[str, Any]]:
    return [
        {
            "classification": ALLOWED_RESULT_CLASSIFICATIONS[0],
            "selected": False,
            "meaning": (
                "The bounded weak-conservation test passed and still requires "
                "result review before any interpretation."
            ),
        },
        {
            "classification": ALLOWED_RESULT_CLASSIFICATIONS[1],
            "selected": False,
            "meaning": (
                "The bounded weak-conservation test exposed an explicit "
                "obstruction requiring a countermodel or scope refinement."
            ),
        },
        {
            "classification": ALLOWED_RESULT_CLASSIFICATIONS[2],
            "selected": True,
            "meaning": (
                "The bounded weak-conservation test was executed against the "
                "packet criteria, but supplied assumptions do not decide pass "
                "or fail."
            ),
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The executed conservation-test attempt must be result-reviewed "
                "before any countermodel, scope refinement, conservation, or "
                "source-admissibility work is authorized."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This bounded conservation-test attempt target is consumed here.",
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_countermodel_packet",
            "decision": "not_selected_pending_result_review",
            "reason": (
                "No explicit failing obstruction is promoted before result review."
            ),
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_scope_refinement_packet",
            "decision": "not_selected_pending_result_review",
            "reason": (
                "The inconclusive result may motivate refinement only after "
                "review accepts the attempt result."
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
            "reason": "The attempt records an inconclusive test result, not a proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by this test attempt.",
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
            "reason": "QFT-GR closure remains outside this bounded test attempt.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _criterion_rows(
    criteria: list[str],
    *,
    satisfied: bool,
    evaluation: str,
    reason: str,
) -> list[dict[str, Any]]:
    return [
        {
            "criterion": criterion,
            "satisfied": satisfied,
            "evaluation": evaluation,
            "reason": reason,
        }
        for criterion in criteria
    ]


def _test_execution_matrix(packet: dict[str, Any]) -> dict[str, Any]:
    criteria = packet.get("pass_fail_inconclusive_criteria", {})
    return {
        "test_result": TEST_RESULT,
        "weak_conservation_scope": packet.get("weak_vs_strong_conservation_scope", {}),
        "test_object_and_domain": packet.get("test_object_and_test_domain", {}),
        "pass_criteria_evaluation": _criterion_rows(
            criteria.get("pass", []),
            satisfied=False,
            evaluation="not_established_under_supplied_assumptions",
            reason=(
                "The packet imports domain, pairing, and regularity support but "
                "does not supply a zero weak-divergence derivation for every "
                "admitted pairing."
            ),
        ),
        "fail_criteria_evaluation": _criterion_rows(
            criteria.get("fail", []),
            satisfied=False,
            evaluation="not_triggered_by_available_artifacts",
            reason=(
                "The available artifacts do not exhibit an explicit nonzero "
                "weak pairing, undefined required pairing, or blocked exchange "
                "step for this bounded candidate."
            ),
        ),
        "inconclusive_criteria_evaluation": _criterion_rows(
            criteria.get("inconclusive", []),
            satisfied=True,
            evaluation="triggered",
            reason=(
                "The test reaches the packet's undecided branch because deciding "
                "zero versus nonzero would require a stronger source-domain, "
                "pairing, or regularity result than this attempt may add."
            ),
        ),
    }


def _why_inconclusive(packet: dict[str, Any]) -> list[str]:
    domain = packet.get("test_object_and_test_domain", {}).get("test_domain", {})
    return [
        (
            "The pairing domain remains "
            f"{domain.get('pairing_domain_status')}, so the attempt cannot "
            "promote imported pairing support to a source-level conservation proof."
        ),
        (
            "The source domain remains "
            f"{domain.get('domain_status')}, and admissible source-domain "
            "membership is not established."
        ),
        (
            "No weak-divergence zero derivation is available for every admitted "
            "test vector under only the packet's supplied assumptions."
        ),
        (
            "No explicit nonzero weak pairing, undefined required pairing, or "
            "blocked exchange row is produced, so the attempt does not classify "
            "as a failure."
        ),
        (
            "No conservation proof object or conservation witness is constructed."
        ),
    ]


def _what_was_tested(packet: dict[str, Any]) -> list[str]:
    return [
        packet.get("conservation_sense_being_tested", {}).get("sense_being_tested", ""),
        "pass criteria for defined weak pairings and zero weak-divergence pairings",
        "fail criteria for explicit nonzero pairing, undefined required pairing, or blocked exchange",
        "inconclusive criteria for insufficient supplied domain, pairing, or regularity strength",
    ]


def _what_was_not_tested() -> list[str]:
    return [
        "strong pointwise covariant conservation",
        "source admissibility",
        "Bianchi compatibility",
        "the semiclassical Einstein equation",
        "QFT-GR source-map or seam closure",
        "empirical validation or public submission readiness",
    ]


def build_qft_gr_minimal_working_model_conservation_test_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_result_review_path)
    packet_pointer = review.get(
        "consumes_qft_gr_minimal_working_model_conservation_test_packet_pointer"
    )
    if not isinstance(packet_pointer, str):
        raise ValueError("Packet result review does not point to its consumed packet")
    packet_path = _resolve_repo_path(packet_pointer)
    packet = _read_json(packet_path)

    candidate_next_targets = _candidate_next_targets()
    classification_rows = _classification_rows()
    execution_matrix = _test_execution_matrix(packet)
    why_inconclusive = _why_inconclusive(packet)

    pass_rows = execution_matrix["pass_criteria_evaluation"]
    fail_rows = execution_matrix["fail_criteria_evaluation"]
    inconclusive_rows = execution_matrix["inconclusive_criteria_evaluation"]

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
        "bounded_attempt_authorized": review.get(
            "bounded_conservation_test_attempt_authorized"
        )
        is True,
        "review_did_not_execute_attempt": review.get(
            "bounded_conservation_test_attempt_executed_by_review"
        )
        is False
        and review.get("conservation_test_executed") is False,
        "consumed_packet_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == EXPECTED_PACKET_ID,
        "consumed_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "consumed_packet_classification_expected": packet.get(
            "packet_classification"
        )
        == EXPECTED_PACKET_CLASSIFICATION,
        "bounded_weak_test_executed_only": (
            packet.get("conservation_sense_being_tested", {}).get("sense_id")
            == "weak_distributional_covariant_conservation_for_toy_candidate"
            and packet.get("weak_vs_strong_conservation_scope", {}).get(
                "scope_decision"
            )
            == "weak_scope_only_for_this_packet"
        ),
        "toy_source_candidate_remains_candidate_only": packet.get(
            "toy_source_candidate_status"
        )
        == TOY_SOURCE_STATUS
        and packet.get("toy_source_candidate_remains_candidate_only") is True,
        "classification_allowed": RESULT_CLASSIFICATION
        in ALLOWED_RESULT_CLASSIFICATIONS,
        "exactly_one_classification_selected": sum(
            1 for row in classification_rows if row["selected"]
        )
        == 1,
        "test_result_inconclusive": execution_matrix["test_result"] == TEST_RESULT
        and bool(inconclusive_rows)
        and all(row["satisfied"] is True for row in inconclusive_rows),
        "pass_not_established": bool(pass_rows)
        and all(row["satisfied"] is False for row in pass_rows),
        "fail_not_triggered": bool(fail_rows)
        and all(row["satisfied"] is False for row in fail_rows),
        "why_inconclusive_recorded": len(why_inconclusive) >= 5,
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
    executed = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": executed,
        "accepted": executed,
        "attempt_executed": executed,
        "bounded_conservation_test_attempt_only": True,
        "outcome_id": OUTCOME_ID
        if executed
        else "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_REQUIRES_REMEDIATION",
        "result_classification": RESULT_CLASSIFICATION
        if executed
        else "qft_gr_minimal_working_model_conservation_test_attempt_requires_remediation",
        "result_classification_count": 1 if executed else 0,
        "allowed_result_classifications": ALLOWED_RESULT_CLASSIFICATIONS,
        "classification_rows": classification_rows,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_test_packet_result_review": (
            EXPECTED_PACKET_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_test_packet_result_review_pointer": _ptr(
            packet_result_review_path
        ),
        "consumed_packet_result_review_outcome_id": review.get("outcome_id"),
        "consumed_packet_result_review_classification": review.get(
            "result_review_classification"
        ),
        "consumes_qft_gr_minimal_working_model_conservation_test_packet": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_test_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "conservation_sense_being_tested": packet.get(
            "conservation_sense_being_tested"
        ),
        "weak_vs_strong_conservation_scope": packet.get(
            "weak_vs_strong_conservation_scope"
        ),
        "test_object_and_test_domain": packet.get("test_object_and_test_domain"),
        "pass_fail_inconclusive_criteria": packet.get(
            "pass_fail_inconclusive_criteria"
        ),
        "test_execution_status": TEST_STATUS,
        "test_execution_matrix": execution_matrix,
        "test_result": TEST_RESULT if executed else "requires_remediation",
        "test_passed": False,
        "test_failed": False,
        "test_inconclusive": executed,
        "conservation_test_executed": executed,
        "conservation_test_result_recorded": executed,
        "conservation_test_result_claimed": False,
        "conservation_test_pass_claimed": False,
        "conservation_test_failure_claimed": False,
        "conservation_test_inconclusive_recorded": executed,
        "conservation_test_attempt_result_review_pending": executed,
        "why_inconclusive": why_inconclusive,
        "what_was_tested": _what_was_tested(packet),
        "what_was_not_tested": _what_was_not_tested(),
        "toy_source_candidate_status": packet.get("toy_source_candidate_status"),
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
        "selected_next_target": NEXT_TARGET
        if executed
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT",
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if executed else 0,
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_"
            "RESULT_ONLY_NO_CONSERVATION_PROOF_WITNESS_SOURCE_ADMISSIBILITY_"
            "BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_"
            "VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This bounded conservation-test attempt executes only the prepared "
            "weak-conservation protocol for the toy source candidate and records "
            "an inconclusive result pending review. It preserves no conservation "
            "claim, no conservation proof object, no conservation witness, no "
            "source admissibility, no Bianchi compatibility, no semiclassical "
            "Einstein equation, no QFT-GR closure, no empirical validation, no "
            "public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_test_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_test_attempt(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model bounded conservation-test "
            "attempt report."
        )
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_PACKET_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_conservation_test_attempt(
        packet_result_review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_test_attempt_report: "
        f"executed={payload['executed']} "
        f"classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
