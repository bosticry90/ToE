from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    TOY_SOURCE_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-12T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_RESULT_REVIEW_"
    "20260612_v0"
)
REVIEW_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_RESULT_REVIEW_"
    "ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_CONSERVATION_TEST_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_test_packet_result_review_"
    "accepts_packet_and_authorizes_bounded_conservation_test_attempt_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "execute_qft_gr_minimal_working_model_conservation_test_attempt"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_conservation_test_attempt_execution_only"
AUTHORIZED_CONSERVATION_TEST_ATTEMPT_CLASSIFICATIONS = [
    "qft_gr_minimal_working_model_conservation_test_attempt_executed_pending_result_review",
    "qft_gr_minimal_working_model_conservation_obstruction_identified_requires_countermodel_or_scope_refinement",
    "qft_gr_minimal_working_model_conservation_test_inconclusive_requires_model_scope_refinement",
]
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_RESULT_REVIEW_20260612_v0.json"
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
                "The conservation-test packet is accepted as a protocol, so "
                "the next bounded action may execute only that test attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This conservation-test packet result-review target is consumed here.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains a candidate only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The review authorizes a bounded test attempt, not a proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized by review.",
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


def build_qft_gr_minimal_working_model_conservation_test_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    conservation_sense = packet.get("conservation_sense_being_tested", {})
    weak_strong_scope = packet.get("weak_vs_strong_conservation_scope", {})
    test_object_and_domain = packet.get("test_object_and_test_domain", {})
    criteria = packet.get("pass_fail_inconclusive_criteria", {})
    candidate_next_targets = _candidate_next_targets()

    acceptance_criteria = {
        "consumes_expected_conservation_test_packet": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_result_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_preparation_only_confirmed": packet.get("packet_preparation_only")
        is True
        and packet.get("conservation_test_executed") is False,
        "conservation_sense_defined": conservation_sense.get("sense_id")
        == "weak_distributional_covariant_conservation_for_toy_candidate",
        "weak_scope_only_confirmed": weak_strong_scope.get("scope_decision")
        == "weak_scope_only_for_this_packet"
        and weak_strong_scope.get("strong_conservation_claimed") is False,
        "test_object_and_domain_defined": test_object_and_domain.get(
            "test_object_status"
        )
        == TOY_SOURCE_STATUS
        and test_object_and_domain.get("test_domain", {}).get(
            "admissible_source_domain_established"
        )
        is False,
        "pass_fail_inconclusive_defined": set(criteria) == {
            "pass",
            "fail",
            "inconclusive",
        },
        "passing_not_source_admissibility_recorded": len(
            packet.get("why_passing_does_not_imply_source_admissibility", [])
        )
        >= 3,
        "failure_routing_recorded": len(
            packet.get("why_failing_routes_to_countermodel_or_scope_refinement", [])
        )
        >= 3,
        "toy_source_remains_candidate_only": packet.get("toy_source_candidate_status")
        == TOY_SOURCE_STATUS
        and packet.get("toy_source_candidate_remains_candidate_only") is True,
        "no_source_admissibility_claim": packet.get("source_admissibility_claimed")
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": packet.get("conservation_claimed")
        is False
        and packet.get("conservation_proved") is False
        and packet.get("conservation_proof_object_constructed") is False
        and packet.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": packet.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and packet.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": packet.get("qft_gr_seam_closed") is False
        and packet.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": packet.get(
            "empirical_validation_claimed"
        )
        is False
        and packet.get("public_submission_authorized") is False,
        "no_master_action_promotion": packet.get("master_action_promoted") is False
        and packet.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_RESULT_REVIEW"
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
        else "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_conservation_test_packet_result_review_requires_remediation",
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_test_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_minimal_working_model_conservation_test_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "packet_result_review_accepted": accepted,
        "packet_preparation_only_confirmed": accepted,
        "bounded_conservation_test_attempt_authorized": accepted,
        "bounded_conservation_test_attempt_executed_by_review": False,
        "conservation_test_executed": False,
        "conservation_test_result_claimed": False,
        "conservation_sense_being_tested": conservation_sense,
        "weak_vs_strong_conservation_scope": weak_strong_scope,
        "test_object_and_test_domain": test_object_and_domain,
        "pass_fail_inconclusive_criteria": criteria,
        "why_passing_does_not_imply_source_admissibility": packet.get(
            "why_passing_does_not_imply_source_admissibility", []
        ),
        "why_failing_routes_to_countermodel_or_scope_refinement": packet.get(
            "why_failing_routes_to_countermodel_or_scope_refinement", []
        ),
        "conservation_test_attempt_result_classifications": (
            AUTHORIZED_CONSERVATION_TEST_ATTEMPT_CLASSIFICATIONS
        ),
        "conservation_test_attempt_result_classification_count": len(
            AUTHORIZED_CONSERVATION_TEST_ATTEMPT_CLASSIFICATIONS
        ),
        "toy_source_candidate_status": packet.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": accepted,
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
        "aggregate_lean_timeout_caveat_preserved": packet.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": packet.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_"
            "ONLY_NO_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_WITNESS_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_"
            "PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the prepared conservation-test "
            "packet and authorizes one bounded conservation-test attempt. It "
            "does not execute the test and preserves no source admissibility, "
            "no conservation claim, no conservation proof object, no "
            "conservation witness, no Bianchi compatibility, no semiclassical "
            "Einstein equation, no QFT-GR closure, no empirical validation, "
            "no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_test_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_test_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model conservation-test "
            "packet result review."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_conservation_test_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_test_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
