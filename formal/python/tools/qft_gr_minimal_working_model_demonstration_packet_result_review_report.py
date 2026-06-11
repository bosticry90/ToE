from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    REVIEW_TARGET as CONSUMED_TARGET,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.qft_gr_post_mr_assump004_governed_maturation_reports import (
    CAPTURED_AT_UTC,
    COMPLETED_FAMILIES_AFTER_MR,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_RESULT_REVIEW_"
    "20260610_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_MODEL_CONSTRUCTION_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_demonstration_packet_result_review_"
    "accepts_packet_and_authorizes_bounded_model_construction_attempt_only"
)
NEXT_TARGET = "execute_qft_gr_minimal_working_model_construction_attempt"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_construction_attempt_execution_only"
AUTHORIZED_CONSTRUCTION_ATTEMPT_CLASSIFICATIONS = [
    "qft_gr_minimal_working_model_candidate_constructed_pending_result_review",
    "qft_gr_minimal_working_model_obstruction_identified_requires_scope_refinement",
    "qft_gr_minimal_working_model_inconclusive_requires_countermodel_or_assumption_reduction",
]
AGGREGATE_LEAN_TIMEOUT_CAVEAT = (
    "full lake build ToeFormal timed out after repair and rerun attempt; "
    "targeted Lean packet/frontier/historical modules passed"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_RESULT_REVIEW_"
        "20260610_v0.json"
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
                "The packet is accepted as preparation only, so the next "
                "bounded action is a construction attempt for the minimal "
                "working model. This review does not execute that attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This packet result-review target is consumed here.",
        },
        {
            "target": "execute_qft_gr_minimal_working_model_demonstration",
            "decision": "not_authorized_without_construction_attempt",
            "reason": (
                "The packet review authorizes construction-attempt execution "
                "only, not a broader model demonstration execution."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains a candidate only.",
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": "No conservation proof object is constructed or authorized.",
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
            "reason": "QFT-GR closure remains outside this checkpoint.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def build_qft_gr_minimal_working_model_demonstration_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    nonclaims = packet.get("non_claim_boundary", {})
    toy_source_candidate = packet.get("toy_source_candidate", {})
    admissibility_candidate = packet.get("admissibility_candidate_only", {})
    conservation_test_target = packet.get("conservation_test_target", {})
    scope = packet.get("minimal_model_scope", {})

    acceptance_criteria = {
        "consumes_expected_minimal_model_packet_json": packet.get("schema_id")
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
        and packet.get("model_execution_authorized") is False,
        "minimal_model_scope_is_bounded": scope.get("model_class")
        == "free scalar-field stress-energy-like candidate"
        and scope.get("scope") == "fixed controlled background with no backreaction",
        "toy_source_candidate_remains_candidate_only": toy_source_candidate.get(
            "status"
        )
        == "candidate_only_not_source_admissibility"
        and toy_source_candidate.get("source_admissibility_claimed") is False,
        "admissibility_candidate_only_preserved": admissibility_candidate.get(
            "admissibility_claimed"
        )
        is False
        and admissibility_candidate.get("source_map_closure_claimed") is False,
        "imports_completed_assumption_families": packet.get(
            "imported_assumption_families"
        )
        == COMPLETED_FAMILIES_AFTER_MR,
        "no_conservation_witness_or_proof_object": conservation_test_target.get(
            "conservation_proved"
        )
        is False
        and conservation_test_target.get("conservation_witness_constructed") is False
        and nonclaims.get("conservation_proof_object_constructed") is False,
        "no_source_admissibility_claim": nonclaims.get("source_admissibility_claimed")
        is False
        and nonclaims.get("stress_energy_source_admissibility_claimed") is False,
        "no_bianchi_compatibility": nonclaims.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_equation": nonclaims.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_closure": nonclaims.get("qft_gr_seam_closed") is False,
        "no_empirical_validation_or_public_submission": nonclaims.get(
            "empirical_validation_claimed"
        )
        is False
        and nonclaims.get("public_submission_authorized") is False,
        "no_master_action_promotion": nonclaims.get("master_action_promoted") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_RESULT_REVIEW"
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
        else "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_demonstration_packet_result_review_requires_remediation",
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_demonstration_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_minimal_working_model_demonstration_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "packet_preparation_only_confirmed_by_review": accepted,
        "minimal_model_scope_bounded": accepted,
        "toy_source_candidate_status": toy_source_candidate.get("status"),
        "toy_source_candidate_remains_candidate_only": accepted,
        "bounded_model_construction_attempt_authorized": accepted,
        "bounded_model_construction_attempt_executed_by_review": False,
        "minimal_model_demonstration_executed_by_review": False,
        "model_execution_authorized_by_review": False,
        "construction_attempt_result_classifications": (
            AUTHORIZED_CONSTRUCTION_ATTEMPT_CLASSIFICATIONS
        ),
        "construction_attempt_result_classification_count": len(
            AUTHORIZED_CONSTRUCTION_ATTEMPT_CLASSIFICATIONS
        ),
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
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
        "validation_caveat": AGGREGATE_LEAN_TIMEOUT_CAVEAT,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "packet_result_review_selected_target_split_preserved": (
            accepted and selected_next_target != CONSUMED_TARGET
        ),
        "next_action_scope": (
            "EXECUTE_QFT_GR_MINIMAL_WORKING_MODEL_CONSTRUCTION_ATTEMPT_ONLY_"
            "NO_SOURCE_ADMISSIBILITY_CONSERVATION_WITNESS_BIANCHI_SEE_QFT_GR_"
            "CLOSURE_EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the prepared QFT-GR minimal "
            "working model demonstration packet and authorizes one bounded "
            "model-construction attempt. It preserves no source admissibility, "
            "no conservation proof object, no conservation witness, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, no empirical validation, no master-action promotion, no "
            "release assembly, and no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_demonstration_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_demonstration_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model demonstration packet "
            "result review."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_demonstration_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_demonstration_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
