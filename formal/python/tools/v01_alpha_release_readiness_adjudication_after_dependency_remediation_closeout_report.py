from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_EXECUTION_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_report import (
    CRITICIZABILITY_QUESTION,
    EXECUTION_CLASSIFICATIONS,
    REQUIRED_BOUNDARY,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_20260525_v0"
)
EXECUTION_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_EXECUTED_WITH_NO_RELEASE_ASSEMBLY_OR_PROMOTION"
)
EXECUTION_CLASSIFICATION = (
    "v01_alpha_criticizability_readiness_eligible_pending_result_review"
)
CONSUMED_TARGET = (
    "execute_v01_alpha_release_readiness_adjudication_after_dependency_"
    "remediation_closeout"
)
NEXT_TARGET = (
    "review_v01_alpha_release_readiness_adjudication_after_dependency_"
    "remediation_closeout_result"
)
CRITICIZABILITY_READINESS_STATUS = (
    "v01_alpha_criticizability_readiness_eligible_pending_result_review"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_20260525_v0.json"
    )
)

FORBIDDEN_EFFECTS = [
    "canonical_toe_claimed",
    "claim_promotion_authorized",
    "empirical_validation_authorized",
    "empirical_validation_claimed",
    "lean_theorem_debt_discharged",
    "master_action_promotion_authorized",
    "phase2_authorized",
    "proof_debt_reduced",
    "public_submission_authorized",
    "publication_authorized",
    "qft_gr_seam_closed",
    "qft_gr_seam_closure_authorized",
    "qft_gr_seam_closure_claimed",
    "qft_gr_source_map_semantic_closure_claimed",
    "readiness_marking_authorized",
    "release_assembly_authorized",
    "release_packet_assembled",
    "retained_assumptions_discharged",
    "scientific_validation_claimed",
    "source_map_seam_pillar_master_action_promotion_authorized",
    "theorem_discharge_authorized",
    "track2_scientific_evidence_claimed_from_track1",
    "track2_started",
    "v01_alpha_marked_ready",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded criticizability-readiness execution must be result-"
                "reviewed before any later release-control step."
            ),
        },
        {
            "target": (
                "construct_or_refute_qft_gr_conserved_renormalized_stress_"
                "energy_source_witness"
            ),
            "decision": "deferred",
            "reason": "Track 2 remains deferred unless explicitly selected after result review.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly is not authorized by criticizability execution.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Readiness marking requires a separate reviewed authorization.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission remains outside this bounded execution.",
        },
    ]


def build_release_readiness_adjudication_after_dependency_remediation_closeout(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_result_review_path)
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_packet_result_review": review.get("review_id")
        == EXPECTED_PACKET_RESULT_REVIEW_ID,
        "packet_result_review_schema_expected": review.get("schema_id")
        == EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
        "packet_result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
        "packet_result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
        "packet_result_review_selected_this_execution": review.get("selected_next_target")
        == CONSUMED_TARGET
        and EXPECTED_EXECUTION_TARGET == CONSUMED_TARGET,
        "execution_authorized_not_already_executed": review.get(
            "criticizability_readiness_adjudication_execution_authorized"
        )
        is True
        and review.get("criticizability_readiness_adjudication_executed") is False
        and review.get("criticizability_readiness_decision_made") is False,
        "dependency_remediation_closeout_accepted": review.get(
            "dependency_remediation_closeout_accepted"
        )
        is True
        and review.get("dependency_remediation_queue_closed") is True
        and review.get("all_dependency_tranches_nonblocking") is True
        and review.get("documented_dependency_nonblocking_tranche_count") == 6,
        "classification_is_one_exact_execution_option": EXECUTION_CLASSIFICATION
        in EXECUTION_CLASSIFICATIONS
        and sum(1 for item in EXECUTION_CLASSIFICATIONS if item == EXECUTION_CLASSIFICATION)
        == 1,
        "executes_criticizability_readiness_only": bool(CRITICIZABILITY_QUESTION)
        and bool(REQUIRED_BOUNDARY),
        "no_release_assembly_public_submission_or_science_claim": all(
            forbidden_effect_status[key] is False
            for key in [
                "release_assembly_authorized",
                "release_packet_assembled",
                "public_submission_authorized",
                "publication_authorized",
                "scientific_validation_claimed",
            ]
        ),
        "no_qft_gr_or_promotion": all(
            forbidden_effect_status[key] is False
            for key in [
                "qft_gr_seam_closed",
                "qft_gr_seam_closure_authorized",
                "qft_gr_seam_closure_claimed",
                "qft_gr_source_map_semantic_closure_claimed",
                "source_map_seam_pillar_master_action_promotion_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "track2_not_started": forbidden_effect_status["track2_started"] is False
        and review.get("track2_remains_deferred") is True,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "execution_id": EXECUTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_"
            "REMEDIATION_CLOSEOUT_BLOCKED"
        ),
        "consumes_criticizability_readiness_packet_result_review": (
            EXPECTED_PACKET_RESULT_REVIEW_ID
        ),
        "consumes_criticizability_readiness_packet_result_review_pointer": _ptr(
            packet_result_review_path
        ),
        "consumed_packet_result_review_schema_id": review.get("schema_id"),
        "consumed_packet_result_review_outcome_id": review.get("outcome_id"),
        "consumed_packet_result_review_classification": review.get(
            "result_review_classification"
        ),
        "execution_scope": (
            "EXECUTE_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_AFTER_"
            "DEPENDENCY_REMEDIATION_CLOSEOUT_ONLY_NO_RELEASE_ASSEMBLY_OR_"
            "SCIENTIFIC_VALIDATION"
        ),
        "execution_classification": EXECUTION_CLASSIFICATION,
        "execution_classification_count": 1 if accepted else 0,
        "criticizability_readiness_adjudication_executed": accepted,
        "criticizability_readiness_execution_only": accepted,
        "criticizability_readiness_question": CRITICIZABILITY_QUESTION,
        "criticizability_readiness_question_answered": accepted,
        "criticizability_readiness_decision_made": accepted,
        "criticizability_readiness_decision": CRITICIZABILITY_READINESS_STATUS,
        "criticizability_readiness_status": CRITICIZABILITY_READINESS_STATUS,
        "criticizability_readiness_result_review_required": accepted,
        "required_boundary": REQUIRED_BOUNDARY,
        "dependency_remediation_closeout_accepted": accepted,
        "dependency_remediation_queue_closed": accepted,
        "all_dependency_tranches_nonblocking": accepted,
        "documented_dependency_nonblocking_tranche_count": review.get(
            "documented_dependency_nonblocking_tranche_count"
        ),
        "release_readiness_eligible_for_bounded_criticizability_treatment": accepted,
        "release_readiness_marked": False,
        "release_readiness_held": False,
        "release_readiness_inconclusive": False,
        "release_readiness_requires_refinement": False,
        "release_readiness_proceed_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "source_map_seam_pillar_master_action_promotion_authorized": False,
        "lean_theorem_debt_discharged": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "theorem_discharge_authorized": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promotion_authorized": False,
        "canonical_toe_claimed": False,
        "track2_qft_gr_witness_target": review.get("track2_qft_gr_witness_target"),
        "track2_started": False,
        "track2_remains_deferred": True,
        "track2_selected_after_this_execution": False,
        "track2_scientific_evidence_claimed_from_track1": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_"
            "DEPENDENCY_REMEDIATION_CLOSEOUT"
        ),
        "selected_next_target_kind": (
            "criticizability_readiness_adjudication_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_ONLY_"
            "NO_RELEASE_ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha criticizability-readiness adjudication execution "
            "decides only that v0.1-alpha is eligible for bounded "
            "criticizability treatment pending result review. It does not mark "
            "release readiness, assemble release, authorize public submission, "
            "close the QFT-GR seam, start Track 2, promote source-map/seam/"
            "pillar/master-action status, validate scientifically, or claim "
            "external truth."
        ),
        "roadmap_update_required": True,
    }


def write_release_readiness_adjudication_after_dependency_remediation_closeout(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_release_readiness_adjudication_after_dependency_remediation_closeout(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha criticizability-readiness adjudication "
            "execution after dependency-remediation closeout."
        )
    )
    parser.add_argument(
        "--packet-result-review",
        type=Path,
        default=DEFAULT_PACKET_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_result_review_path = (
        ns.packet_result_review
        if ns.packet_result_review.is_absolute()
        else (REPO_ROOT / ns.packet_result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_release_readiness_adjudication_after_dependency_remediation_closeout(
        packet_result_review_path=packet_result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_release_readiness_adjudication_after_dependency_"
        "remediation_closeout_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['execution_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
