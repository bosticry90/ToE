from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_report import (
    CRITICIZABILITY_QUESTION,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    EXECUTION_CLASSIFICATIONS,
    FORBIDDEN_EFFECTS,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    REQUIRED_BOUNDARY,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_PACKET_RESULT_REVIEW_20260525_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "CRITICIZABILITY_ONLY_PACKET_AND_AUTHORIZES_READINESS_ADJUDICATION_"
    "EXECUTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "criticizability_readiness_packet_result_review_accepts_packet_and_"
    "authorizes_readiness_adjudication_execution_only_no_release_assembly_or_"
    "seam_promotion"
)
CONSUMED_TARGET = (
    "review_v01_alpha_release_readiness_adjudication_after_dependency_"
    "remediation_closeout_packet_result"
)
NEXT_TARGET = (
    "execute_v01_alpha_release_readiness_adjudication_after_dependency_"
    "remediation_closeout"
)
CRITICIZABILITY_READINESS_PACKET_RESULT_REVIEW_STATUS = (
    "criticizability_readiness_packet_result_review_accepted_execution_authorized_only"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_PACKET_RESULT_REVIEW_20260525_v0.json"
    )
)


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
                "The criticizability-readiness packet is accepted for execution "
                "of the bounded readiness adjudication only."
            ),
        },
        {
            "target": (
                "construct_or_refute_qft_gr_conserved_renormalized_stress_"
                "energy_source_witness"
            ),
            "decision": "deferred",
            "reason": "Track 2 remains deferred because this review selected Track 1 execution.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains outside this packet result review.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Readiness marking requires execution and result review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure is scientifically separate and not selected.",
        },
    ]


def build_release_readiness_adjudication_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_criticizability_packet": packet.get("packet_id")
        == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION
        and packet.get("packet_classification_count") == 1,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "dependency_remediation_closeout_accepted": packet.get(
            "dependency_remediation_closeout_accepted"
        )
        is True
        and packet.get("dependency_remediation_queue_closed") is True
        and packet.get("all_dependency_tranches_nonblocking") is True
        and packet.get("documented_dependency_nonblocking_tranche_count") == 6,
        "packet_preparation_only": packet.get("accepted") is True
        and packet.get("prepared") is True
        and packet.get("criticizability_readiness_adjudication_packet_prepared") is True
        and packet.get("criticizability_readiness_question") == CRITICIZABILITY_QUESTION
        and packet.get("criticizability_readiness_question_prepared") is True
        and packet.get("criticizability_readiness_question_answered") is False
        and packet.get("criticizability_readiness_decision_made") is False,
        "no_release_assembly_public_submission_or_qft_gr_closure": packet.get(
            "release_assembly_authorized"
        )
        is False
        and packet.get("release_packet_assembled") is False
        and packet.get("public_submission_authorized") is False
        and packet.get("publication_authorized") is False
        and packet.get("qft_gr_seam_closed") is False
        and packet.get("qft_gr_seam_closure_authorized") is False
        and packet.get("qft_gr_seam_closure_claimed") is False,
        "no_source_map_seam_pillar_or_master_action_promotion": packet.get(
            "qft_gr_source_map_semantic_closure_claimed"
        )
        is False
        and packet.get("master_action_promotion_authorized") is False
        and packet.get("canonical_toe_claimed") is False
        and packet.get("scientific_validation_claimed") is False,
        "track2_deferred_unless_explicitly_selected_after_review": packet.get(
            "track2_qft_gr_witness_target_deferred_until_result_review"
        )
        is True
        and packet.get("track2_scientific_evidence_claimed_from_track1") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
        "execution_options_carried_without_decision": packet.get(
            "execution_classification_options"
        )
        == EXECUTION_CLASSIFICATIONS
        and len(EXECUTION_CLASSIFICATIONS) == 3,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_"
            "BLOCKED"
        ),
        "consumes_criticizability_readiness_packet": EXPECTED_PACKET_ID,
        "consumes_criticizability_readiness_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "review_scope": (
            "REVIEW_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_PACKET_"
            "RESULT_ONLY_AUTHORIZE_READINESS_ADJUDICATION_EXECUTION_NO_RELEASE_"
            "ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "criticizability_readiness_packet_result_reviewed": accepted,
        "criticizability_readiness_packet_accepted": accepted,
        "criticizability_readiness_packet_prepared_only": accepted,
        "criticizability_readiness_adjudication_packet_prepared": accepted,
        "criticizability_readiness_adjudication_execution_authorized": accepted,
        "criticizability_readiness_adjudication_executed": False,
        "criticizability_readiness_decision_made": False,
        "criticizability_readiness_question": CRITICIZABILITY_QUESTION,
        "criticizability_readiness_question_answered": False,
        "criticizability_readiness_status": (
            CRITICIZABILITY_READINESS_PACKET_RESULT_REVIEW_STATUS
        ),
        "required_boundary": REQUIRED_BOUNDARY,
        "dependency_remediation_closeout_accepted": accepted,
        "dependency_remediation_queue_closed": accepted,
        "all_dependency_tranches_nonblocking": accepted,
        "documented_dependency_nonblocking_tranche_count": packet.get(
            "documented_dependency_nonblocking_tranche_count"
        ),
        "execution_classification_options": EXECUTION_CLASSIFICATIONS,
        "execution_classification_option_count": len(EXECUTION_CLASSIFICATIONS),
        "execution_classification_selected": None,
        "release_readiness_adjudication_preparation_authorized": True,
        "release_readiness_adjudication_prepared": True,
        "release_readiness_eligible_for_adjudication": False,
        "release_readiness_still_requires_separate_adjudication": True,
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
        "scientific_validation_claimed": False,
        "master_action_promotion_authorized": False,
        "canonical_toe_claimed": False,
        "track2_qft_gr_witness_target": packet.get("track2_qft_gr_witness_target"),
        "track2_remains_deferred": True,
        "track2_selected_after_this_review": False,
        "track2_scientific_evidence_claimed_from_track1": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_V01_ALPHA_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_"
            "REVIEW"
        ),
        "selected_next_target_kind": (
            "criticizability_readiness_adjudication_execution_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_ONLY_NO_"
            "RELEASE_ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha criticizability-readiness packet result review "
            "accepts the packet and authorizes only bounded readiness "
            "adjudication execution. It does not make the readiness decision, "
            "mark release readiness, assemble release, authorize public "
            "submission, close the QFT-GR seam, promote source-map/seam/"
            "pillar/master-action status, select Track 2, or claim scientific "
            "validation."
        ),
        "roadmap_update_required": True,
    }


def write_release_readiness_adjudication_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_release_readiness_adjudication_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha criticizability-readiness adjudication "
            "packet result review after dependency-remediation closeout."
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
    payload = write_release_readiness_adjudication_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_release_readiness_adjudication_after_dependency_"
        "remediation_closeout_packet_result_review_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
