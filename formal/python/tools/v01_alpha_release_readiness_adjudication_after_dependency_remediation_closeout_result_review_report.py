from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_report import (
    CRITICIZABILITY_READINESS_STATUS as EXPECTED_CRITICIZABILITY_STATUS,
    DEFAULT_OUT as DEFAULT_EXECUTION_PATH,
    EXECUTION_CLASSIFICATION as EXPECTED_EXECUTION_CLASSIFICATION,
    EXECUTION_ID as EXPECTED_EXECUTION_ID,
    FORBIDDEN_EFFECTS as EXECUTION_FORBIDDEN_EFFECTS,
    NEXT_TARGET as EXPECTED_RESULT_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_EXECUTION_OUTCOME,
    SCHEMA_ID as EXPECTED_EXECUTION_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW_"
    "20260525_v0"
)
REVIEW_ID = "V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW_ACCEPTS_"
    "ELIGIBILITY_AND_AUTHORIZES_QFT_GR_WITNESS_PACKET_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "v01_alpha_criticizability_readiness_result_review_accepts_eligibility_"
    "and_authorizes_qft_gr_witness_packet_preparation_only_no_release_assembly_"
    "or_scientific_validation"
)
CONSUMED_TARGET = (
    "review_v01_alpha_release_readiness_adjudication_after_dependency_"
    "remediation_closeout_result"
)
NEXT_TARGET = (
    "prepare_qft_gr_conserved_renormalized_stress_energy_source_witness_packet"
)
CRITICIZABILITY_READINESS_REVIEW_DECISION = (
    "criticizability_readiness_eligibility_accepted"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW_20260525_v0.json"
)

FORBIDDEN_EFFECTS = sorted(
    set(EXECUTION_FORBIDDEN_EFFECTS)
    | {
        "qft_gr_witness_packet_prepared_by_review",
        "qft_gr_witness_executed_by_review",
        "track2_science_lane_execution_started_by_review",
        "release_readiness_marked_by_review",
        "release_assembly_authorized_by_review",
    }
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
                "The criticizability-readiness eligibility result is accepted, "
                "so the next bounded step prepares a QFT-GR witness packet only."
            ),
        },
        {
            "target": (
                "execute_qft_gr_conserved_renormalized_stress_energy_source_witness"
            ),
            "decision": "not_authorized",
            "reason": "Track 2 execution requires a separately reviewed packet.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly is not authorized by this result review.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission remains outside this bounded review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "A witness packet is not QFT-GR seam closure.",
        },
    ]


def build_release_readiness_adjudication_result_review(
    *,
    execution_path: Path = DEFAULT_EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(execution_path)
    candidate_next_targets = _candidate_next_targets()
    execution_forbidden = dict(execution.get("forbidden_effect_status", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_execution_artifact": execution.get("execution_id")
        == EXPECTED_EXECUTION_ID,
        "execution_schema_expected": execution.get("schema_id")
        == EXPECTED_EXECUTION_SCHEMA_ID,
        "execution_outcome_expected": execution.get("outcome_id")
        == EXPECTED_EXECUTION_OUTCOME,
        "execution_selected_this_review": execution.get("selected_next_target")
        == CONSUMED_TARGET
        and EXPECTED_RESULT_REVIEW_TARGET == CONSUMED_TARGET,
        "classification_is_expected_eligible_pending_review": execution.get(
            "execution_classification"
        )
        == EXPECTED_EXECUTION_CLASSIFICATION
        and execution.get("criticizability_readiness_status")
        == EXPECTED_CRITICIZABILITY_STATUS
        and execution.get("execution_classification_count") == 1,
        "criticizability_execution_completed": execution.get(
            "criticizability_readiness_adjudication_executed"
        )
        is True
        and execution.get("criticizability_readiness_decision_made") is True
        and execution.get("criticizability_readiness_result_review_required") is True,
        "eligibility_accepted_without_release_readiness_marking": execution.get(
            "release_readiness_eligible_for_bounded_criticizability_treatment"
        )
        is True
        and execution.get("release_readiness_marked") is False
        and execution.get("readiness_marking_authorized") is False
        and execution.get("v01_alpha_marked_ready") is False,
        "no_release_assembly_or_public_submission": execution.get(
            "release_assembly_authorized"
        )
        is False
        and execution.get("release_packet_assembled") is False
        and execution.get("public_submission_authorized") is False
        and execution.get("publication_authorized") is False,
        "no_scientific_validation_or_qft_gr_closure": execution.get(
            "scientific_validation_claimed"
        )
        is False
        and execution.get("qft_gr_seam_closed") is False
        and execution.get("qft_gr_seam_closure_authorized") is False
        and execution.get("qft_gr_seam_closure_claimed") is False,
        "no_source_map_seam_pillar_or_master_action_promotion": execution.get(
            "qft_gr_source_map_semantic_closure_claimed"
        )
        is False
        and execution.get("source_map_seam_pillar_master_action_promotion_authorized")
        is False
        and execution.get("master_action_promotion_authorized") is False
        and execution.get("canonical_toe_claimed") is False,
        "no_theorem_proof_phase2_or_empirical_discharge": execution.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and execution.get("proof_debt_reduced") is False
        and execution.get("retained_assumptions_discharged") is False
        and execution.get("theorem_discharge_authorized") is False
        and execution.get("phase2_authorized") is False
        and execution.get("empirical_validation_authorized") is False
        and execution.get("empirical_validation_claimed") is False,
        "track2_selected_only_as_separate_packet_preparation": execution.get(
            "track2_started"
        )
        is False
        and execution.get("track2_remains_deferred") is True
        and forbidden_effect_status["track2_science_lane_execution_started_by_review"]
        is False,
        "forbidden_execution_effects_remain_false": all(
            execution_forbidden.get(effect) is False for effect in EXECUTION_FORBIDDEN_EFFECTS
        ),
        "review_forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
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
        else "V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW_BLOCKED",
        "consumes_criticizability_readiness_execution": EXPECTED_EXECUTION_ID,
        "consumes_criticizability_readiness_execution_pointer": _ptr(execution_path),
        "consumed_execution_schema_id": execution.get("schema_id"),
        "consumed_execution_outcome_id": execution.get("outcome_id"),
        "consumed_execution_classification": execution.get("execution_classification"),
        "review_scope": (
            "REVIEW_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_ONLY_"
            "ACCEPT_ELIGIBILITY_AUTHORIZE_QFT_GR_WITNESS_PACKET_PREPARATION_NO_"
            "RELEASE_ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "criticizability_readiness_result_reviewed": accepted,
        "criticizability_readiness_eligibility_accepted": accepted,
        "criticizability_readiness_eligibility_rejected": False,
        "criticizability_readiness_review_decision": (
            CRITICIZABILITY_READINESS_REVIEW_DECISION if accepted else "blocked"
        ),
        "criticizability_readiness_status": EXPECTED_CRITICIZABILITY_STATUS,
        "criticizability_readiness_execution_classification": (
            EXPECTED_EXECUTION_CLASSIFICATION
        ),
        "release_readiness_eligible_for_bounded_criticizability_treatment": accepted,
        "release_readiness_marked": False,
        "release_readiness_proceed_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "qft_gr_witness_packet_preparation_authorized": accepted,
        "qft_gr_witness_packet_prepared": False,
        "qft_gr_witness_execution_authorized": False,
        "qft_gr_witness_executed": False,
        "qft_gr_witness_packet_target": NEXT_TARGET,
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
        "track2_started": False,
        "track2_selected_after_result_review": accepted,
        "track2_selection_kind": "qft_gr_witness_packet_preparation_only",
        "track2_science_lane_execution_started": False,
        "track2_scientific_evidence_claimed_from_track1": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW",
        "selected_next_target_kind": "qft_gr_witness_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
            "PACKET_ONLY_NO_TRACK2_EXECUTION_RELEASE_ASSEMBLY_OR_SCIENTIFIC_"
            "VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha criticizability-readiness adjudication result "
            "review accepts eligibility only for bounded criticizability "
            "treatment and authorizes only QFT-GR witness packet preparation. "
            "It does not assemble release, authorize public submission, claim "
            "scientific validation, close the QFT-GR seam, promote source-map/"
            "seam/pillar/master-action status, discharge theorem or proof "
            "debt, authorize Phase 2, validate empirically, or execute Track 2."
        ),
        "roadmap_update_required": True,
    }


def write_release_readiness_adjudication_result_review(
    *,
    execution_path: Path = DEFAULT_EXECUTION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_release_readiness_adjudication_result_review(
        execution_path=execution_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha criticizability-readiness adjudication "
            "result review after dependency-remediation closeout."
        )
    )
    parser.add_argument("--execution", type=Path, default=DEFAULT_EXECUTION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    execution_path = (
        ns.execution if ns.execution.is_absolute() else (REPO_ROOT / ns.execution)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_release_readiness_adjudication_result_review(
        execution_path=execution_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_release_readiness_adjudication_after_dependency_"
        "remediation_closeout_result_review_report: "
        f"accepted={payload['accepted']} decision="
        f"{payload['criticizability_readiness_review_decision']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
