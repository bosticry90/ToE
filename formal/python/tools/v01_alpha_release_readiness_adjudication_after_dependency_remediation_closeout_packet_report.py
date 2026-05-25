from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_result_review_report import (
    DEFAULT_OUT as DEFAULT_CLOSEOUT_RESULT_REVIEW_PATH,
    DEPENDENCY_REMEDIATION_CLOSEOUT_ACCEPTED_STATUS,
    OUTCOME_ID as EXPECTED_CLOSEOUT_RESULT_REVIEW_OUTCOME,
    RELEASE_READINESS_STATUS as EXPECTED_RELEASE_READINESS_STATUS,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_CLOSEOUT_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_CLOSEOUT_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    SELECTED_TRANCHE_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_report import (
    REGISTERED_TRANCHE_004_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_PACKET_20260525_v0"
)
PACKET_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_PACKET_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
    "CLOSEOUT_PACKET_PREPARED_CRITICIZABILITY_ONLY_NO_RELEASE_ASSEMBLY_OR_"
    "SEAM_PROMOTION"
)
PACKET_CLASSIFICATION = (
    "criticizability_readiness_adjudication_packet_prepared_after_dependency_"
    "remediation_closeout_no_release_assembly_or_seam_promotion"
)
CONSUMED_TARGET = (
    "prepare_v01_alpha_release_readiness_adjudication_after_dependency_"
    "remediation_closeout"
)
NEXT_TARGET = (
    "review_v01_alpha_release_readiness_adjudication_after_dependency_"
    "remediation_closeout_packet_result"
)
CRITICIZABILITY_QUESTION = (
    "Is v0.1-alpha eligible for criticizability-readiness adjudication after "
    "dependency-remediation closeout?"
)
REQUIRED_BOUNDARY = (
    "Even if criticizability-readiness is accepted, the result authorizes only "
    "a bounded review/research next step, not public submission, release "
    "assembly, physics closure, claim promotion, or scientific validation."
)
CRITICIZABILITY_READINESS_PACKET_STATUS = (
    "criticizability_readiness_adjudication_packet_prepared_pending_result_review"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_PACKET_20260525_v0.json"
    )
)

EXECUTION_CLASSIFICATIONS = [
    "v01_alpha_criticizability_readiness_eligible_pending_result_review",
    "v01_alpha_criticizability_readiness_not_eligible_requires_refinement",
    "v01_alpha_criticizability_readiness_inconclusive_requires_gap_review",
]

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
    "semiclassical_einstein_equation_derivation_claimed",
    "theorem_discharge_authorized",
    "track2_scientific_evidence_claimed_from_track1",
    "v01_alpha_marked_ready",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _documented_dependency_nonblocking_tranches() -> list[dict[str, str]]:
    return [
        {"finding_id": "V01-ALPHA-DEP-REM-001", "status": TRANCHE_001_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-002", "status": TRANCHE_002_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-003", "status": TRANCHE_003_STATUS},
        {
            "finding_id": "V01-ALPHA-DEP-REM-004",
            "tranche_id": SELECTED_TRANCHE_ID,
            "status": REGISTERED_TRANCHE_004_STATUS,
        },
        {"finding_id": "V01-ALPHA-DEP-REM-005", "status": TRANCHE_005_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-006", "status": TRANCHE_006_STATUS},
    ]


def _packet_preparation_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion": "dependency_remediation_closeout_accepted",
            "status": "satisfied",
            "evidence": (
                "The closeout result review accepted all six dependency "
                "tranches as documented nonblocking at the control layer."
            ),
        },
        {
            "criterion": "criticizability_question_scoped",
            "status": "satisfied",
            "evidence": CRITICIZABILITY_QUESTION,
        },
        {
            "criterion": "release_assembly_forbidden",
            "status": "preserved",
            "evidence": (
                "The packet prepares adjudication only and does not assemble "
                "release or mark readiness."
            ),
        },
        {
            "criterion": "science_firewall_preserved",
            "status": "preserved",
            "evidence": REQUIRED_BOUNDARY,
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The criticizability-readiness adjudication packet is prepared; "
                "the next bounded step is packet result review only."
            ),
        },
        {
            "target": (
                "execute_v01_alpha_criticizability_readiness_adjudication_after_"
                "dependency_remediation_closeout"
            ),
            "decision": "deferred",
            "reason": (
                "Execution requires a separate packet result-review acceptance."
            ),
        },
        {
            "target": (
                "construct_or_refute_qft_gr_conserved_renormalized_stress_"
                "energy_source_witness"
            ),
            "decision": "deferred_until_result_review",
            "reason": (
                "The QFT-GR witness lane may be prepared only after the control "
                "packet result review, and may claim no scientific support from "
                "criticizability clearance."
            ),
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly is outside criticizability packet preparation.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Readiness marking requires separate adjudication and review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains scientifically separate.",
        },
    ]


def build_release_readiness_adjudication_packet(
    *,
    closeout_result_review_path: Path = DEFAULT_CLOSEOUT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(closeout_result_review_path)
    documented_tranches = _documented_dependency_nonblocking_tranches()
    preparation_criteria = _packet_preparation_criteria()
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_closeout_result_review": result_review.get("review_id")
        == EXPECTED_CLOSEOUT_RESULT_REVIEW_ID,
        "closeout_result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
        "closeout_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_CLOSEOUT_RESULT_REVIEW_OUTCOME,
        "closeout_result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_CLOSEOUT_RESULT_REVIEW_CLASSIFICATION
        and result_review.get("result_classification_count") == 1,
        "closeout_result_review_selected_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "dependency_remediation_closeout_accepted": result_review.get("accepted")
        is True
        and result_review.get("dependency_remediation_closeout_status")
        == DEPENDENCY_REMEDIATION_CLOSEOUT_ACCEPTED_STATUS
        and result_review.get("dependency_remediation_closeout_accepted") is True
        and result_review.get("dependency_remediation_queue_closed") is True,
        "all_six_dependency_tranches_documented_nonblocking": len(documented_tranches)
        == 6
        and result_review.get("all_dependency_tranches_nonblocking") is True
        and result_review.get("documented_dependency_nonblocking_tranche_count") == 6
        and result_review.get("tranche_001_status") == TRANCHE_001_STATUS
        and result_review.get("tranche_002_status") == TRANCHE_002_STATUS
        and result_review.get("tranche_003_status") == TRANCHE_003_STATUS
        and result_review.get("tranche_004_status") == REGISTERED_TRANCHE_004_STATUS
        and result_review.get("tranche_005_status") == TRANCHE_005_STATUS
        and result_review.get("tranche_006_status") == TRANCHE_006_STATUS,
        "release_readiness_preparation_authorized_but_not_marked": result_review.get(
            "release_readiness_decision_status"
        )
        == EXPECTED_RELEASE_READINESS_STATUS
        and result_review.get("release_readiness_adjudication_preparation_authorized")
        is True
        and result_review.get("release_readiness_adjudication_prepared") is False
        and result_review.get("release_readiness_eligible_for_adjudication") is True
        and result_review.get("release_readiness_proceed_authorized") is False
        and result_review.get("readiness_marking_authorized") is False
        and result_review.get("v01_alpha_marked_ready") is False,
        "no_release_assembly_or_qft_gr_seam_closure": result_review.get(
            "release_assembly_authorized"
        )
        is False
        and result_review.get("release_packet_assembled") is False
        and result_review.get("qft_gr_seam_closed") is False
        and result_review.get("qft_gr_seam_closure_authorized") is False
        and result_review.get("qft_gr_seam_closure_claimed") is False,
        "does_not_discharge_debt_or_promote_science_program": result_review.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and result_review.get("proof_debt_reduced") is False
        and result_review.get("retained_assumptions_discharged") is False
        and result_review.get("phase2_authorized") is False
        and result_review.get("empirical_validation_authorized") is False
        and result_review.get("publication_authorized") is False
        and result_review.get("master_action_promotion_authorized") is False,
        "packet_question_and_boundary_defined": bool(CRITICIZABILITY_QUESTION)
        and bool(REQUIRED_BOUNDARY)
        and len(EXECUTION_CLASSIFICATIONS) == 3,
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
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "prepared": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_"
            "REMEDIATION_CLOSEOUT_PACKET_BLOCKED"
        ),
        "consumes_dependency_remediation_closeout_result_review": (
            EXPECTED_CLOSEOUT_RESULT_REVIEW_ID
        ),
        "consumes_dependency_remediation_closeout_result_review_pointer": _ptr(
            closeout_result_review_path
        ),
        "consumed_dependency_remediation_closeout_result_review_schema_id": (
            result_review.get("schema_id")
        ),
        "consumed_dependency_remediation_closeout_result_review_outcome_id": (
            result_review.get("outcome_id")
        ),
        "consumed_dependency_remediation_closeout_result_review_classification": (
            result_review.get("result_review_classification")
        ),
        "packet_scope": (
            "PREPARE_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_AFTER_"
            "DEPENDENCY_REMEDIATION_CLOSEOUT_ONLY_NO_RELEASE_ASSEMBLY_OR_"
            "SCIENTIFIC_VALIDATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if accepted else 0,
        "criticizability_readiness_adjudication_packet_prepared": accepted,
        "release_readiness_adjudication_packet_prepared": accepted,
        "criticizability_readiness_adjudication_prepared": accepted,
        "criticizability_readiness_question": CRITICIZABILITY_QUESTION,
        "criticizability_readiness_question_prepared": accepted,
        "criticizability_readiness_question_answered": False,
        "criticizability_readiness_decision_made": False,
        "criticizability_readiness_status": CRITICIZABILITY_READINESS_PACKET_STATUS,
        "criticizability_readiness_result_review_required": accepted,
        "required_boundary": REQUIRED_BOUNDARY,
        "criticizability_readiness_firewall_defined": True,
        "dependency_remediation_closeout_accepted": accepted,
        "dependency_remediation_closeout_status": (
            DEPENDENCY_REMEDIATION_CLOSEOUT_ACCEPTED_STATUS
        ),
        "dependency_remediation_queue_closed": accepted,
        "dependency_remediation_queue_exhausted": accepted,
        "all_dependency_tranches_nonblocking": accepted,
        "documented_dependency_nonblocking_tranches": documented_tranches,
        "documented_dependency_nonblocking_tranche_count": len(documented_tranches),
        "unresolved_dependency_remediation_tranches": [],
        "unresolved_dependency_remediation_tranche_count": 0,
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": REGISTERED_TRANCHE_004_STATUS,
        "tranche_004_status_exact": REGISTERED_TRANCHE_004_STATUS,
        "tranche_004_cleared_for_release_readiness": False,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_006_status": TRANCHE_006_STATUS,
        "source_map_closure_registered": result_review.get("source_map_closure_registered"),
        "source_map_closure_achieved": result_review.get("source_map_closure_achieved"),
        "source_map_closure_external_truth_claimed": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "preparation_criteria": preparation_criteria,
        "preparation_criteria_count": len(preparation_criteria),
        "evidence_chain": list(result_review.get("evidence_chain", [])),
        "evidence_chain_count": result_review.get("evidence_chain_count"),
        "execution_classification_options": EXECUTION_CLASSIFICATIONS,
        "execution_classification_option_count": len(EXECUTION_CLASSIFICATIONS),
        "release_readiness_decision_status_before_packet": (
            EXPECTED_RELEASE_READINESS_STATUS
        ),
        "release_readiness_adjudication_preparation_authorized": True,
        "release_readiness_adjudication_prepared": accepted,
        "release_readiness_eligible_for_adjudication": False,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
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
        "semiclassical_einstein_equation_derivation_claimed": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "theorem_discharge_authorized": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promotion_authorized": False,
        "canonical_toe_claimed": False,
        "track2_may_be_prepared_after_result_review": True,
        "track2_qft_gr_witness_target": (
            "construct_or_refute_qft_gr_conserved_renormalized_stress_"
            "energy_source_witness"
        ),
        "track2_qft_gr_witness_target_deferred_until_result_review": True,
        "track2_control_clearance_only": True,
        "track2_scientific_evidence_claimed_from_track1": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_"
            "DEPENDENCY_REMEDIATION_CLOSEOUT_PACKET"
        ),
        "selected_next_target_kind": (
            "criticizability_readiness_packet_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_PACKET_"
            "RESULT_ONLY_NO_RELEASE_ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha criticizability-readiness adjudication packet "
            "prepares only the question of eligibility for bounded review after "
            "dependency-remediation closeout. It does not mark release "
            "readiness, assemble release, authorize public submission, close "
            "the QFT-GR seam, derive the semiclassical Einstein equation, "
            "discharge theorem/proof debt or retained assumptions, authorize "
            "Phase 2, authorize empirical validation, authorize publication, "
            "promote the master action, make Track 2 scientific evidence from "
            "Track 1, or claim external truth."
        ),
        "roadmap_update_required": True,
    }


def write_release_readiness_adjudication_packet(
    *,
    closeout_result_review_path: Path = DEFAULT_CLOSEOUT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_release_readiness_adjudication_packet(
        closeout_result_review_path=closeout_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha criticizability-readiness adjudication "
            "packet after dependency-remediation closeout."
        )
    )
    parser.add_argument(
        "--closeout-result-review",
        type=Path,
        default=DEFAULT_CLOSEOUT_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    closeout_result_review_path = (
        ns.closeout_result_review
        if ns.closeout_result_review.is_absolute()
        else (REPO_ROOT / ns.closeout_result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_release_readiness_adjudication_packet(
        closeout_result_review_path=closeout_result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_release_readiness_adjudication_after_dependency_"
        "remediation_closeout_packet_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['packet_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
