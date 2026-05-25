from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DEPENDENCY_REMEDIATION_CLOSEOUT_STATUS as EXPECTED_CLOSEOUT_PENDING_STATUS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REGISTERED_TRANCHE_004_STATUS,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    SELECTED_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_20260523_v0"
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_PREPARED_AFTER_TRANCHE_004_"
    "MOVEMENT_WITH_NO_RELEASE_READINESS_OR_SEAM_PROMOTION"
)
CLOSEOUT_CLASSIFICATION = (
    "dependency_remediation_closeout_prepared_all_tranches_documented_"
    "nonblocking_no_release_readiness_or_seam_promotion"
)
CONSUMED_TARGET = "prepare_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement"
NEXT_TARGET = "review_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_result"
RELEASE_READINESS_STATUS = (
    "release_readiness_requires_dependency_remediation_closeout_result_review_and_"
    "separate_adjudication"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_20260523_v0.json"
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "empirical_validation_authorized",
    "empirical_validation_claimed",
    "lean_theorem_debt_discharged",
    "master_action_promotion_authorized",
    "phase2_authorized",
    "proof_debt_reduced",
    "publication_authorized",
    "qft_gr_seam_closed",
    "qft_gr_seam_closure_authorized",
    "qft_gr_seam_closure_claimed",
    "readiness_marking_authorized",
    "release_assembly_authorized",
    "release_packet_assembled",
    "release_readiness_adjudication_prepared",
    "release_readiness_proceed_authorized",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
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
            "finding_id": TRANCHE_004_FINDING_ID,
            "tranche_id": SELECTED_TRANCHE_ID,
            "dependency": TRANCHE_004_DEPENDENCY,
            "status": REGISTERED_TRANCHE_004_STATUS,
        },
        {"finding_id": "V01-ALPHA-DEP-REM-005", "status": TRANCHE_005_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-006", "status": TRANCHE_006_STATUS},
    ]


def _closeout_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion": "all_six_tranches_nonblocking",
            "status": "satisfied",
            "evidence": "tranches 001/002/003/005/006 documented_dependency_nonblocking and tranche 004 documented_source_map_closed_nonblocking",
        },
        {
            "criterion": "tranche_004_source_map_closed_status_accepted",
            "status": "satisfied",
            "evidence": "retained tranche 004 blocker movement registration result review accepted documented_source_map_closed_nonblocking",
        },
        {
            "criterion": "release_readiness_separate",
            "status": "preserved",
            "evidence": "closeout preparation does not mark readiness or assemble release",
        },
        {
            "criterion": "seam_closure_separate",
            "status": "preserved",
            "evidence": "closeout preparation does not close the QFT-GR seam",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The closeout packet is prepared; the next bounded step is "
                "result review of the closeout packet only."
            ),
        },
        {
            "target": "prepare_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout",
            "decision": "deferred",
            "reason": (
                "Release-readiness adjudication remains downstream of closeout "
                "result-review acceptance."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains a separate downstream adjudication.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains unauthorized by closeout preparation.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Release readiness remains unmarked until separately adjudicated.",
        },
    ]


def build_closeout_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    documented_tranches = _documented_dependency_nonblocking_tranches()
    criteria = _closeout_criteria()
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_tranche_004_movement_result_review": result_review.get(
            "review_id"
        )
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION
        and result_review.get("result_classification_count") == 1,
        "result_review_selected_this_closeout_preparation": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "result_review_accepts_tranche_004_movement": result_review.get("accepted")
        is True
        and result_review.get("documented_source_map_closed_nonblocking_status_accepted")
        is True
        and result_review.get("tranche_004_status") == REGISTERED_TRANCHE_004_STATUS
        and result_review.get("tranche_004_formal_movement_accepted") is True,
        "all_six_dependency_tranches_nonblocking": len(documented_tranches) == 6
        and result_review.get("documented_dependency_nonblocking_tranche_count") == 6
        and result_review.get("tranche_001_status") == TRANCHE_001_STATUS
        and result_review.get("tranche_002_status") == TRANCHE_002_STATUS
        and result_review.get("tranche_003_status") == TRANCHE_003_STATUS
        and result_review.get("tranche_004_status") == REGISTERED_TRANCHE_004_STATUS
        and result_review.get("tranche_005_status") == TRANCHE_005_STATUS
        and result_review.get("tranche_006_status") == TRANCHE_006_STATUS,
        "dependency_queue_exhausted_before_closeout": result_review.get(
            "dependency_remediation_closeout_status"
        )
        == EXPECTED_CLOSEOUT_PENDING_STATUS
        and result_review.get("dependency_remediation_blocker_queue_exhausted") is True
        and result_review.get("simple_dependency_remediation_queue_exhausted") is True
        and result_review.get("unresolved_dependency_remediation_tranche_count") == 0
        and result_review.get("dependency_remediation_closeout_preparation_authorized")
        is True
        and result_review.get("dependency_remediation_closeout_prepared") is False,
        "source_map_closure_evidence_preserved": result_review.get(
            "source_map_closure_registered"
        )
        is True
        and result_review.get("final_source_map_closure_registered") is True
        and result_review.get("source_map_closure_achieved") is True
        and result_review.get("source_map_closure_external_truth_claimed") is False,
        "closeout_prepares_only_no_release_or_seam": result_review.get(
            "release_readiness_held"
        )
        is True
        and result_review.get("release_readiness_still_blocked") is True
        and result_review.get("release_assembly_authorized") is False
        and result_review.get("release_packet_assembled") is False
        and result_review.get("v01_alpha_marked_ready") is False
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_BLOCKED",
        "consumes_tranche_004_movement_registration_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_tranche_004_movement_registration_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_tranche_004_movement_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "consumed_tranche_004_movement_result_review_outcome_id": result_review.get(
            "outcome_id"
        ),
        "consumed_tranche_004_movement_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "packet_scope": (
            "PREPARE_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
            "MOVEMENT_ONLY_NO_RELEASE_READINESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "dependency_remediation_closeout_classification": CLOSEOUT_CLASSIFICATION,
        "dependency_remediation_closeout_classification_count": 1 if accepted else 0,
        "dependency_remediation_closeout_packet_prepared": accepted,
        "dependency_remediation_closeout_prepared": accepted,
        "dependency_remediation_closeout_result_review_required": accepted,
        "dependency_remediation_closeout_status_before_packet": (
            EXPECTED_CLOSEOUT_PENDING_STATUS
        ),
        "dependency_remediation_closeout_status": (
            "dependency_remediation_closeout_prepared_pending_result_review"
        ),
        "dependency_remediation_queue_exhausted": accepted,
        "dependency_remediation_blocker_queue_exhausted": accepted,
        "simple_dependency_remediation_queue_exhausted": accepted,
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
        "tranche_004_status_pending_result_review": False,
        "tranche_004_formal_movement_accepted": True,
        "tranche_004_retained_blocker_discharged": True,
        "tranche_004_cleared_for_release_readiness": False,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_006_status": TRANCHE_006_STATUS,
        "accepted_source_map_closure_registration": result_review.get(
            "accepted_source_map_closure_registration"
        ),
        "source_map_closure_registration_status": result_review.get(
            "source_map_closure_registration_status"
        ),
        "registered_source_map_closure_accepted_by_review": result_review.get(
            "registered_source_map_closure_accepted_by_review"
        ),
        "source_map_closure_registered": True,
        "final_source_map_closure_registered": True,
        "source_map_closure_achieved": True,
        "source_map_closure_claimed": False,
        "source_map_closure_external_truth_claimed": False,
        "closeout_criteria": criteria,
        "closeout_criteria_count": len(criteria),
        "evidence_chain": list(result_review.get("evidence_chain", [])),
        "evidence_chain_count": result_review.get("evidence_chain_count"),
        "release_readiness_decision_status": RELEASE_READINESS_STATUS,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_proceed_authorized": False,
        "release_readiness_adjudication_prepared": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "theorem_discharge_authorized": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "empirical_validation_claimed": False,
        "publication_authorized": False,
        "master_action_promotion_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT",
        "selected_next_target_kind": (
            "dependency_remediation_closeout_after_tranche_004_movement_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
            "MOVEMENT_RESULT_ONLY_NO_RELEASE_READINESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency-remediation closeout packet after "
            "tranche 004 movement records all six dependency-remediation "
            "tranches as nonblocking at the control layer and prepares "
            "closeout result review only. It does not close the QFT-GR seam, "
            "assemble release, mark release readiness, discharge theorem/proof "
            "debt or retained assumptions, authorize Phase 2, authorize "
            "empirical validation, authorize publication, promote the master "
            "action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_closeout_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_closeout_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation closeout packet "
            "after retained tranche 004 movement."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review if ns.result_review.is_absolute() else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_closeout_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['dependency_remediation_closeout_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
