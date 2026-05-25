from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_report import (
    DEFAULT_OUT as DEFAULT_EXECUTION_PATH,
    EXECUTION_ID as EXPECTED_EXECUTION_ID,
    OUTCOME_ID as EXPECTED_EXECUTION_OUTCOME,
    REGISTERED_TRANCHE_004_STATUS,
    REGISTRATION_CLASSIFICATION as EXPECTED_EXECUTION_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_EXECUTION_SCHEMA_ID,
    TRANCHE_004_STATUS_PENDING_REVIEW,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report import (
    ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS,
    PRIOR_TRANCHE_004_STATUS,
    PROPOSED_MOVEMENT,
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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_result_review_report import (
    SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
    "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
    "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_RESULT_"
    "REVIEW_ACCEPTS_DOCUMENTED_SOURCE_MAP_CLOSED_NONBLOCKING_STATUS_AND_"
    "AUTHORIZES_DEPENDENCY_REMEDIATION_CLOSEOUT_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "documented_source_map_closed_nonblocking_status_accepted_dependency_"
    "remediation_closeout_preparation_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_retained_tranche_004_blocker_movement_registration_"
    "after_source_map_closure_result"
)
NEXT_TARGET = (
    "prepare_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement"
)
DEPENDENCY_REMEDIATION_CLOSEOUT_STATUS = (
    "dependency_remediation_all_tranches_documented_nonblocking_pending_closeout"
)
RELEASE_READINESS_STATUS = (
    "release_readiness_requires_dependency_remediation_closeout_and_separate_"
    "adjudication"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
        "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0.json"
    )
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "dependency_remediation_closeout_prepared",
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
            "movement": PROPOSED_MOVEMENT,
        },
        {"finding_id": "V01-ALPHA-DEP-REM-005", "status": TRANCHE_005_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-006", "status": TRANCHE_006_STATUS},
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "All dependency-remediation tranches are now documented "
                "nonblocking at the control layer, so the next bounded step is "
                "closeout packet preparation only."
            ),
        },
        {
            "target": "prepare_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout",
            "decision": "deferred",
            "reason": (
                "Release-readiness adjudication remains downstream of a separate "
                "dependency-remediation closeout packet."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure requires a separate downstream adjudication.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains unauthorized by movement result review.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Release readiness remains unmarked until separately adjudicated.",
        },
    ]


def build_blocker_movement_registration_result_review_after_source_map_closure(
    *,
    execution_path: Path = DEFAULT_EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(execution_path)
    evidence_chain = list(execution.get("evidence_chain", []))
    movement_criteria = list(execution.get("movement_registration_criteria", []))
    registration_criteria = list(execution.get("registration_criteria", []))
    reviewed_closure_requirements = list(execution.get("reviewed_closure_requirements", []))
    reviewed_authorization_requirements = list(
        execution.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(execution.get("reviewed_witness_chain_components", []))
    forbidden_downstream_claims = list(execution.get("forbidden_downstream_claims", []))
    registration_steps = list(execution.get("blocker_movement_registration_steps", []))
    movement = dict(execution.get("registered_movement", {}))
    candidate_next_targets = _candidate_next_targets()
    documented_tranches = _documented_dependency_nonblocking_tranches()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_registration_execution": execution.get("execution_id")
        == EXPECTED_EXECUTION_ID,
        "execution_schema_expected": execution.get("schema_id")
        == EXPECTED_EXECUTION_SCHEMA_ID,
        "execution_outcome_expected": execution.get("outcome_id")
        == EXPECTED_EXECUTION_OUTCOME,
        "execution_selected_this_review": execution.get("selected_next_target")
        == CONSUMED_TARGET,
        "execution_classification_expected": execution.get(
            "blocker_movement_registration_result_classification"
        )
        == EXPECTED_EXECUTION_CLASSIFICATION
        and execution.get("blocker_movement_registration_result_classification_count")
        == 1,
        "execution_registered_movement_pending_result_review": execution.get("accepted")
        is True
        and execution.get("executed") is True
        and execution.get("blocker_movement_registration_executed") is True
        and execution.get("blocker_movement_registered") is True
        and execution.get("blocker_movement_registration_result_review_required")
        is True
        and execution.get("tranche_004_status") == TRANCHE_004_STATUS_PENDING_REVIEW,
        "registered_movement_exact": movement.get("previous_status")
        == PRIOR_TRANCHE_004_STATUS
        and movement.get("registered_status") == REGISTERED_TRANCHE_004_STATUS
        and movement.get("status_after_execution") == TRANCHE_004_STATUS_PENDING_REVIEW
        and movement.get("registered_movement") == PROPOSED_MOVEMENT
        and movement.get("movement_scope")
        == "retained_tranche_004_source_map_blocker_only",
        "source_map_closure_registration_evidence_preserved": execution.get(
            "accepted_source_map_closure_registration"
        )
        == ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
        and execution.get("source_map_closure_registration_status")
        == SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
        and execution.get("registered_source_map_closure_accepted_by_review") is True
        and execution.get("source_map_closure_registered") is True
        and execution.get("final_source_map_closure_registered") is True
        and execution.get("source_map_closure_external_truth_claimed") is False,
        "review_material_preserved": len(evidence_chain) == 9
        and execution.get("evidence_chain_count") == 9
        and len(movement_criteria) == 4
        and execution.get("movement_registration_criteria_count") == 4
        and len(registration_criteria) == 4
        and execution.get("registration_criteria_count") == 4
        and len(reviewed_closure_requirements) == 7
        and execution.get("reviewed_closure_requirement_count") == 7
        and execution.get("accepted_closure_requirement_count") == 7
        and len(reviewed_authorization_requirements) == 7
        and execution.get("reviewed_authorization_requirement_count") == 7
        and execution.get("accepted_authorization_requirement_count") == 7
        and len(reviewed_components) == 7
        and execution.get("reviewed_witness_chain_component_count") == 7
        and len(forbidden_downstream_claims) == 6
        and execution.get("forbidden_downstream_claim_count") == 6
        and len(registration_steps) == 5
        and execution.get("blocker_movement_registration_step_count") == 5,
        "all_dependency_tranches_documented_nonblocking_after_acceptance": len(
            documented_tranches
        )
        == 6
        and documented_tranches[3]["finding_id"] == TRANCHE_004_FINDING_ID
        and documented_tranches[3]["status"] == REGISTERED_TRANCHE_004_STATUS
        and execution.get("tranche_001_status") == TRANCHE_001_STATUS
        and execution.get("tranche_002_status") == TRANCHE_002_STATUS
        and execution.get("tranche_003_status") == TRANCHE_003_STATUS
        and execution.get("tranche_005_status") == TRANCHE_005_STATUS
        and execution.get("tranche_006_status") == TRANCHE_006_STATUS,
        "accepts_documented_source_map_closed_nonblocking_status": execution.get(
            "registered_tranche_004_status"
        )
        == REGISTERED_TRANCHE_004_STATUS
        and REGISTERED_TRANCHE_004_STATUS == "documented_source_map_closed_nonblocking",
        "does_not_close_seam_or_promote_release": execution.get("qft_gr_seam_closed")
        is False
        and execution.get("qft_gr_seam_closure_authorized") is False
        and execution.get("qft_gr_seam_closure_claimed") is False
        and execution.get("release_assembly_authorized") is False
        and execution.get("release_packet_assembled") is False
        and execution.get("v01_alpha_marked_ready") is False,
        "does_not_discharge_debt_or_promote_science_program": execution.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and execution.get("proof_debt_reduced") is False
        and execution.get("retained_assumptions_discharged") is False
        and execution.get("phase2_authorized") is False
        and execution.get("empirical_validation_authorized") is False
        and execution.get("publication_authorized") is False
        and execution.get("master_action_promotion_authorized") is False,
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
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
            "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_blocker_movement_registration_execution": EXPECTED_EXECUTION_ID,
        "consumes_blocker_movement_registration_execution_pointer": _ptr(
            execution_path
        ),
        "consumed_blocker_movement_registration_schema_id": execution.get("schema_id"),
        "consumed_blocker_movement_registration_outcome_id": execution.get(
            "outcome_id"
        ),
        "consumed_blocker_movement_registration_classification": execution.get(
            "blocker_movement_registration_result_classification"
        ),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_"
            "SOURCE_MAP_CLOSURE_RESULT_ONLY_AUTHORIZE_DEPENDENCY_REMEDIATION_"
            "CLOSEOUT_PREPARATION_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "blocker_movement_registration_result_reviewed": accepted,
        "blocker_movement_registration_result_accepted": accepted,
        "documented_source_map_closed_nonblocking_status_accepted": accepted,
        "documented_source_map_closed_nonblocking_status_rejected": False,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "prior_tranche_004_status": PRIOR_TRANCHE_004_STATUS,
        "registered_tranche_004_status": REGISTERED_TRANCHE_004_STATUS,
        "accepted_tranche_004_status": REGISTERED_TRANCHE_004_STATUS,
        "tranche_004_status": REGISTERED_TRANCHE_004_STATUS,
        "tranche_004_previous_pending_review_status": TRANCHE_004_STATUS_PENDING_REVIEW,
        "tranche_004_status_pending_result_review": False,
        "registered_movement": movement,
        "registered_movement_name": PROPOSED_MOVEMENT,
        "blocker_movement_registration_status": REGISTERED_TRANCHE_004_STATUS,
        "blocker_movement_registration_result_classification": (
            EXPECTED_EXECUTION_CLASSIFICATION
        ),
        "tranche_004_status_moved_by_execution": True,
        "tranche_004_status_moved_by_result_review": accepted,
        "tranche_004_status_moved": accepted,
        "tranche_004_formal_movement_accepted": accepted,
        "tranche_004_moved_to_documented_source_map_closed_nonblocking": accepted,
        "tranche_004_retained_blocker_discharged": accepted,
        "tranche_004_cleared_for_release_readiness": False,
        "accepted_source_map_closure_registration": (
            ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
        ),
        "source_map_closure_registration_status": (
            SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
        ),
        "registered_source_map_closure_accepted_by_review": True,
        "source_map_closure_registered": True,
        "final_source_map_closure_registered": True,
        "source_map_closure_authorized": True,
        "final_source_map_closure_authorized": True,
        "source_map_closure_achieved": True,
        "source_map_closure_claimed": False,
        "source_map_closure_external_truth_claimed": False,
        "source_map_closure_registration_external_truth_claimed": False,
        "documented_dependency_nonblocking_tranches": documented_tranches,
        "documented_dependency_nonblocking_tranche_count": len(documented_tranches),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_006_status": TRANCHE_006_STATUS,
        "dependency_remediation_closeout_status": DEPENDENCY_REMEDIATION_CLOSEOUT_STATUS,
        "dependency_remediation_blocker_queue_exhausted": accepted,
        "simple_dependency_remediation_queue_exhausted": accepted,
        "unresolved_dependency_remediation_tranches": [],
        "unresolved_dependency_remediation_tranche_count": 0,
        "dependency_remediation_closeout_preparation_authorized": accepted,
        "dependency_remediation_closeout_prepared": False,
        "release_readiness_decision_status": RELEASE_READINESS_STATUS,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_proceed_authorized": False,
        "release_readiness_adjudication_prepared": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "movement_registration_criteria": movement_criteria,
        "movement_registration_criteria_count": len(movement_criteria),
        "registration_criteria": registration_criteria,
        "registration_criteria_count": len(registration_criteria),
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
        "reviewed_closure_requirements": reviewed_closure_requirements,
        "reviewed_closure_requirement_count": len(reviewed_closure_requirements),
        "accepted_closure_requirement_count": execution.get(
            "accepted_closure_requirement_count"
        ),
        "reviewed_authorization_requirements": reviewed_authorization_requirements,
        "reviewed_authorization_requirement_count": len(
            reviewed_authorization_requirements
        ),
        "accepted_authorization_requirement_count": execution.get(
            "accepted_authorization_requirement_count"
        ),
        "reviewed_witness_chain_components": reviewed_components,
        "reviewed_witness_chain_component_count": len(reviewed_components),
        "forbidden_downstream_claims": forbidden_downstream_claims,
        "forbidden_downstream_claim_count": len(forbidden_downstream_claims),
        "blocker_movement_registration_steps": registration_steps,
        "blocker_movement_registration_step_count": len(registration_steps),
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "empirical_validation_claimed": False,
        "publication_authorized": False,
        "master_action_promotion_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_"
            "REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "dependency_remediation_closeout_preparation_after_tranche_004_"
            "movement_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
            "MOVEMENT_ONLY_NO_RELEASE_READINESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 blocker-movement registration result "
            "review accepts documented_source_map_closed_nonblocking as a "
            "repo-local dependency-remediation status for tranche 004 and "
            "authorizes only dependency-remediation closeout preparation. It "
            "does not close the QFT-GR seam, assemble release, mark release "
            "readiness, discharge theorem/proof debt or retained assumptions, "
            "authorize Phase 2, authorize empirical validation, authorize "
            "publication, promote the master action, or make an external-truth "
            "claim."
        ),
        "roadmap_update_required": True,
    }


def write_blocker_movement_registration_result_review_after_source_map_closure(
    *,
    execution_path: Path = DEFAULT_EXECUTION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_blocker_movement_registration_result_review_after_source_map_closure(
        execution_path=execution_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 blocker movement "
            "registration result review after source-map closure."
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
    payload = write_blocker_movement_registration_result_review_after_source_map_closure(
        execution_path=execution_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_blocker_movement_registration_"
        "after_source_map_closure_result_review_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
