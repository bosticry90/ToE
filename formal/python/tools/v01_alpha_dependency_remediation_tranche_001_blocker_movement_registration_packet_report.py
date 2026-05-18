from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "20260515_v0"
)
PACKET_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "PREPARED_WITH_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_"
    "ACCEPTS_DOCUMENTED_NONBLOCKING_STATUS_CANDIDATE_AND_AUTHORIZES_BLOCKER_MOVEMENT_REGISTRATION_PREPARATION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_packet"
)
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-001"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
SELECTED_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
POLICY_CLASSIFICATION = "policy_acceptable_with_documentation_requirement"
DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION = (
    "documentation_accepted_pending_tranche_001_status_adjudication"
)
STATUS_CANDIDATE = "documented_dependency_nonblocking_pending_result_review"
CURRENT_BLOCKER_STATUS = "release_blocking"
CANDIDATE_BLOCKER_STATUS = "documented_dependency_nonblocking"
PROPOSED_MOVEMENT = "release_blocking_to_documented_nonblocking_dependency"
NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_packet_result"
)

FORBIDDEN_EFFECTS = [
    "blocker_movement_registration_execution_authorized",
    "blocker_movement_registered",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _accepted_evidence(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("accepted_lean_dependency_evidence", {}))


def _documentation_surface(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("documentation_surface", {}))


def _other_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _other_obligations_carried_forward(result_review: dict[str, Any]) -> bool:
    rows = _other_obligations(result_review)
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
            for row in rows
        )
    )


def _movement_proposal() -> dict[str, Any]:
    return {
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "current_status": CURRENT_BLOCKER_STATUS,
        "candidate_status": CANDIDATE_BLOCKER_STATUS,
        "accepted_status_candidate": STATUS_CANDIDATE,
        "proposed_movement": PROPOSED_MOVEMENT,
        "movement_scope": "tranche_001_only",
        "requires_result_review_before_execution": True,
        "registers_movement_now": False,
        "clears_blocker_now": False,
        "marks_release_readiness_now": False,
    }


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    evidence = _accepted_evidence(result_review)
    documentation_surface = _documentation_surface(result_review)
    other_obligations = _other_obligations(result_review)
    movement_proposal = _movement_proposal()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_status_adjudication_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "status_adjudication_result_review_accepted": result_review.get("accepted") is True,
        "status_adjudication_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "status_adjudication_result_review_selected_this_packet": result_review.get(
            "selected_next_target"
        )
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "registration_packet_preparation_authorized": result_review.get(
            "blocker_movement_registration_packet_preparation_authorized"
        )
        is True,
        "previous_review_did_not_prepare_or_register_movement": result_review.get(
            "blocker_movement_registration_packet_prepared"
        )
        is False
        and result_review.get("blocker_movement_registered") is False,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "accepted_status_candidate_exact": result_review.get("status_candidate_reviewed")
        == STATUS_CANDIDATE
        and result_review.get("documented_nonblocking_status_candidate_accepted") is True,
        "movement_proposal_is_tranche_001_only": movement_proposal["selected_remediation_finding_id"]
        == SELECTED_REMEDIATION_FINDING_ID
        and movement_proposal["selected_dependency"] == SELECTED_DEPENDENCY
        and movement_proposal["movement_scope"] == "tranche_001_only",
        "movement_proposal_preserves_current_and_candidate_status": movement_proposal[
            "current_status"
        ]
        == CURRENT_BLOCKER_STATUS
        and movement_proposal["candidate_status"] == CANDIDATE_BLOCKER_STATUS
        and movement_proposal["accepted_status_candidate"] == STATUS_CANDIDATE
        and movement_proposal["proposed_movement"] == PROPOSED_MOVEMENT,
        "movement_proposal_requires_review_before_execution": movement_proposal[
            "requires_result_review_before_execution"
        ]
        is True
        and movement_proposal["registers_movement_now"] is False
        and movement_proposal["clears_blocker_now"] is False,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used") == []
        and evidence.get("project_axiom_count") == 0,
        "policy_classification_preserved": result_review.get("policy_classification")
        == POLICY_CLASSIFICATION,
        "documentation_chain_preserved": result_review.get(
            "documentation_result_review_classification"
        )
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
        and result_review.get("documentation_accepted_only_as_documentation") is True
        and documentation_surface.get("exists") is True
        and documentation_surface.get("accepted_as_documentation") is True,
        "other_five_obligations_carried_forward": _other_obligations_carried_forward(
            result_review
        ),
        "prepares_registration_packet_only": forbidden_effect_status[
            "blocker_movement_registration_execution_authorized"
        ]
        is False
        and forbidden_effect_status["blocker_movement_registered"] is False,
        "does_not_clear_or_move_blocker": forbidden_effect_status["blocker_fully_remediated"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_theorem_or_proof_debt_discharge": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "no_retained_assumption_discharge": forbidden_effect_status[
            "retained_assumptions_discharged"
        ]
        is False,
        "no_phase2_seam_empirical_or_master_action_authorization": all(
            forbidden_effect_status[key] is False
            for key in [
                "phase2_authorized",
                "seam_closure_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "review_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_packet_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_BLOCKED",
        "consumes_status_adjudication_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_status_adjudication_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "accepted_lean_dependency_evidence": {
            "command": evidence.get("command"),
            "parsed_axioms": evidence.get("parsed_axioms"),
            "project_axioms_used": evidence.get("project_axioms_used"),
            "project_axiom_count": evidence.get("project_axiom_count"),
            "classification": evidence.get("classification"),
            "raw_output": evidence.get("raw_output"),
        },
        "policy_classification": POLICY_CLASSIFICATION,
        "documentation_result_review_classification": DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
        "documentation_surface": documentation_surface,
        "documentation_accepted_only_as_documentation": True,
        "status_candidate_reviewed": STATUS_CANDIDATE,
        "documented_nonblocking_status_candidate_accepted": True,
        "movement_proposal": movement_proposal,
        "movement_registration_inputs": [
            "accepted Lean dependency evidence [propext, Classical.choice, Quot.sound]",
            "project_axioms_used = []",
            "policy_acceptable_with_documentation_requirement",
            "documentation accepted as documentation only",
            "status candidate accepted pending blocker-movement registration",
            "other five release-blocking obligations tracked and unmodified",
        ],
        "movement_registration_acceptance_criteria": [
            "The proposed movement is only for V01-ALPHA-DEP-REM-001.",
            "The movement proposal preserves release_blocking as the current status.",
            "The movement proposal preserves documented_dependency_nonblocking as the candidate status.",
            "The exact Lean dependency evidence remains unchanged.",
            "project_axioms_used remains empty.",
            "The other five release-blocking obligations remain carried forward unchanged.",
            "No release readiness or global theorem/proof debt discharge is inferred.",
        ],
        "movement_registration_failure_criteria": [
            "The proposal touches any dependency other than master_action_stationary_implies_free_scalar_kg.",
            "The proposal treats documentation as theorem/proof debt discharge.",
            "The proposal registers blocker movement before result review.",
            "The proposal assembles the release or marks v0.1-alpha readiness.",
            "The proposal modifies any of the other five blockers.",
        ],
        "blocker_movement_registration_packet_prepared": accepted,
        "blocker_movement_registration_execution_authorized": False,
        "blocker_movement_registered": False,
        "blocker_movement_authorized": False,
        "remediation_fully_satisfied": False,
        "tranche_001_release_blocker_status": (
            "release_blocking_pending_blocker_movement_registration_packet_result_review"
        ),
        "other_release_blocking_obligations": other_obligations,
        "other_release_blocking_obligation_count": len(other_obligations),
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET",
        "selected_next_target_kind": "blocker_movement_registration_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The proposed blocker movement must be result-reviewed before any movement registration execution is authorized.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration",
                "decision": "deferred",
                "reason": "Actual blocker movement registration requires acceptance of this preparation packet.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by unregistered tranche 001 movement and five other blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 001 blocker movement registration "
            "packet prepares a proposed movement from release-blocking to documented/nonblocking "
            "dependency status for V01-ALPHA-DEP-REM-001 only. It does not register blocker "
            "movement, clear tranche 001, assemble the release packet, mark v0.1-alpha readiness, "
            "discharge Lean theorem debt, reduce axiom/spec-backed proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 001 blocker movement "
            "registration packet."
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
    payload = write_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_packet_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
