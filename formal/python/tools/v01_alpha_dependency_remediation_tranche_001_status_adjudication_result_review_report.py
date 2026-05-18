from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_"
    "ACCEPTS_DOCUMENTED_NONBLOCKING_STATUS_CANDIDATE_AND_AUTHORIZES_BLOCKER_MOVEMENT_REGISTRATION_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_ADJUDICATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_ADJUDICATION_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_v0"
EXPECTED_ADJUDICATION_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATED_PENDING_RESULT_REVIEW_"
    "WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_ADJUDICATION_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result"
)
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-001"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
SELECTED_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
POLICY_CLASSIFICATION = "policy_acceptable_with_documentation_requirement"
DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION = (
    "documentation_accepted_pending_tranche_001_status_adjudication"
)
STATUS_DECISION = "documented_dependency_nonblocking_pending_result_review"
STATUS_CLASSIFICATION = "status_adjudicated_documented_dependency_pending_result_review"
RESULT_REVIEW_CLASSIFICATION = (
    "documented_nonblocking_status_candidate_accepted_pending_blocker_movement_registration"
)
NEXT_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_packet"
)

FORBIDDEN_EFFECTS = [
    "blocker_movement_registration_packet_prepared",
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


def _accepted_evidence(adjudication: dict[str, Any]) -> dict[str, Any]:
    return dict(adjudication.get("accepted_lean_dependency_evidence", {}))


def _documentation_surface(adjudication: dict[str, Any]) -> dict[str, Any]:
    return dict(adjudication.get("documentation_surface", {}))


def _status_decision(adjudication: dict[str, Any]) -> dict[str, Any]:
    return dict(adjudication.get("status_adjudication_decision", {}))


def _other_obligations(adjudication: dict[str, Any]) -> list[dict[str, Any]]:
    return list(adjudication.get("other_release_blocking_obligations", []))


def _other_obligations_carried_forward(adjudication: dict[str, Any]) -> bool:
    rows = _other_obligations(adjudication)
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
            for row in rows
        )
    )


def build_result_review(
    *,
    adjudication_path: Path = DEFAULT_ADJUDICATION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    adjudication = _read_json(adjudication_path)
    evidence = _accepted_evidence(adjudication)
    documentation_surface = _documentation_surface(adjudication)
    decision = _status_decision(adjudication)
    other_obligations = _other_obligations(adjudication)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_adjudication": adjudication.get("execution_id")
        == EXPECTED_ADJUDICATION_ID,
        "adjudication_executed_and_accepted": adjudication.get("executed") is True
        and adjudication.get("accepted") is True,
        "adjudication_outcome_expected": adjudication.get("outcome_id")
        == EXPECTED_ADJUDICATION_OUTCOME,
        "adjudication_selected_this_review": adjudication.get("selected_next_target")
        == EXPECTED_ADJUDICATION_SELECTED_TARGET,
        "selected_tranche_expected": adjudication.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": adjudication.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": adjudication.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "status_candidate_exact": adjudication.get("tranche_001_status_candidate")
        == STATUS_DECISION
        and decision.get("decision") == STATUS_DECISION,
        "status_classification_exact": adjudication.get("status_adjudication_classification")
        == STATUS_CLASSIFICATION
        and decision.get("classification") == STATUS_CLASSIFICATION,
        "status_decision_was_bounded": decision.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID
        and decision.get("selected_dependency") == SELECTED_DEPENDENCY
        and decision.get("formal_blocker_movement_requires_result_review") is True,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used") == []
        and evidence.get("project_axiom_count") == 0,
        "policy_classification_preserved": adjudication.get("policy_classification")
        == POLICY_CLASSIFICATION,
        "documentation_chain_preserved": adjudication.get(
            "documentation_result_review_classification"
        )
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
        and adjudication.get("documentation_accepted_only_as_documentation") is True
        and documentation_surface.get("exists") is True
        and documentation_surface.get("accepted_as_documentation") is True,
        "candidate_accepted_without_direct_movement": forbidden_effect_status[
            "blocker_movement_registered"
        ]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False
        and forbidden_effect_status["blocker_fully_remediated"] is False,
        "blocker_movement_registration_preparation_only": forbidden_effect_status[
            "blocker_movement_registration_packet_prepared"
        ]
        is False,
        "other_five_obligations_carried_forward": _other_obligations_carried_forward(
            adjudication
        ),
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
        == "prepare_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_BLOCKED",
        "consumes_adjudication": EXPECTED_ADJUDICATION_ID,
        "consumes_adjudication_pointer": _ptr(adjudication_path),
        "consumed_adjudication_schema_id": adjudication.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_001_STATUS_ADJUDICATION_RESULT_ONLY_AUTHORIZE_BLOCKER_MOVEMENT_REGISTRATION_PACKET_PREPARATION_NO_DIRECT_MOVEMENT"
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
        "status_candidate_reviewed": STATUS_DECISION,
        "status_adjudication_classification": STATUS_CLASSIFICATION,
        "status_adjudication_result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "documented_nonblocking_status_candidate_accepted": accepted,
        "blocker_movement_registration_packet_preparation_authorized": accepted,
        "blocker_movement_registration_packet_prepared": False,
        "blocker_movement_registered": False,
        "tranche_001_release_blocker_status": (
            "status_candidate_accepted_pending_blocker_movement_registration_packet"
        ),
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW",
        "selected_next_target_kind": "blocker_movement_registration_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_ONLY_NO_DIRECT_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The documented nonblocking status candidate is accepted, so prepare a registration packet before any formal blocker movement.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002",
                "decision": "deferred",
                "reason": "The next remediation tranche remains deferred until tranche 001 blocker movement registration is prepared and reviewed.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by unregistered tranche 001 movement and five other blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 001 status adjudication result review "
            "accepts the documented nonblocking status candidate and authorizes only blocker "
            "movement registration packet preparation. It does not itself register blocker movement, "
            "clear tranche 001, assemble the release packet, mark v0.1-alpha readiness, discharge "
            "Lean theorem debt, reduce axiom/spec-backed proof debt, discharge retained assumptions, "
            "authorize Phase 2, close seams, validate empirically, promote the master action, "
            "promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    adjudication_path: Path = DEFAULT_ADJUDICATION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        adjudication_path=adjudication_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 001 status adjudication "
            "result review."
        )
    )
    parser.add_argument("--adjudication", type=Path, default=DEFAULT_ADJUDICATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    adjudication_path = (
        ns.adjudication if ns.adjudication.is_absolute() else (REPO_ROOT / ns.adjudication)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        adjudication_path=adjudication_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
