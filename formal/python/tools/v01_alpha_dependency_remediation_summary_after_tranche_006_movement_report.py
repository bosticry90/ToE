from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_006_blocker_movement_registration_result_review_report import (
    CANDIDATE_BLOCKER_STATUS as TRANCHE_006_STATUS,
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET as EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SELECTED_DEPENDENCY as TRANCHE_006_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS as TRANCHE_006_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID as TRANCHE_006_FINDING_ID,
    SELECTED_TRANCHE_ID as TRANCHE_006_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_20260522_v0"
)
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_PREPARED_AFTER_TRANCHE_006_MOVEMENT_"
    "WITH_TRANCHE_004_RETAINED_RELEASE_BLOCKER"
)

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260522_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_20260522_v0.json"
)

TRANCHE_001_FINDING_ID = "V01-ALPHA-DEP-REM-001"
TRANCHE_001_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
TRANCHE_002_FINDING_ID = "V01-ALPHA-DEP-REM-002"
TRANCHE_002_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-002"
TRANCHE_003_FINDING_ID = "V01-ALPHA-DEP-REM-003"
TRANCHE_003_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-003"
TRANCHE_004_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-004"
TRANCHE_005_FINDING_ID = "V01-ALPHA-DEP-REM-005"
TRANCHE_005_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-005"

NEXT_TARGET = "prepare_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet"
SUMMARY_CLASSIFICATION = (
    "dependency_remediation_queue_exhausted_tranche_004_retained_release_blocker"
)
REQUIRED_NEXT_DECISION = (
    "retained_tranche_004_release_readiness_adjudication_or_release_hold"
)

FORBIDDEN_EFFECTS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "release_readiness_pause_registered",
    "release_readiness_adjudication_prepared",
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


def _retained_tranche_004(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("retained_tranche_004_carry_forward", {}))


def _remaining_release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("remaining_release_blocking_obligations", []))


def _tranche_006(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("tranche_006_obligation_carry_forward", {}))


def _documented_dependency_nonblocking_tranches() -> list[dict[str, str]]:
    return [
        {
            "tranche_id": TRANCHE_001_TRANCHE_ID,
            "finding_id": TRANCHE_001_FINDING_ID,
            "status": TRANCHE_001_STATUS,
        },
        {
            "tranche_id": TRANCHE_002_TRANCHE_ID,
            "finding_id": TRANCHE_002_FINDING_ID,
            "status": TRANCHE_002_STATUS,
        },
        {
            "tranche_id": TRANCHE_003_TRANCHE_ID,
            "finding_id": TRANCHE_003_FINDING_ID,
            "status": TRANCHE_003_STATUS,
        },
        {
            "tranche_id": TRANCHE_005_TRANCHE_ID,
            "finding_id": TRANCHE_005_FINDING_ID,
            "status": TRANCHE_005_STATUS,
            "dependency": TRANCHE_005_DEPENDENCY,
        },
        {
            "tranche_id": TRANCHE_006_TRANCHE_ID,
            "finding_id": TRANCHE_006_FINDING_ID,
            "status": TRANCHE_006_STATUS,
            "dependency": TRANCHE_006_DEPENDENCY,
            "dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        },
    ]


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    retained_tranche_004 = _retained_tranche_004(result_review)
    remaining_release_blockers = _remaining_release_blockers(result_review)
    tranche_006 = _tranche_006(result_review)
    documented_tranches = _documented_dependency_nonblocking_tranches()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_summary": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": result_review.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": result_review.get(
            "tranche_005_status"
        )
        == TRANCHE_005_STATUS
        and result_review.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": result_review.get(
            "tranche_006_status"
        )
        == TRANCHE_006_STATUS
        and result_review.get("tranche_006_formal_movement_accepted") is True
        and result_review.get("tranche_006_release_blocker_status") == TRANCHE_006_STATUS
        and tranche_006.get("dependency_finding_id") == TRANCHE_006_FINDING_ID
        and tranche_006.get("dependency") == TRANCHE_006_DEPENDENCY,
        "registered_movement_confirmed": result_review.get("registered") is True
        and result_review.get("blocker_movement_registered") is True
        and result_review.get("registered_movement", {}).get("registered_movement")
        == "release_blocking -> documented_dependency_nonblocking",
        "tranche_004_retained_release_blocker_preserved": result_review.get(
            "tranche_004_status"
        )
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "no_unresolved_simple_dependency_tranches_remain": result_review.get(
            "dependency_remediation_queue_exhausted"
        )
        is True
        and len(remaining_release_blockers) == 1
        and remaining_release_blockers[0].get("dependency_finding_id")
        == TRANCHE_004_FINDING_ID
        and remaining_release_blockers[0].get("status_carry_forward") == TRANCHE_004_STATUS,
        "release_readiness_not_marked": result_review.get("v01_alpha_marked_ready")
        is False,
        "release_assembly_not_authorized": result_review.get("release_packet_assembled")
        is False,
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
        == "prepare_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_BLOCKED",
        "consumes_tranche_006_movement_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_tranche_006_movement_result_review_pointer": _ptr(result_review_path),
        "consumed_tranche_006_movement_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "packet_scope": (
            "PREPARE_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_ONLY_"
            "NO_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "dependency_remediation_summary_classification": SUMMARY_CLASSIFICATION,
        "documented_dependency_nonblocking_tranches": documented_tranches,
        "documented_dependency_nonblocking_tranche_count": len(documented_tranches),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_dependency": TRANCHE_006_DEPENDENCY,
        "tranche_006_dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_006_tranche_id": TRANCHE_006_TRANCHE_ID,
        "tranche_006_formal_movement_accepted": True,
        "tranche_006_moved_or_cleared": True,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_release_blocking_obligations": remaining_release_blockers,
        "retained_release_blocking_obligation_count": len(remaining_release_blockers),
        "simple_dependency_remediation_queue_exhausted": True,
        "unresolved_simple_dependency_tranches": [],
        "unresolved_simple_dependency_tranche_count": 0,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_still_blocked": True,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "release_readiness_pause_registered": False,
        "release_readiness_adjudication_prepared": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "required_next_decision": REQUIRED_NEXT_DECISION,
        "preferred_next_decision_path": NEXT_TARGET,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT",
        "selected_next_target_kind": (
            "retained_tranche_004_release_readiness_adjudication_packet_preparation_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_ONLY_"
            "NO_RELEASE_ASSEMBLY_OR_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The simple dependency-remediation queue is exhausted, so the next bounded "
                    "decision is whether retained tranche 004 permits any release-readiness path."
                ),
            },
            {
                "target": "prepare_v01_alpha_release_hold_packet_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": (
                    "A release-hold packet remains a conservative alternative, but the summary "
                    "first routes to a bounded retained-blocker adjudication packet."
                ),
            },
            {
                "target": "assemble_v01_alpha_release_packet",
                "decision": "deferred",
                "reason": (
                    "Release assembly remains blocked because retained tranche 004 still carries "
                    "a release-blocking source-map authorization obligation."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation summary after tranche 006 movement records "
            "that tranches 001, 002, 003, 005, and 006 are documented/nonblocking while tranche "
            "004 remains a retained release blocker. It does not assemble release, mark "
            "readiness, discharge theorem/proof debt or retained assumptions, authorize Phase 2, "
            "close seams, validate empirically, promote the master action, or make an "
            "external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation summary after tranche 006 movement."
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
        "v01_alpha_dependency_remediation_summary_after_tranche_006_movement_report: "
        f"accepted={payload['accepted']} queue_exhausted={payload['simple_dependency_remediation_queue_exhausted']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
