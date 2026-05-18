from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_PREPARED_AFTER_"
    "TRANCHE_001_MOVEMENT_WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_ACCEPTS_DOCUMENTED_NONBLOCKING_MOVEMENT_AND_AUTHORIZES_NEXT_"
    "REMEDIATION_TRANCHE_SELECTION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet"
)
TRANCHE_001_FINDING_ID = "V01-ALPHA-DEP-REM-001"
TRANCHE_001_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
SELECTED_NEXT_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-002"
SELECTED_NEXT_FINDING_ID = "V01-ALPHA-DEP-REM-002"
SELECTED_NEXT_DEPENDENCY = "stationary_implies_operator_zero"
SELECTED_NEXT_DEPENDENCY_CLASS = "lean_theorem_dependency"
NEXT_TARGET = "review_v01_alpha_dependency_remediation_next_tranche_selection_packet_result"

FORBIDDEN_EFFECTS = [
    "remediation_execution_authorized",
    "remediation_executed",
    "selected_tranche_execution_packet_prepared",
    "blocker_movement_registered",
    "blocker_fully_remediated",
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


def _other_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _remaining_obligations_are_unmodified(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
            for row in rows
        )
    )


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_NEXT_FINDING_ID:
            return dict(row)
    return {}


def _selection_row(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "selected_tranche_id": SELECTED_NEXT_TRANCHE_ID,
        "selected_dependency_finding_id": SELECTED_NEXT_FINDING_ID,
        "selected_dependency": SELECTED_NEXT_DEPENDENCY,
        "selected_dependency_class": SELECTED_NEXT_DEPENDENCY_CLASS,
        "source_status": row.get("status_carry_forward"),
        "selection_method": "stable_order_first_remaining_release_blocking_obligation",
        "selection_reason": (
            "After tranche 001 movement, this is the first remaining carried-forward "
            "release-blocking obligation in the remediation ledger and has a direct Lean "
            "theorem-dependency surface suitable for the next bounded preparation step."
        ),
        "execution_prepared": False,
        "execution_authorized": False,
        "remediation_executed": False,
        "requires_result_review_before_execution_packet": True,
    }


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    remaining_obligations = _other_obligations(result_review)
    selected_obligation = _selected_obligation(remaining_obligations)
    selected_row = _selection_row(selected_obligation)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_tranche_001_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "tranche_001_result_review_accepted": result_review.get("accepted") is True,
        "tranche_001_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "tranche_001_result_review_selected_this_packet": result_review.get(
            "selected_next_target"
        )
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "tranche_001_documented_nonblocking_accepted": result_review.get(
            "tranche_001_formal_movement_accepted"
        )
        is True
        and result_review.get("tranche_001_release_blocker_status") == TRANCHE_001_STATUS,
        "tranche_001_identity_preserved": result_review.get("selected_remediation_finding_id")
        == TRANCHE_001_FINDING_ID
        and result_review.get("selected_dependency") == TRANCHE_001_DEPENDENCY,
        "global_release_still_blocked": result_review.get(
            "global_release_readiness_still_blocked"
        )
        is True
        and result_review.get("release_blocking_obligation_count_after_review") == 5,
        "other_five_obligations_tracked_unmodified": _remaining_obligations_are_unmodified(
            remaining_obligations
        ),
        "selected_row_present": selected_obligation.get("dependency_finding_id")
        == SELECTED_NEXT_FINDING_ID,
        "selected_row_expected_dependency": selected_obligation.get("dependency")
        == SELECTED_NEXT_DEPENDENCY
        and selected_obligation.get("dependency_class") == SELECTED_NEXT_DEPENDENCY_CLASS,
        "selects_exactly_one_next_tranche": selected_row["selected_tranche_id"]
        == SELECTED_NEXT_TRANCHE_ID
        and selected_row["selected_dependency_finding_id"] == SELECTED_NEXT_FINDING_ID,
        "selection_preparation_only": selected_row["execution_prepared"] is False
        and selected_row["execution_authorized"] is False
        and selected_row["remediation_executed"] is False,
        "no_remediation_execution": forbidden_effect_status["remediation_executed"] is False
        and forbidden_effect_status["remediation_execution_authorized"] is False,
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
        == "review_v01_alpha_dependency_remediation_next_tranche_selection_packet_result",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_BLOCKED",
        "consumes_tranche_001_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_tranche_001_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_NEXT_REMEDIATION_TRANCHE_SELECTION_PACKET_ONLY_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_001_formal_movement_accepted": True,
        "tranche_001_dependency_policy_remediation_satisfied": True,
        "tranche_001_cleared_for_global_release_readiness": False,
        "global_release_readiness_still_blocked": True,
        "remaining_release_blocking_obligations": remaining_obligations,
        "remaining_release_blocking_obligation_count": len(remaining_obligations),
        "selected_next_remediation_tranche": selected_row,
        "selected_next_tranche_id": SELECTED_NEXT_TRANCHE_ID,
        "selected_next_dependency_finding_id": SELECTED_NEXT_FINDING_ID,
        "selected_next_dependency": SELECTED_NEXT_DEPENDENCY,
        "selected_next_dependency_class": SELECTED_NEXT_DEPENDENCY_CLASS,
        "selection_count": 1 if accepted else 0,
        "selection_policy": {
            "method": "stable_order_first_remaining_release_blocking_obligation",
            "eligible_finding_ids": [
                row.get("dependency_finding_id") for row in remaining_obligations
            ],
            "selected_finding_id": SELECTED_NEXT_FINDING_ID,
            "does_not_execute_selection": True,
            "requires_result_review_before_execution_packet": True,
        },
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "selected_tranche_execution_packet_prepared": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET",
        "selected_next_target_kind": "next_tranche_selection_packet_result_review_only",
        "next_action_scope": (
            "REVIEW_NEXT_REMEDIATION_TRANCHE_SELECTION_PACKET_RESULT_ONLY_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The next-tranche selection packet must be reviewed before tranche-specific execution preparation.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_tranche_002_execution_packet",
                "decision": "deferred",
                "reason": "Tranche 002 execution-packet preparation requires result-review acceptance of this selection packet.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by five remaining release-blocking obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation next-tranche selection packet selects only "
            "one remaining release-blocking obligation for the next bounded remediation tranche. "
            "It does not execute remediation, prepare the tranche-specific execution packet, "
            "assemble the release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, "
            "reduce axiom/spec-backed proof debt, discharge retained assumptions, authorize Phase 2, "
            "close seams, validate empirically, promote the master action, promote claims, or make "
            "an external-truth claim."
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
        description="Generate the v0.1-alpha dependency remediation next-tranche selection packet."
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
        "v01_alpha_dependency_remediation_next_tranche_selection_packet_report: "
        f"accepted={payload['accepted']} selected_next_tranche={payload['selected_next_tranche_id']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
