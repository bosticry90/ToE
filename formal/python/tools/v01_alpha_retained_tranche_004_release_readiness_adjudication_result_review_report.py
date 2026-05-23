from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_ADJUDICATION_PATH,
    EXECUTION_ID as EXPECTED_ADJUDICATION_ID,
    FORBIDDEN_EFFECTS as ADJUDICATION_FORBIDDEN_EFFECTS,
    NEXT_TARGET as EXPECTED_ADJUDICATION_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_ADJUDICATION_OUTCOME,
    RELEASE_HOLD_PACKET_TARGET as NEXT_TARGET,
    RELEASE_READINESS_DECISION,
    SCHEMA_ID as EXPECTED_ADJUDICATION_SCHEMA_ID,
    SELECTED_TRANCHE_ID,
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
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_DEPENDENCY_CLASS,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_"
    "20260522_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_"
    "ACCEPTS_RELEASE_HOLD_AND_AUTHORIZES_RELEASE_HOLD_PACKET_PREPARATION_ONLY"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_20260522_v0.json"
)

POLICY_EXCEPTION_PACKET_TARGET = (
    "prepare_v01_alpha_retained_blocker_release_policy_exception_packet"
)
ASSEMBLE_RELEASE_PACKET_TARGET = "assemble_v01_alpha_release_packet"

FORBIDDEN_EFFECTS = sorted(
    set(ADJUDICATION_FORBIDDEN_EFFECTS)
    | {
        "release_hold_packet_prepared_by_review",
        "release_hold_registered_by_review",
        "release_readiness_marked_ready_by_review",
        "release_assembly_authorized_by_review",
        "policy_exception_packet_authorized",
    }
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _retained_tranche_004(adjudication: dict[str, Any]) -> dict[str, Any]:
    return dict(adjudication.get("retained_tranche_004_carry_forward", {}))


def _documented_rows(adjudication: dict[str, Any]) -> list[dict[str, Any]]:
    return list(adjudication.get("documented_dependency_nonblocking_tranches", []))


def build_result_review(
    *,
    adjudication_path: Path = DEFAULT_ADJUDICATION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    adjudication = _read_json(adjudication_path)
    retained_tranche_004 = _retained_tranche_004(adjudication)
    documented_rows = _documented_rows(adjudication)
    adjudication_forbidden = dict(adjudication.get("forbidden_effect_status", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_adjudication": adjudication.get("execution_id")
        == EXPECTED_ADJUDICATION_ID,
        "adjudication_schema_expected": adjudication.get("schema_id")
        == EXPECTED_ADJUDICATION_SCHEMA_ID,
        "adjudication_executed_and_accepted": adjudication.get("executed") is True
        and adjudication.get("accepted") is True,
        "adjudication_outcome_expected": adjudication.get("outcome_id")
        == EXPECTED_ADJUDICATION_OUTCOME,
        "adjudication_selected_this_review": adjudication.get("selected_next_target")
        == EXPECTED_ADJUDICATION_SELECTED_TARGET,
        "release_readiness_decision_expected": adjudication.get(
            "release_readiness_decision_status"
        )
        == RELEASE_READINESS_DECISION
        and adjudication.get("release_readiness_held") is True
        and adjudication.get("release_readiness_question_answered") is True
        and adjudication.get("release_readiness_decision_made") is True,
        "tranche_001_documented_nonblocking_preserved": adjudication.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": adjudication.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": adjudication.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": adjudication.get(
            "tranche_005_status"
        )
        == TRANCHE_005_STATUS
        and adjudication.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": adjudication.get(
            "tranche_006_status"
        )
        == TRANCHE_006_STATUS
        and adjudication.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and adjudication.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and adjudication.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID,
        "documented_dependency_queue_count_expected": adjudication.get(
            "documented_dependency_nonblocking_tranche_count"
        )
        == 5
        and [row.get("finding_id") for row in documented_rows]
        == [
            "V01-ALPHA-DEP-REM-001",
            "V01-ALPHA-DEP-REM-002",
            "V01-ALPHA-DEP-REM-003",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ],
        "tranche_004_retained_blocker_preserved": adjudication.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "simple_dependency_remediation_queue_exhausted": adjudication.get(
            "simple_dependency_remediation_queue_exhausted"
        )
        is True,
        "release_readiness_not_marked": adjudication.get("v01_alpha_marked_ready")
        is False
        and adjudication.get("readiness_marking_authorized") is False,
        "release_packet_not_assembled": adjudication.get("release_packet_assembled")
        is False
        and adjudication.get("release_assembly_authorized") is False,
        "no_theorem_or_proof_debt_discharge": adjudication.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and adjudication.get("proof_debt_reduced") is False
        and adjudication.get("axiom_spec_backed_debt_reduced") is False,
        "no_source_map_or_qft_gr_seam_closure": adjudication.get(
            "source_map_closure_claimed"
        )
        is False
        and adjudication.get("qft_gr_seam_closure_claimed") is False,
        "no_phase2_empirical_or_master_action_promotion": all(
            adjudication.get(key, adjudication_forbidden.get(key)) is False
            for key in [
                "phase2_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "review_does_not_prepare_release_hold_packet": forbidden_effect_status[
            "release_hold_packet_prepared"
        ]
        is False
        and forbidden_effect_status["release_hold_packet_prepared_by_review"] is False,
        "review_authorizes_release_hold_packet_preparation_only": NEXT_TARGET
        == "prepare_v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker",
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": True,
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_BLOCKED",
        "consumes_adjudication": EXPECTED_ADJUDICATION_ID,
        "consumes_adjudication_pointer": _ptr(adjudication_path),
        "consumed_adjudication_schema_id": adjudication.get("schema_id"),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_ONLY_"
            "ACCEPT_RELEASE_HOLD_AUTHORIZE_HOLD_PACKET_PREPARATION_NO_RELEASE_PROMOTION"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_dependency": TRANCHE_006_DEPENDENCY,
        "tranche_006_dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_006_dependency_finding_id": TRANCHE_006_FINDING_ID,
        "documented_dependency_nonblocking_tranches": documented_rows,
        "documented_dependency_nonblocking_tranche_count": len(documented_rows),
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_release_blocking_obligations": adjudication.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": adjudication.get(
            "retained_release_blocking_obligation_count"
        ),
        "simple_dependency_remediation_queue_exhausted": True,
        "release_readiness_decision_reviewed": True,
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_hold_accepted": accepted,
        "release_readiness_held": True,
        "release_readiness_hold_reason": "retained_tranche_004_source_map_blocker",
        "release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_proceed_authorized": False,
        "release_hold_packet_preparation_authorized": accepted,
        "release_hold_packet_prepared": False,
        "release_hold_registered": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_downgraded": False,
        "tranche_004_retained_blocker_discharged": False,
        "source_map_closure_claimed": False,
        "qft_gr_seam_closure_claimed": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW",
        "selected_next_target_kind": "release_hold_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_ONLY_"
            "NO_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The adjudication result review accepts the held-readiness decision, so "
                    "the next bounded step prepares a release-hold packet."
                ),
            },
            {
                "target": POLICY_EXCEPTION_PACKET_TARGET,
                "decision": "not_authorized",
                "reason": (
                    "A retained-blocker policy exception is not authorized by this result review."
                ),
            },
            {
                "target": ASSEMBLE_RELEASE_PACKET_TARGET,
                "decision": "not_authorized",
                "reason": (
                    "Release assembly remains blocked because tranche 004 remains retained."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 release-readiness adjudication result review accepts "
            "only the release hold caused by the retained source-map blocker and authorizes "
            "only release-hold packet preparation. It does not prepare the hold packet, "
            "assemble release, mark readiness, downgrade tranche 004, discharge theorem/proof "
            "debt or retained assumptions, claim source-map or QFT-GR seam closure, authorize "
            "Phase 2, validate empirically, promote the master action, or make an external-truth "
            "claim."
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
            "Generate the v0.1-alpha retained tranche 004 release-readiness adjudication "
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
        "v01_alpha_retained_tranche_004_release_readiness_adjudication_result_review_report: "
        f"accepted={payload['accepted']} decision={payload['release_readiness_decision_status']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
