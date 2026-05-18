from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_ACCEPTS_REVIEW_SCOPE_ONLY_"
    "AND_AUTHORIZES_EXPERT_REVIEW_EXECUTION_PACKET_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_EXPERT_PACKET_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_EXPERT_PACKET_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
EXPECTED_EXPERT_PACKET_OUTCOME = (
    "V01_ALPHA_EXPERT_REVIEW_PACKET_PREPARED_FROM_LEAN_DEPENDENCY_AUDIT_CAPTURE_"
    "WITH_NO_REVIEW_EXECUTION_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SCOPE = "PREPARE_EXPERT_REVIEW_PACKET_ONLY_NO_REVIEW_EXECUTION_OR_RELEASE_ASSEMBLY"
EXPECTED_PACKET_GAP = "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0"
EXPECTED_PACKET_SELECTED_TARGET = "review_v01_alpha_expert_review_packet_result"
NEXT_TARGET = "prepare_v01_alpha_expert_review_execution_packet"

FORBIDDEN_EFFECTS = [
    "expert_review_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
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


def _dependency_rows_still_unexecuted(packet: dict[str, Any]) -> bool:
    rows = packet.get("dependency_review_rows", [])
    if len(rows) != 6:
        return False
    return all(
        row.get("review_execution_status") == "not_executed_v0"
        and row.get("reviewer_assessment_status") == "prepared_not_assessed"
        and row.get("proof_debt_discharge_claim") is False
        for row in rows
    )


def _retained_assumptions_remain_retained(packet: dict[str, Any]) -> bool:
    retained = packet.get("review_scope", {}).get("retained_assumptions", {})
    rows = retained.get("rows", [])
    return len(rows) == 22 and all(row.get("status") == "retained_assumption" for row in rows)


def build_result_review(
    *,
    expert_packet_path: Path = DEFAULT_EXPERT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(expert_packet_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    summary = packet.get("packet_summary", {})
    retained_scope = packet.get("review_scope", {}).get("retained_assumptions", {})
    acceptance_criteria = {
        "consumes_expert_review_packet": packet.get("packet_id") == EXPECTED_EXPERT_PACKET_ID,
        "expert_review_packet_prepared": packet.get("prepared") is True,
        "expert_review_packet_nonclaim_status": packet.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "expert_review_packet_outcome_expected": packet.get("outcome_id") == EXPECTED_EXPERT_PACKET_OUTCOME,
        "expert_review_packet_scope_only": packet.get("packet_scope") == EXPECTED_PACKET_SCOPE,
        "expert_review_packet_review_not_executed": packet.get("review_execution_status") == "not_executed_v0",
        "expert_review_packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "primary_packet_gap_preserved": summary.get("primary_packet_gap") == EXPECTED_PACKET_GAP,
        "dependency_review_rows_preserved": summary.get("dependency_review_row_count") == 6,
        "release_blocking_dependencies_preserved": summary.get("release_blocking_dependency_count") == 6,
        "documentation_only_dependencies_preserved": summary.get("documentation_only_dependency_count") == 3,
        "expert_review_required_dependencies_preserved": summary.get("expert_review_required_dependency_count")
        == 6,
        "retained_assumption_count_preserved": summary.get("retained_assumption_count") == 22,
        "proof_debt_class_count_preserved": summary.get("proof_debt_class_count") == 3,
        "dependency_rows_still_unexecuted": _dependency_rows_still_unexecuted(packet),
        "retained_assumptions_remain_retained": _retained_assumptions_remain_retained(packet),
        "reviewer_promotion_firewall_present": len(packet.get("reviewer_not_allowed_to_promote", [])) == 10,
        "no_expert_review_execution": packet.get("expert_review_executed") is False,
        "no_release_packet_assembly": packet.get("release_packet_assembled") is False,
        "no_v01_readiness_marking": packet.get("v01_alpha_marked_ready") is False,
        "no_lean_theorem_debt_discharge": packet.get("lean_theorem_debt_discharged") is False,
        "no_axiom_spec_backed_debt_reduction": packet.get("axiom_spec_backed_debt_reduced") is False,
        "packet_forbidden_effects_all_false": all(
            packet.get("forbidden_effect_status", {}).get(key) is False
            for key in packet.get("forbidden_effect_status", {})
        ),
        "review_forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "prepare_v01_alpha_expert_review_execution_packet",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID if accepted else "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_expert_review_packet": EXPECTED_EXPERT_PACKET_ID,
        "consumes_expert_review_packet_pointer": _ptr(expert_packet_path),
        "consumed_expert_review_packet_schema_id": packet.get("schema_id"),
        "source_capture_review": packet.get("consumes_result_review"),
        "source_capture_packet": packet.get("source_capture_packet"),
        "review_scope": "EXPERT_REVIEW_PACKET_RESULT_REVIEW_ONLY_NO_REVIEW_EXECUTION",
        "review_scope_only_acceptance": accepted,
        "packet_summary_reviewed": {
            "primary_packet_gap": summary.get("primary_packet_gap"),
            "dependency_review_row_count": summary.get("dependency_review_row_count"),
            "release_blocking_dependency_count": summary.get("release_blocking_dependency_count"),
            "documentation_only_dependency_count": summary.get("documentation_only_dependency_count"),
            "expert_review_required_dependency_count": summary.get("expert_review_required_dependency_count"),
            "retained_assumption_count": summary.get("retained_assumption_count"),
            "proof_debt_class_count": summary.get("proof_debt_class_count"),
        },
        "retained_assumption_posture": {
            "row_count": retained_scope.get("row_count"),
            "remain_retained": _retained_assumptions_remain_retained(packet),
            "discharged_count_by_this_review": 0,
        },
        "dependency_review_posture": {
            "row_count": len(packet.get("dependency_review_rows", [])),
            "all_rows_not_executed": _dependency_rows_still_unexecuted(packet),
            "reviewer_assessment_status": "prepared_not_assessed",
            "proof_debt_discharge_claim_count": 0,
        },
        "forbidden_effect_status": forbidden_effect_status,
        "expert_review_executed": False,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "expert_review_execution_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": "PREPARE_EXECUTION_PACKET_ONLY_NO_EXPERT_REVIEW_EXECUTION",
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The expert-review scope packet is accepted, so the next bounded object may prepare execution criteria without executing review.",
            },
            {
                "target": "execute_v01_alpha_expert_review",
                "decision": "deferred",
                "reason": "Expert review execution remains closed until a separate execution packet is prepared and reviewed.",
            },
            {
                "target": "assemble_v01_alpha_public_release_packet",
                "decision": "deferred",
                "reason": "Release assembly remains blocked while expert review and dependency adjudication are not complete.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha expert review packet result review accepts reviewer-scope preparation only. It authorizes "
            "only preparation of an expert-review execution packet and does not execute expert review, assemble the "
            "release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, reduce axiom/spec-backed proof "
            "debt, discharge retained assumptions, authorize Phase 2, close seams, validate empirically, promote the "
            "master action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    expert_packet_path: Path = DEFAULT_EXPERT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        expert_packet_path=expert_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the v0.1-alpha expert review packet result review.")
    parser.add_argument("--expert-packet", type=Path, default=DEFAULT_EXPERT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    expert_packet_path = ns.expert_packet if ns.expert_packet.is_absolute() else (REPO_ROOT / ns.expert_packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        expert_packet_path=expert_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_expert_review_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
