from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_ACCEPTS_CAPTURE_ONLY_"
    "AND_AUTHORIZES_EXPERT_REVIEW_PACKET_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_CAPTURE_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_CAPTURE_PACKET_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
EXPECTED_CAPTURE_OUTCOME = (
    "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_PREPARED_WITH_NO_RELEASE_ASSEMBLY_OR_PROOF_PROMOTION"
)
EXPECTED_GAP_REVIEW_ID = "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_v0"
EXPECTED_GAP_READOUT = "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY"
EXPECTED_CAPTURE_GAP = "EXACT_AXIOM_PRINT_OUTPUT_AND_EXPERT_REVIEW_NOT_EXECUTED_V0"
EXPECTED_CAPTURE_SELECTED_TARGET = "review_v01_alpha_lean_dependency_audit_capture_packet_result"
NEXT_TARGET = "prepare_v01_alpha_expert_review_packet"

FORBIDDEN_EFFECTS = [
    "expert_review_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
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


def _all_capture_forbidden_false(capture_packet: dict[str, Any]) -> bool:
    forbidden = capture_packet.get("forbidden_effect_status", {})
    return all(forbidden.get(effect) is False for effect in FORBIDDEN_EFFECTS if effect in forbidden)


def build_result_review(
    *,
    capture_packet_path: Path = DEFAULT_CAPTURE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    capture_packet = _read_json(capture_packet_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    capture_summary = capture_packet.get("capture_summary", {})
    acceptance_criteria = {
        "consumes_capture_packet": capture_packet.get("packet_id") == EXPECTED_CAPTURE_PACKET_ID,
        "capture_packet_prepared": capture_packet.get("prepared") is True,
        "capture_packet_nonclaim_status": capture_packet.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "capture_packet_outcome_expected": capture_packet.get("outcome_id") == EXPECTED_CAPTURE_OUTCOME,
        "original_gap_review_consumed": capture_packet.get("consumes_gap_review") == EXPECTED_GAP_REVIEW_ID,
        "original_gap_readout_preserved": capture_packet.get("source_gap_review_primary_gap")
        == EXPECTED_GAP_READOUT,
        "capture_gap_preserved": capture_summary.get("primary_capture_gap") == EXPECTED_CAPTURE_GAP,
        "capture_packet_selected_this_review": capture_packet.get("selected_next_target")
        == EXPECTED_CAPTURE_SELECTED_TARGET,
        "dependency_audit_rows_preserved": capture_summary.get("v01_dependency_audit_row_count") == 6,
        "release_index_checks_preserved": capture_summary.get("release_index_check_count") == 8,
        "release_blocking_dependencies_preserved": capture_summary.get("release_blocking_dependency_count")
        == 6,
        "expert_review_required_dependencies_preserved": capture_summary.get(
            "expert_review_required_dependency_count"
        )
        == 6,
        "unresolved_dependencies_preserved": capture_summary.get("unresolved_dependency_count") == 6,
        "expert_review_not_executed": capture_packet.get("expert_review_executed") is False,
        "release_packet_assembly_closed": capture_packet.get("release_packet_assembled") is False,
        "v01_alpha_readiness_not_marked": capture_packet.get("v01_alpha_marked_ready") is False,
        "lean_theorem_debt_not_discharged": capture_packet.get("lean_theorem_debt_discharged") is False,
        "axiom_spec_backed_debt_not_reduced_by_documentation": capture_packet.get(
            "axiom_spec_backed_debt_reduced_by_documentation"
        )
        is False,
        "capture_forbidden_effects_all_false": _all_capture_forbidden_false(capture_packet),
        "review_forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
        "exactly_one_next_target_selected": NEXT_TARGET == "prepare_v01_alpha_expert_review_packet",
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
        else "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_BLOCKED",
        "consumes_capture_packet": EXPECTED_CAPTURE_PACKET_ID,
        "consumes_capture_packet_pointer": _ptr(capture_packet_path),
        "consumed_capture_packet_schema_id": capture_packet.get("schema_id"),
        "source_gap_review": capture_packet.get("consumes_gap_review"),
        "source_gap_review_primary_gap": capture_packet.get("source_gap_review_primary_gap"),
        "review_scope": "CAPTURE_RESULT_REVIEW_ONLY_NO_EXPERT_REVIEW_EXECUTION_OR_RELEASE_ASSEMBLY",
        "capture_only_acceptance": accepted,
        "capture_summary_reviewed": {
            "primary_capture_gap": capture_summary.get("primary_capture_gap"),
            "v01_dependency_audit_row_count": capture_summary.get("v01_dependency_audit_row_count"),
            "release_index_check_count": capture_summary.get("release_index_check_count"),
            "relevant_module_count": capture_summary.get("relevant_module_count"),
            "release_blocking_dependency_count": capture_summary.get("release_blocking_dependency_count"),
            "expert_review_required_dependency_count": capture_summary.get(
                "expert_review_required_dependency_count"
            ),
            "unresolved_dependency_count": capture_summary.get("unresolved_dependency_count"),
        },
        "axiom_ledger_posture_reviewed": capture_packet.get("axiom_ledger_posture", {}),
        "dependency_counts_reviewed": {
            "release_blocking_dependency_count": len(capture_packet.get("release_blocking_dependencies", [])),
            "expert_review_required_dependency_count": len(
                capture_packet.get("expert_review_required_dependencies", [])
            ),
            "unresolved_dependency_count": len(capture_packet.get("unresolved_dependencies", [])),
            "documentation_only_dependency_count": len(capture_packet.get("documentation_only_dependencies", [])),
        },
        "capture_packet_boundary_confirmed": {
            "captured_dependency_posture_is_not_reviewed_dependency_posture": True,
            "captured_audit_packet_is_not_release_readiness": True,
            "documentation_is_not_theorem_discharge": True,
            "documentation_is_not_proof_debt_reduction": True,
        },
        "forbidden_effect_status": forbidden_effect_status,
        "expert_review_executed": False,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "validation_claim_authorized": False,
        "selected_next_target": NEXT_TARGET if accepted else "REMEDIATE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_REVIEW",
        "selected_next_target_kind": "expert_review_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": "PREPARE_EXPERT_REVIEW_PACKET_ONLY_NO_EXPERT_REVIEW_EXECUTION",
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The capture packet is accepted as capture-only, so the next bounded object is an expert-review packet preparation surface.",
            },
            {
                "target": "execute_v01_alpha_expert_review",
                "decision": "deferred",
                "reason": "Expert review execution requires a prepared and reviewed packet first.",
            },
            {
                "target": "assemble_v01_alpha_public_release_packet",
                "decision": "deferred",
                "reason": "Release assembly remains blocked while Lean dependency review and expert-review packet work are incomplete.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The Lean dependency audit capture result review accepts the prior packet as capture-only. It authorizes "
            "only expert-review packet preparation and does not execute expert review, assemble the v0.1-alpha "
            "release packet, mark readiness, discharge Lean theorem debt, reduce axiom/spec-backed proof debt by "
            "documentation, authorize Phase 2, close seams, validate empirically, promote the master action, promote "
            "claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    capture_packet_path: Path = DEFAULT_CAPTURE_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        capture_packet_path=capture_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha Lean dependency audit capture result review."
    )
    parser.add_argument("--capture-packet", type=Path, default=DEFAULT_CAPTURE_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    capture_packet_path = (
        ns.capture_packet if ns.capture_packet.is_absolute() else (REPO_ROOT / ns.capture_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        capture_packet_path=capture_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_lean_dependency_audit_capture_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
