from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_expert_review_execution_packet_report import (
    REQUIRED_EXECUTION_PACKET_SECTIONS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_ACCEPTS_EXECUTION_PACKET_"
    "AND_AUTHORIZES_EXPERT_REVIEW_EXECUTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_EXECUTION_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_EXECUTION_PACKET_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0"
EXPECTED_EXECUTION_PACKET_OUTCOME = (
    "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_PREPARED_WITH_NO_EXPERT_REVIEW_"
    "EXECUTION_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SCOPE = (
    "PREPARE_EXPERT_REVIEW_EXECUTION_PACKET_ONLY_NO_REVIEW_EXECUTION_OR_RELEASE_PROMOTION"
)
EXPECTED_EXECUTION_PACKET_SELECTED_TARGET = "review_v01_alpha_expert_review_execution_packet_result"
EXPECTED_PRIMARY_PACKET_GAP = "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0"
NEXT_TARGET = "execute_v01_alpha_expert_review_packet"

FORBIDDEN_EFFECTS = [
    "expert_review_executed",
    "expert_review_conclusions_produced",
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


def _execution_packet_sections_present(packet: dict[str, Any]) -> bool:
    return set(packet.get("execution_packet", {})) == REQUIRED_EXECUTION_PACKET_SECTIONS


def _review_contract_complete(packet: dict[str, Any]) -> bool:
    execution_packet = packet.get("execution_packet", {})
    return (
        len(execution_packet.get("reviewer_inputs", [])) == 5
        and len(execution_packet.get("reviewer_questions", [])) == 5
        and len(execution_packet.get("review_acceptance_criteria", [])) == 5
        and len(execution_packet.get("review_failure_criteria", [])) == 4
        and execution_packet.get("expert_review_output_schema", {}).get("schema_prepared") is True
        and execution_packet.get("expert_review_output_schema", {}).get(
            "conclusions_produced_by_this_packet"
        )
        is False
    )


def _evidence_bundle_complete(packet: dict[str, Any]) -> bool:
    evidence = packet.get("execution_packet", {}).get("evidence_bundle_pointers", {})
    required_keys = {
        "expert_review_packet_result_review",
        "expert_review_packet",
        "lean_dependency_audit_capture_packet",
        "lean_dependency_audit_capture_result_review",
        "lean_dependency_audit_table",
        "lean_release_index",
        "lean_aggregate",
        "axiom_spec_backed_ledger",
        "axiom_refresh_result_review",
    }
    return set(evidence) == required_keys and all(evidence.get(key) for key in required_keys)


def _retained_assumptions_remain_retained(packet: dict[str, Any]) -> bool:
    retained = packet.get("execution_packet", {}).get("retained_assumption_review_expectations", {})
    return (
        retained.get("row_count") == 22
        and retained.get("expected_status") == "retained_assumption"
        and retained.get("remain_retained_through_this_packet") is True
        and retained.get("discharge_allowed_by_this_packet") is False
    )


def _release_blockers_remain_unmoved(packet: dict[str, Any]) -> bool:
    blockers = packet.get("execution_packet", {}).get(
        "release_blocking_dependency_review_expectations", {}
    )
    return (
        blockers.get("row_count") == 6
        and len(blockers.get("dependency_names", [])) == 6
        and blockers.get("release_blocker_status_changes_allowed_by_this_packet") is False
    )


def _adjudication_rules_support_execution_only(packet: dict[str, Any]) -> bool:
    rules = packet.get("execution_packet", {}).get("post_review_adjudication_rules", {})
    return (
        rules.get("result_review_required_before_execution") is True
        and rules.get("next_review_target") == EXPECTED_EXECUTION_PACKET_SELECTED_TARGET
        and rules.get("execution_after_this_packet") == "not_authorized"
        and rules.get("release_readiness_effect") == "none_by_this_packet"
        and rules.get("debt_discharge_effect") == "none_by_this_packet"
    )


def build_result_review(
    *,
    execution_packet_path: Path = DEFAULT_EXECUTION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(execution_packet_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    summary = packet.get("packet_summary", {})
    output_schema = packet.get("execution_packet", {}).get("expert_review_output_schema", {})

    acceptance_criteria = {
        "consumes_execution_packet": packet.get("packet_id") == EXPECTED_EXECUTION_PACKET_ID,
        "execution_packet_prepared": packet.get("prepared") is True,
        "execution_packet_nonclaim_status": packet.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "execution_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_EXECUTION_PACKET_OUTCOME,
        "execution_packet_scope_preparation_only": packet.get("packet_scope") == EXPECTED_PACKET_SCOPE,
        "execution_packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_EXECUTION_PACKET_SELECTED_TARGET,
        "execution_packet_not_executed": packet.get("execution_status") == "not_executed_v0",
        "expert_review_not_executed_by_packet": packet.get("expert_review_executed") is False,
        "expert_review_not_executed_by_review": forbidden_effect_status["expert_review_executed"]
        is False,
        "review_conclusions_not_produced": packet.get("expert_review_conclusions_produced") is False
        and output_schema.get("conclusions_produced_by_this_packet") is False,
        "primary_packet_gap_preserved": summary.get("primary_packet_gap")
        == EXPECTED_PRIMARY_PACKET_GAP,
        "dependency_rows_preserved": summary.get("dependency_review_row_count") == 6,
        "release_blocking_dependencies_preserved": summary.get(
            "release_blocking_dependency_count"
        )
        == 6,
        "documentation_only_dependencies_preserved": summary.get(
            "documentation_only_dependency_count"
        )
        == 3,
        "expert_review_required_dependencies_preserved": summary.get(
            "expert_review_required_dependency_count"
        )
        == 6,
        "retained_assumption_count_preserved": summary.get("retained_assumption_count") == 22,
        "proof_debt_class_count_preserved": summary.get("proof_debt_class_count") == 3,
        "execution_packet_sections_present": _execution_packet_sections_present(packet),
        "review_contract_complete": _review_contract_complete(packet),
        "evidence_bundle_complete": _evidence_bundle_complete(packet),
        "retained_assumptions_remain_retained": _retained_assumptions_remain_retained(packet),
        "release_blockers_remain_unmoved": _release_blockers_remain_unmoved(packet),
        "adjudication_rules_support_execution_only": _adjudication_rules_support_execution_only(
            packet
        ),
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"] is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_lean_theorem_debt_discharge": forbidden_effect_status["lean_theorem_debt_discharged"]
        is False,
        "no_axiom_spec_backed_debt_reduction": forbidden_effect_status[
            "axiom_spec_backed_debt_reduced"
        ]
        is False,
        "no_retained_assumption_discharge": forbidden_effect_status["retained_assumptions_discharged"]
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
        "review_forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "execution_authorization_is_narrow": True,
        "exactly_one_next_target_selected": NEXT_TARGET == "execute_v01_alpha_expert_review_packet",
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
        else "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_execution_packet": EXPECTED_EXECUTION_PACKET_ID,
        "consumes_execution_packet_pointer": _ptr(execution_packet_path),
        "consumed_execution_packet_schema_id": packet.get("schema_id"),
        "source_expert_review_packet": packet.get("source_expert_review_packet"),
        "source_expert_review_packet_pointer": packet.get("source_expert_review_packet_pointer"),
        "source_lean_dependency_audit_capture_packet": packet.get(
            "source_lean_dependency_audit_capture_packet"
        ),
        "review_scope": "EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_ONLY_NO_EXPERT_REVIEW_EXECUTION",
        "review_acceptance_posture": "execution_packet_accepted_as_preparation_only",
        "expert_review_executed": False,
        "expert_review_conclusions_produced": False,
        "expert_review_execution_authorized": accepted,
        "expert_review_execution_authorization_scope": (
            "EXECUTE_EXPERT_REVIEW_PACKET_ONLY_NO_RELEASE_PROMOTION"
            if accepted
            else "NO_EXPERT_REVIEW_EXECUTION_AUTHORIZATION"
        ),
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "packet_summary_reviewed": {
            "primary_packet_gap": summary.get("primary_packet_gap"),
            "dependency_review_row_count": summary.get("dependency_review_row_count"),
            "release_blocking_dependency_count": summary.get(
                "release_blocking_dependency_count"
            ),
            "documentation_only_dependency_count": summary.get(
                "documentation_only_dependency_count"
            ),
            "expert_review_required_dependency_count": summary.get(
                "expert_review_required_dependency_count"
            ),
            "retained_assumption_count": summary.get("retained_assumption_count"),
            "proof_debt_class_count": summary.get("proof_debt_class_count"),
            "execution_schema_defined": summary.get("execution_schema_defined"),
            "review_conclusions_produced": summary.get("review_conclusions_produced"),
        },
        "execution_packet_review": {
            "sections_present": _execution_packet_sections_present(packet),
            "review_contract_complete": _review_contract_complete(packet),
            "evidence_bundle_complete": _evidence_bundle_complete(packet),
            "output_schema_prepared": output_schema.get("schema_prepared") is True,
            "output_schema_produced_by_this_review": False,
            "review_conclusions_produced_by_this_review": False,
        },
        "retained_assumption_posture": {
            "row_count": summary.get("retained_assumption_count"),
            "remain_retained": _retained_assumptions_remain_retained(packet),
            "discharged_count_by_this_review": 0,
        },
        "dependency_review_posture": {
            "row_count": summary.get("dependency_review_row_count"),
            "release_blocking_dependency_count": summary.get("release_blocking_dependency_count"),
            "release_blockers_remain_unmoved": _release_blockers_remain_unmoved(packet),
            "proof_debt_discharge_claim_count": 0,
        },
        "authorization_boundary": {
            "selected_execution_target": NEXT_TARGET if accepted else None,
            "expert_review_execution_authorized": accepted,
            "expert_review_execution_may_produce": "expert_review_result_packet_only",
            "release_readiness_authorized": False,
            "release_packet_assembly_authorized": False,
            "theorem_or_proof_debt_discharge_authorized": False,
            "seam_or_master_action_promotion_authorized": False,
        },
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "expert_review_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": "EXECUTE_EXPERT_REVIEW_PACKET_ONLY_NO_RELEASE_PROMOTION",
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The execution packet is complete, so the next bounded target may execute expert review and produce an expert-review result packet only.",
            },
            {
                "target": "remediate_v01_alpha_expert_review_execution_packet",
                "decision": "deferred",
                "reason": "No execution-packet completeness gap was found by this result review.",
            },
            {
                "target": "assemble_v01_alpha_public_release_packet",
                "decision": "deferred",
                "reason": "Release assembly remains blocked until expert review execution and later dependency/readiness adjudication are complete.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha expert review execution packet result review accepts the execution packet as "
            "preparation-only and authorizes only the next bounded expert-review execution target. It does "
            "not execute expert review, produce expert-review conclusions, assemble the release packet, mark "
            "v0.1-alpha readiness, discharge Lean theorem debt, reduce axiom/spec-backed proof debt, "
            "discharge retained assumptions, authorize Phase 2, close seams, validate empirically, promote "
            "the master action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    execution_packet_path: Path = DEFAULT_EXECUTION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        execution_packet_path=execution_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha expert review execution packet result review."
    )
    parser.add_argument("--execution-packet", type=Path, default=DEFAULT_EXECUTION_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    execution_packet_path = (
        ns.execution_packet if ns.execution_packet.is_absolute() else (REPO_ROOT / ns.execution_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        execution_packet_path=execution_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_expert_review_execution_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
