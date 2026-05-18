from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_ACCEPTS_REMEDIATION_"
    "PLAN_AND_AUTHORIZES_ONE_BOUNDED_REMEDIATION_EXECUTION_PACKET_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_v0"
EXPECTED_PACKET_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_PREPARED_FOR_SIX_RELEASE_BLOCKING_"
    "FINDINGS_WITH_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SCOPE = "PREPARE_DEPENDENCY_REMEDIATION_PACKET_ONLY_NO_REMEDIATION_EXECUTION"
EXPECTED_PACKET_SELECTED_TARGET = "review_v01_alpha_dependency_remediation_packet_result"
NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_execution_packet"

FORBIDDEN_EFFECTS = [
    "dependency_remediation_executed",
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


def _rows(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("release_blocking_findings_preserved", []))


def _rows_complete(packet: dict[str, Any]) -> bool:
    rows = _rows(packet)
    return (
        len(rows) == 6
        and all(
            row.get("dependency_finding_id")
            and row.get("dependency")
            and row.get("dependency_class")
            and row.get("blocking_reason")
            and row.get("required_remediation_type")
            and isinstance(row.get("required_evidence_surface"), list)
            and len(row.get("required_evidence_surface", [])) == 3
            and row.get("lean_work_required") is True
            and row.get("documentation_sufficient") is False
            and row.get("expert_re_review_required") is True
            and row.get("release_readiness_can_be_reconsidered_after_remediation") is True
            and row.get("next_bounded_action")
            for row in rows
        )
    )


def _rows_are_planning_only(packet: dict[str, Any]) -> bool:
    return all(
        row.get("remediation_execution_status") == "not_executed_v0"
        and row.get("remediation_result_status") == "not_produced_v0"
        and row.get("proof_debt_discharge_claim") is False
        for row in _rows(packet)
    )


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    rows = _rows(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    summary = packet.get("remediation_plan_summary", {})

    acceptance_criteria = {
        "consumes_dependency_remediation_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_accepted": packet.get("accepted") is True,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_scope_planning_only": packet.get("packet_scope") == EXPECTED_PACKET_SCOPE,
        "packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "all_six_release_blocking_findings_present": len(rows) == 6
        and packet.get("release_blocking_finding_count") == 6,
        "all_rows_have_required_remediation_fields": _rows_complete(packet),
        "all_rows_remain_planning_only": _rows_are_planning_only(packet),
        "remediation_summary_matches_rows": summary.get("release_blocking_findings_targeted") == 6
        and summary.get("lean_work_required_count") == 6
        and summary.get("documentation_sufficient_count") == 0
        and summary.get("expert_re_review_required_count") == 6
        and summary.get("remediation_execution_count") == 0
        and summary.get("remediation_result_count") == 0,
        "packet_remediation_execution_not_authorized": packet.get(
            "remediation_execution_authorized"
        )
        is False,
        "packet_remediation_not_executed": packet.get("remediation_executed") is False,
        "no_remediation_execution": forbidden_effect_status["dependency_remediation_executed"]
        is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"] is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_lean_theorem_debt_discharge": forbidden_effect_status["lean_theorem_debt_discharged"]
        is False,
        "no_axiom_spec_backed_debt_reduction": forbidden_effect_status[
            "axiom_spec_backed_debt_reduced"
        ]
        is False,
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
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "prepare_v01_alpha_dependency_remediation_execution_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_packet": EXPECTED_PACKET_ID,
        "consumes_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "source_expert_review_execution_result_review": packet.get("consumes_result_review"),
        "source_expert_review_execution": packet.get("source_expert_review_execution"),
        "review_scope": "DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_ONLY_NO_REMEDIATION_EXECUTION",
        "packet_acceptance_posture": "remediation_plan_accepted_as_planning_only",
        "remediation_plan_review_summary": {
            "release_blocking_findings_present": len(rows),
            "dependency_finding_ids": [row.get("dependency_finding_id") for row in rows],
            "dependency_classes": sorted({str(row.get("dependency_class")) for row in rows}),
            "lean_work_required_count": summary.get("lean_work_required_count"),
            "documentation_sufficient_count": summary.get("documentation_sufficient_count"),
            "expert_re_review_required_count": summary.get("expert_re_review_required_count"),
            "release_readiness_reconsiderable_after_remediation_count": summary.get(
                "release_readiness_reconsiderable_after_remediation_count"
            ),
            "remediation_execution_count": summary.get("remediation_execution_count"),
            "remediation_result_count": summary.get("remediation_result_count"),
        },
        "reviewed_remediation_rows": [
            {
                "dependency_finding_id": row.get("dependency_finding_id"),
                "dependency": row.get("dependency"),
                "dependency_class": row.get("dependency_class"),
                "blocking_reason": row.get("blocking_reason"),
                "required_remediation_type": row.get("required_remediation_type"),
                "required_evidence_surface": row.get("required_evidence_surface"),
                "lean_work_required": row.get("lean_work_required"),
                "documentation_sufficient": row.get("documentation_sufficient"),
                "expert_re_review_required": row.get("expert_re_review_required"),
                "next_bounded_action": row.get("next_bounded_action"),
                "remediation_execution_status": row.get("remediation_execution_status"),
            }
            for row in rows
        ],
        "routing_decision": {
            "remediation_plan_accepted": accepted,
            "one_bounded_remediation_execution_packet_preparation_authorized": accepted,
            "remediation_execution_authorized": False,
            "release_readiness_adjudication_preparation_authorized": False,
            "reason": (
                "The packet is complete as planning-only remediation coverage for six release-blocking "
                "findings, so the next step may prepare one bounded remediation execution packet; "
                "actual remediation remains closed."
            ),
        },
        "remediation_execution_packet_preparation_authorized": accepted,
        "remediation_execution_authorized": False,
        "remediation_executed": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "bounded_remediation_execution_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_ONE_BOUNDED_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_ONLY_"
            "NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The remediation plan is complete enough to prepare one bounded execution packet, but not to execute remediation.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche",
                "decision": "deferred",
                "reason": "Actual remediation execution requires a separate execution packet and result-review authorization.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_priority_split_packet",
                "decision": "deferred",
                "reason": "The six-row plan is coherent enough for one bounded execution-packet preparation step.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Readiness adjudication remains blocked until remediation execution evidence is produced and reviewed.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation packet result review accepts the remediation "
            "plan as planning-only and authorizes only preparation of one bounded remediation "
            "execution packet. It does not execute remediation, assemble the release packet, mark "
            "v0.1-alpha readiness, discharge Lean theorem debt, reduce axiom/spec-backed proof "
            "debt, discharge retained assumptions, authorize Phase 2, close seams, validate "
            "empirically, promote the master action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha dependency remediation packet result review."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
