from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_ACCEPTS_ONE_"
    "BOUNDED_TRANCHE_AND_AUTHORIZES_REMEDIATION_EXECUTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_v0"
EXPECTED_PACKET_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_PREPARED_FOR_ONE_BOUNDED_"
    "REMEDIATION_TRANCHE_WITH_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SCOPE = (
    "PREPARE_ONE_BOUNDED_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_ONLY_"
    "NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_execution_packet_result"
)
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-001"
SELECTED_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
NEXT_TARGET = "execute_v01_alpha_dependency_remediation_tranche_001"

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


def _tracked_rows(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("tracked_release_blocking_findings", []))


def _selected_rows(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("selected_remediation_findings", []))


def _tranche(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("prepared_execution_tranche", {}))


def _selected_tranche_valid(packet: dict[str, Any]) -> bool:
    selected_rows = _selected_rows(packet)
    tranche = _tranche(packet)
    return (
        packet.get("bounded_remediation_tranche_count") == 1
        and packet.get("selected_remediation_finding_count") == 1
        and len(selected_rows) == 1
        and selected_rows[0].get("dependency_finding_id") == SELECTED_REMEDIATION_FINDING_ID
        and selected_rows[0].get("dependency") == SELECTED_DEPENDENCY
        and tranche.get("execution_tranche_id") == SELECTED_TRANCHE_ID
        and tranche.get("selected_remediation_finding_ids") == [SELECTED_REMEDIATION_FINDING_ID]
        and tranche.get("selected_dependencies") == [SELECTED_DEPENDENCY]
        and len(tranche.get("required_evidence_surfaces", [])) == 3
        and tranche.get("lean_work_required") is True
        and tranche.get("documentation_work_required") is True
        and tranche.get("documentation_sufficient_for_remediation") is False
        and bool(tranche.get("expert_re_review_trigger"))
        and len(tranche.get("success_criteria", [])) >= 5
        and len(tranche.get("failure_criteria", [])) >= 5
    )


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    tracked_rows = _tracked_rows(packet)
    selected_rows = _selected_rows(packet)
    tranche = _tranche(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_dependency_remediation_execution_packet": packet.get("packet_id")
        == EXPECTED_PACKET_ID,
        "packet_accepted": packet.get("accepted") is True,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_scope_preparation_only": packet.get("packet_scope") == EXPECTED_PACKET_SCOPE,
        "packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "all_six_release_blocking_obligations_remain_tracked": len(tracked_rows) == 6
        and packet.get("tracked_release_blocking_finding_count") == 6,
        "exactly_one_remediation_tranche_selected": _selected_tranche_valid(packet),
        "selected_tranche_id_expected": tranche.get("execution_tranche_id") == SELECTED_TRANCHE_ID,
        "selected_remediation_finding_expected": selected_rows
        and selected_rows[0].get("dependency_finding_id") == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": selected_rows
        and selected_rows[0].get("dependency") == SELECTED_DEPENDENCY,
        "packet_remediation_execution_not_occurred": packet.get("remediation_executed") is False,
        "packet_did_not_authorize_execution_yet": packet.get("remediation_execution_authorized")
        is False,
        "no_remediation_execution_in_result_review": forbidden_effect_status[
            "dependency_remediation_executed"
        ]
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
        == "execute_v01_alpha_dependency_remediation_tranche_001",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_packet": EXPECTED_PACKET_ID,
        "consumes_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "source_dependency_remediation_packet_result_review": packet.get("consumes_result_review"),
        "source_dependency_remediation_packet": packet.get("source_dependency_remediation_packet"),
        "source_expert_review_execution": packet.get("source_expert_review_execution"),
        "review_scope": (
            "DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_ONLY_"
            "AUTHORIZES_TRANCHE_EXECUTION_NO_RELEASE_PROMOTION"
        ),
        "packet_acceptance_posture": "one_bounded_tranche_accepted_for_execution_authorization_only",
        "tracked_release_blocking_finding_count": len(tracked_rows),
        "tracked_release_blocking_findings": tracked_rows,
        "selected_tranche_review": {
            "execution_tranche_id": tranche.get("execution_tranche_id"),
            "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
            "selected_dependency": SELECTED_DEPENDENCY,
            "required_evidence_surfaces": tranche.get("required_evidence_surfaces"),
            "lean_work_required": tranche.get("lean_work_required"),
            "documentation_work_required": tranche.get("documentation_work_required"),
            "documentation_sufficient_for_remediation": tranche.get(
                "documentation_sufficient_for_remediation"
            ),
            "expert_re_review_trigger": tranche.get("expert_re_review_trigger"),
            "success_criteria_count": len(tranche.get("success_criteria", [])),
            "failure_criteria_count": len(tranche.get("failure_criteria", [])),
            "post_execution_adjudication_target": tranche.get(
                "post_execution_adjudication_target"
            ),
        },
        "routing_decision": {
            "execution_packet_accepted": accepted,
            "bounded_remediation_execution_authorized": accepted,
            "authorized_tranche_id": SELECTED_TRANCHE_ID if accepted else None,
            "authorized_next_target": NEXT_TARGET if accepted else None,
            "release_readiness_adjudication_preparation_authorized": False,
            "reason": (
                "The prepared execution packet cleanly isolates one selected remediation tranche "
                "while all six obligations remain tracked; the next action may execute only tranche 001."
            ),
        },
        "bounded_remediation_execution_authorized": accepted,
        "remediation_execution_authorized": accepted,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "bounded_remediation_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_DEPENDENCY_REMEDIATION_TRANCHE_001_ONLY_NO_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "Only the selected tranche 001 may execute; all release and debt-promotion effects remain closed.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_execution_packet",
                "decision": "deferred",
                "reason": "The tranche-specific execution target is clearer and narrower than executing the whole packet label.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Readiness adjudication remains blocked until remediation execution evidence is produced and reviewed.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation execution packet result review accepts one "
            "bounded tranche and authorizes only tranche execution as the next action. It does not "
            "execute remediation during this review, assemble the release packet, mark v0.1-alpha "
            "readiness, discharge Lean theorem debt, reduce axiom/spec-backed proof debt, discharge "
            "retained assumptions, authorize Phase 2, close seams, validate empirically, promote the "
            "master action, promote claims, or make an external-truth claim."
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
        description="Generate the v0.1-alpha dependency remediation execution packet result review."
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
        "v01_alpha_dependency_remediation_execution_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
