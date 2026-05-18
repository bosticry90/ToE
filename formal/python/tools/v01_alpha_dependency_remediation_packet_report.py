from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_PREPARED_FOR_SIX_RELEASE_BLOCKING_"
    "FINDINGS_WITH_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_v0"
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_ACCEPTS_REVIEW_EVIDENCE_"
    "AND_AUTHORIZES_DEPENDENCY_REMEDIATION_PACKET_PREPARATION_ONLY"
)
EXPECTED_SELECTED_TARGET = "prepare_v01_alpha_dependency_remediation_packet"
NEXT_TARGET = "review_v01_alpha_dependency_remediation_packet_result"

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

DEPENDENCY_METADATA: dict[str, dict[str, Any]] = {
    "master_action_stationary_implies_free_scalar_kg": {
        "dependency_class": "lean_theorem_dependency",
        "release_dependency_class": "release_blocking_pending_capture",
        "release_label": "T-LEAN-COND",
        "source_file": "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean",
        "required_remediation_type": "exact_lean_dependency_and_proof_debt_adjudication",
        "required_evidence_surface": [
            "#print axioms ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg",
            "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean",
            "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md",
        ],
        "next_bounded_action": "prepare_remediation_tranche_for_master_action_stationary_implies_free_scalar_kg",
    },
    "stationary_implies_operator_zero": {
        "dependency_class": "lean_theorem_dependency",
        "release_dependency_class": "release_blocking_pending_capture",
        "release_label": "T-LEAN-COND",
        "source_file": "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean",
        "required_remediation_type": "exact_lean_dependency_and_proof_debt_adjudication",
        "required_evidence_surface": [
            "#print axioms ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero",
            "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean",
            "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md",
        ],
        "next_bounded_action": "prepare_remediation_tranche_for_stationary_implies_operator_zero",
    },
    "finite_transport_theorems_construct_residual_package_v0": {
        "dependency_class": "lean_bridge_dependency",
        "release_dependency_class": "release_blocking_pending_capture",
        "release_label": "T-LEAN-COND",
        "source_file": "formal/toe_formal/ToeFormal/Bridges/QM_STAT_TransportResidualPackage.lean",
        "required_remediation_type": "exact_lean_dependency_and_proof_debt_adjudication",
        "required_evidence_surface": [
            "#print axioms ToeFormal.Bridges.QMSTATTransportResidualPackage.finite_transport_theorems_construct_residual_package_v0",
            "formal/toe_formal/ToeFormal/Bridges/QM_STAT_TransportResidualPackage.lean",
            "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md",
        ],
        "next_bounded_action": "prepare_remediation_tranche_for_finite_transport_theorems_construct_residual_package_v0",
    },
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0": {
        "dependency_class": "blocked_bridge_authorization_dependency",
        "release_dependency_class": "release_blocking_pending_capture",
        "release_label": "B-BLOCKED",
        "source_file": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_SourceMapEligibilityLadderSummary.lean",
        "required_remediation_type": "source_map_authorization_and_dependency_adjudication",
        "required_evidence_surface": [
            "#print axioms ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary.qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0",
            "formal/toe_formal/ToeFormal/Bridges/QFT_GR_SourceMapEligibilityLadderSummary.lean",
            "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md",
        ],
        "next_bounded_action": "prepare_remediation_tranche_for_qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0",
    },
    "supplied_interface_alignment_semantics_construct_bridge_package_v0": {
        "dependency_class": "lean_bridge_dependency",
        "release_dependency_class": "release_blocking_pending_capture",
        "release_label": "T-LEAN-COND",
        "source_file": "formal/toe_formal/ToeFormal/Bridges/EM_QFT_InterfaceAlignmentSemanticBridge.lean",
        "required_remediation_type": "exact_lean_dependency_and_proof_debt_adjudication",
        "required_evidence_surface": [
            "#print axioms ToeFormal.Bridges.EMQFTInterfaceAlignmentSemanticBridge.supplied_interface_alignment_semantics_construct_bridge_package_v0",
            "formal/toe_formal/ToeFormal/Bridges/EM_QFT_InterfaceAlignmentSemanticBridge.lean",
            "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md",
        ],
        "next_bounded_action": "prepare_remediation_tranche_for_supplied_interface_alignment_semantics_construct_bridge_package_v0",
    },
    "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0": {
        "dependency_class": "lean_bridge_dependency",
        "release_dependency_class": "release_blocking_pending_capture",
        "release_label": "T-LEAN-COND",
        "source_file": "formal/toe_formal/ToeFormal/Bridges/SR_CosmologyRegimeTransport.lean",
        "required_remediation_type": "exact_lean_dependency_and_proof_debt_adjudication",
        "required_evidence_surface": [
            "#print axioms ToeFormal.Bridges.SRCosmologyRegimeTransport.supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0",
            "formal/toe_formal/ToeFormal/Bridges/SR_CosmologyRegimeTransport.lean",
            "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md",
        ],
        "next_bounded_action": "prepare_remediation_tranche_for_supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0",
    },
}


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _release_blocking_findings(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("actual_findings_summary", {}).get("release_blocking_dependencies", []))


def _build_remediation_rows(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, finding in enumerate(_release_blocking_findings(result_review), start=1):
        theorem = str(finding.get("theorem"))
        metadata = DEPENDENCY_METADATA[theorem]
        rows.append(
            {
                "dependency_finding_id": f"V01-ALPHA-DEP-REM-{index:03d}",
                "source_finding_pointer": (
                    "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_v0.actual_findings_summary."
                    f"release_blocking_dependencies[{index - 1}]"
                ),
                "dependency": theorem,
                "dependency_class": metadata["dependency_class"],
                "release_dependency_class": metadata["release_dependency_class"],
                "release_label": metadata["release_label"],
                "source_file": metadata["source_file"],
                "blocking_reason": (
                    "Accepted expert-review evidence says this dependency remains release-blocking "
                    "until exact dependency posture and proof-debt remediation are separately adjudicated."
                ),
                "required_remediation_type": metadata["required_remediation_type"],
                "required_evidence_surface": metadata["required_evidence_surface"],
                "lean_work_required": True,
                "documentation_sufficient": False,
                "expert_re_review_required": True,
                "release_readiness_can_be_reconsidered_after_remediation": True,
                "next_bounded_action": metadata["next_bounded_action"],
                "remediation_execution_status": "not_executed_v0",
                "remediation_result_status": "not_produced_v0",
                "blocks_v01_alpha_release_packet": finding.get("blocks_v01_alpha_release_packet"),
                "requires_remediation_before_release_assembly": finding.get(
                    "requires_remediation_before_release_assembly"
                ),
                "proof_debt_discharge_claim": finding.get("proof_debt_discharge_claim"),
            }
        )
    return rows


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    rows = _build_remediation_rows(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_SELECTED_TARGET,
        "result_review_authorized_remediation_preparation_only": result_review.get(
            "routing_decision", {}
        ).get("dependency_remediation_packet_preparation_authorized")
        is True,
        "release_readiness_adjudication_not_authorized_by_source_review": result_review.get(
            "routing_decision", {}
        ).get("release_readiness_adjudication_preparation_authorized")
        is False,
        "six_release_blocking_findings_preserved": len(rows) == 6,
        "all_rows_require_remediation_before_release_assembly": all(
            row["requires_remediation_before_release_assembly"] is True for row in rows
        ),
        "all_rows_prepare_remediation_only": all(
            row["remediation_execution_status"] == "not_executed_v0"
            and row["remediation_result_status"] == "not_produced_v0"
            for row in rows
        ),
        "all_rows_identify_required_fields": all(
            row["dependency_finding_id"]
            and row["dependency_class"]
            and row["blocking_reason"]
            and row["required_remediation_type"]
            and row["required_evidence_surface"]
            and isinstance(row["lean_work_required"], bool)
            and row["documentation_sufficient"] is False
            and row["expert_re_review_required"] is True
            and row["release_readiness_can_be_reconsidered_after_remediation"] is True
            and row["next_bounded_action"]
            for row in rows
        ),
        "no_remediation_execution": forbidden_effect_status["dependency_remediation_executed"] is False,
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
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "review_v01_alpha_dependency_remediation_packet_result",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "source_expert_review_execution": result_review.get("consumes_execution"),
        "source_expert_review_execution_pointer": result_review.get("consumes_execution_pointer"),
        "packet_scope": "PREPARE_DEPENDENCY_REMEDIATION_PACKET_ONLY_NO_REMEDIATION_EXECUTION",
        "remediation_plan_status": "prepared_not_executed",
        "release_blocking_finding_count": len(rows),
        "release_blocking_findings_preserved": rows,
        "remediation_plan_summary": {
            "release_blocking_findings_targeted": len(rows),
            "lean_work_required_count": sum(1 for row in rows if row["lean_work_required"]),
            "documentation_sufficient_count": sum(1 for row in rows if row["documentation_sufficient"]),
            "expert_re_review_required_count": sum(1 for row in rows if row["expert_re_review_required"]),
            "release_readiness_reconsiderable_after_remediation_count": sum(
                1 for row in rows if row["release_readiness_can_be_reconsidered_after_remediation"]
            ),
            "remediation_execution_count": 0,
            "remediation_result_count": 0,
        },
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_PREPARATION",
        "selected_next_target_kind": "result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": "REVIEW_DEPENDENCY_REMEDIATION_PACKET_RESULT_ONLY_NO_REMEDIATION_EXECUTION",
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The remediation packet must be reviewed before any bounded remediation tranche is executed.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche",
                "decision": "deferred",
                "reason": "Execution is blocked until the remediation packet result review authorizes a specific bounded tranche.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Readiness adjudication preparation remains blocked until remediation planning and any authorized remediation execution are reviewed.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation packet prepares a remediation plan for six "
            "release-blocking expert-review findings only. It does not execute remediation, assemble "
            "the release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, reduce "
            "axiom/spec-backed proof debt, discharge retained assumptions, authorize Phase 2, close "
            "seams, validate empirically, promote the master action, promote claims, or make an "
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
        description="Generate the v0.1-alpha dependency remediation packet."
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
        "v01_alpha_dependency_remediation_packet_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
