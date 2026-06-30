from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_theorem_linkage_obligation_packet_report import (
    BOUNDARY_ITEMS as PACKET_BOUNDARY_ITEMS,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
    C_SOURCE_PHI_TARGET_STATEMENT,
    DEFAULT_OUT as PACKET_PATH,
    FIELD_EULER_LAGRANGE_EQUATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW as FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW as LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_SCHEMATIC_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_ID as PREPARED_PACKET_ID,
    PACKET_SCOPE_RECORD,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID as PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW as SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STANDALONE_PHI_SOURCE_ROUTE,
    STRESS_DIVERGENCE_TARGET,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    STRICT_PACKET_RESULT,
    WATCH_ITEMS as PACKET_WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "C_SOURCE_PHI_ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_PHI_SOURCE_ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_theorem_linkage_obligation_packet_result_review_accepts_"
    "standalone_phi_source_scope_no_proof_execution"
)

NEXT_TARGET = "prepare_phi_source_theorem_linkage_attempt_from_standalone_phi_route"
NEXT_TARGET_KIND = (
    "phi_source_theorem_linkage_attempt_from_standalone_phi_route_preparation"
)
SUGGESTED_PREPARATION_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_PREPARED_"
    "C_SOURCE_PHI_LINKAGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_"
    "PROMOTION"
)
STRICT_SUGGESTED_PREPARATION_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_PREPARED_"
    "ON_SHELL_SCALAR_RESIDUAL_ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_"
    "PROMOTION"
)

ACCEPTED_REVIEW_FINDINGS = [
    "phi-source theorem-linkage obligation packet accepted",
    "C_source^phi route scoped from prior standalone phi registry",
    "C_source^nu[g, phi] definition preserved",
    "scalar/on-shell residual identity preserved",
    "R_i^phi definition preserved",
    "no proof execution",
    "no theorem discharge",
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR or EM-QFT closure",
    "no general C_k closure",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

ROUTE_PURITY_WATCH_ITEMS = [
    "no A-sector route import",
    "no psi-A sourced Maxwell import",
    "no QFT-GR source-route import",
    "no silent replacement of the phi residual identity",
]

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no C_source^phi discharge during review",
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR or EM-QFT closure",
    "no general C_k closure",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceTheoremLinkageObligationPacketResultReview.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "review_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_source_phi_discharged": False,
        "phi_source_theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
        "C_k_rule_promotion_authorized": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "psi_A_sourced_Maxwell_substitution": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "A_sector_closure_claimed": False,
        "sourced_maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
    }


def _packet_valid(packet: dict[str, Any]) -> bool:
    return (
        packet.get("schema_id") == PACKET_SCHEMA_ID
        and packet.get("packet_id") == PREPARED_PACKET_ID
        and packet.get("outcome_id") == PACKET_OUTCOME
        and packet.get("packet_result") == PACKET_OUTCOME
        and packet.get("strict_packet_result") == STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == CONSUMED_TARGET
        and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and packet.get("standalone_phi_source_route") == STANDALONE_PHI_SOURCE_ROUTE
        and packet.get("C_source_phi_residual_definition")
        == C_SOURCE_PHI_RESIDUAL_DEFINITION
        and packet.get("source_admissibility_condition")
        == C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
        and packet.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
        and packet.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
        and packet.get("A_source_route_imported") is False
        and packet.get("psi_A_sourced_Maxwell_imported") is False
        and packet.get("QFT_GR_source_route_imported") is False
        and packet.get("proof_attempt_executed") is False
        and packet.get("theorem_discharged") is False
        and packet.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_source_theorem_linkage_obligation_packet_result_review"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_source_theorem_linkage_obligation_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    acceptance_criteria = {
        "consumes_expected_packet_result": _packet_valid(packet),
        "phi_source_packet_accepted": packet.get("accepted") is True,
        "standalone_phi_source_registry_scope_preserved": (
            packet.get("standalone_phi_source_route") == STANDALONE_PHI_SOURCE_ROUTE
            and packet.get("C_source_phi_residual_definition")
            == C_SOURCE_PHI_RESIDUAL_DEFINITION
            and packet.get("C_source_phi_source_admissibility_condition")
            == C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
            and packet.get("C_source_phi_target_statement")
            == C_SOURCE_PHI_TARGET_STATEMENT
        ),
        "scalar_on_shell_residual_identity_preserved": (
            packet.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and packet.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
            and packet.get("on_shell_implication_form") == ON_SHELL_IMPLICATION_FORM
        ),
        "selected_policy_context_preserved": (
            packet.get("field_euler_lagrange_equation")
            == FIELD_EULER_LAGRANGE_EQUATION
            and packet.get("stress_energy_under_selected_policy")
            == STRESS_ENERGY_UNDER_SELECTED_POLICY
            and packet.get("route_bundle_admissibility_form")
            == ROUTE_BUNDLE_ADMISSIBILITY_FORM
        ),
        "route_contamination_blocked": (
            packet.get("A_source_route_imported") is False
            and packet.get("psi_A_sourced_Maxwell_imported") is False
            and packet.get("QFT_GR_source_route_imported") is False
            and packet.get("proof_attempt_executed") is False
            and packet.get("theorem_discharged") is False
        ),
        "review_only_no_theorem_execution": True,
        "blocked_claims_preserved": PACKET_BOUNDARY_ITEMS
        == [
            "no proof execution",
            "no theorem discharge",
            "no phi-sector closure",
            "no full scalar/QFT closure",
            "no QFT-GR closure",
            "no EM-QFT closure",
            "no general C_k closure",
            "no action embedding",
            "no variation",
            "no empirical validation",
            "no master-action promotion",
        ],
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "suggested_preparation_outcome": SUGGESTED_PREPARATION_OUTCOME,
        "strict_suggested_preparation_outcome": (
            STRICT_SUGGESTED_PREPARATION_OUTCOME
        ),
        "prepared_packet_schema_id": PACKET_SCHEMA_ID,
        "prepared_packet_id": PREPARED_PACKET_ID,
        "prepared_packet_outcome": PACKET_OUTCOME,
        "prepared_packet_result": PACKET_OUTCOME,
        "prepared_packet_strict_result": STRICT_PACKET_RESULT,
        "prepared_packet_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "packet_scope_record": PACKET_SCOPE_RECORD,
        "watch_items": PACKET_WATCH_ITEMS,
        "selected_obligation": "C_source^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_source^phi",
        "standalone_phi_source_route": STANDALONE_PHI_SOURCE_ROUTE,
        "standalone_phi_source_route_preserved": accepted,
        "C_source_phi_residual_definition": C_SOURCE_PHI_RESIDUAL_DEFINITION,
        "C_source_phi_source_admissibility_condition": (
            C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
        ),
        "C_source_phi_target_statement": C_SOURCE_PHI_TARGET_STATEMENT,
        "source_admissibility_condition": C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
        "stress_divergence_target": STRESS_DIVERGENCE_TARGET,
        "likely_schematic_route": LIKELY_SCHEMATIC_ROUTE,
        "exact_registry_statement_frozen": accepted,
        "scalar_on_shell_residual_identity_preserved": accepted,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "field_euler_lagrange_equation": FIELD_EULER_LAGRANGE_EQUATION,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        "same_T_phi_definition": True,
        "same_phi_sector_route": True,
        "same_scalar_on_shell_assumptions": True,
        "same_covariant_derivative_convention": True,
        "same_sign_and_index_conventions": True,
        "same_domain_and_boundary_assumptions": True,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "psi_A_sourced_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "route_contamination_guard": (
            "review accepts only the frozen standalone phi route; do not "
            "import A-sector, psi-A sourced Maxwell, or QFT-GR source routes "
            "and do not replace the scalar/on-shell residual identity"
        ),
        "attempt_preparation_only_selected": True,
        "scope_only": True,
        "proof_execution_blocked": True,
        "theorem_discharge_blocked": True,
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below theorem discharge, seam closure, empirical prediction, "
            "empirical confirmation, and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the scoped standalone phi-source "
            "theorem-linkage obligation packet. It preserves C_source^nu[g, "
            "phi] := nabla_mu T_phi^{mu nu}, C_source^nu[g, phi] = 0, the "
            "scalar/on-shell residual identity C_source^nu = sum_i R_i^phi "
            "nabla^nu phi_i, and R_i^phi := Box_g phi_i + partial_i V(phi). "
            "It does not execute a proof, discharge C_source^phi, claim "
            "phi-sector closure, claim full scalar/QFT closure, close EM-QFT "
            "or QFT-GR, claim general C_k closure, embed or vary an action, "
            "claim empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_source_theorem_linkage_obligation_packet_result",
            "fail to accept the phi-source packet scope",
            "fail to preserve C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
            "fail to preserve C_source^nu[g, phi] = 0",
            "silently replace C_source^nu = sum_i R_i^phi nabla^nu phi_i",
            "silently replace R_i^phi := Box_g phi_i + partial_i V(phi)",
            "silently import A-sector source route",
            "silently import psi-A sourced Maxwell route",
            "silently import QFT-GR source route",
            "execute proof during review",
            "discharge C_source^phi during review",
            "claim phi-sector closure",
            "claim full scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiSourceTheoremLinkageObligationPacketResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "prepared_packet_file": _ptr(packet_path),
            "prepared_packet_lean_file": _ptr(PACKET_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the standalone phi-source theorem-linkage obligation "
            "packet without executing or discharging the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_phi_source_theorem_linkage_obligation_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "C_source_phi_residual_definition": payload[
                    "C_source_phi_residual_definition"
                ],
                "residual_identity_form": payload["residual_identity_form"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "theorem_discharged": payload["theorem_discharged"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
