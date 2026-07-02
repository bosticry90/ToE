from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_theorem_linkage_obligation_packet_report import (
    BOUNDARY_ITEMS as PACKET_BOUNDARY_ITEMS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLOSEOUT_OUTCOME,
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    DEFAULT_OUT as PACKET_PATH,
    EXACT_PRIOR_TRANSPORT_ADMISSIBILITY_TARGET,
    EXACT_PRIOR_TRANSPORT_STATEMENT,
    EXACT_PRIOR_TRANSPORT_TARGET,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    LIKELY_PLAIN_MEANING,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as PREPARED_PACKET_OUTCOME,
    PACKET_ID as PREPARED_PACKET_ID,
    PACKET_SCOPE_RECORD,
    RECOVERY_ITEMS,
    SCHEMA_ID as PREPARED_PACKET_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    STANDALONE_PHI_TRANSPORT_ROUTE,
    STRICT_PACKET_RESULT as PREPARED_STRICT_PACKET_RESULT,
    STRICT_SUGGESTED_REVIEW_OUTCOME,
    SUGGESTED_REVIEW_OUTCOME,
    TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_CLOSEOUT_RULE_ROLE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    WATCH_ITEMS as PACKET_WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-01T00:00:00Z"

SCHEMA_ID = "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260701_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = SUGGESTED_REVIEW_OUTCOME
STRICT_REVIEW_RESULT = STRICT_SUGGESTED_REVIEW_OUTCOME
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_transport_theorem_linkage_obligation_packet_result_review_accepts_"
    "standalone_phi_transport_scope_no_proof_execution_or_C_k_rule_promotion"
)

NEXT_TARGET = (
    "prepare_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route"
)
NEXT_TARGET_KIND = (
    "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_"
    "preparation"
)
SUGGESTED_ATTEMPT_PREPARATION_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "PREPARED_COMPONENTWISE_TRANSPORT_ZERO_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_"
    "OR_CK_RULE_PROMOTION"
)
STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "PREPARED_ACTION_TO_REGIME_TRANSPORT_MATCH_TARGET_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)

ACCEPTED_REVIEW_FINDINGS = [
    "phi-transport theorem-linkage obligation packet accepted",
    "C_transport^phi route scoped from prior standalone phi transport registry",
    "exact five-component transport tuple preserved",
    "ACTION -> VARIATION transport component preserved",
    "VARIATION -> BRIDGE transport component preserved",
    "BRIDGE -> SOURCE transport component preserved",
    "SOURCE -> RESIDUAL transport component preserved",
    "RESIDUAL -> REGIME transport component preserved",
    "target C_transport^phi = 0 preserved",
    "no proof execution",
    "no theorem discharge",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

LIKELY_COMPONENTWISE_ATTEMPT_ROUTE = [
    "Transport_ACTION_VARIATION^phi = 0",
    "Transport_VARIATION_BRIDGE^phi = 0",
    "Transport_BRIDGE_SOURCE^phi = 0",
    "Transport_SOURCE_RESIDUAL^phi = 0",
    "Transport_RESIDUAL_REGIME^phi = 0",
    "therefore: C_transport^phi = (0, 0, 0, 0, 0)",
    "therefore: C_transport^phi = 0",
]

ROUTE_PURITY_WATCH_ITEMS = [
    "recover exact C_transport^phi statement from the prior standalone phi transport-consistency registry",
    "do not invent a new transport formula",
    "do not silently substitute C_source^phi",
    "do not silently substitute C_bridge^phi",
    "do not silently substitute A-sector routes",
    "do not silently substitute psi-A routes",
    "do not silently substitute QFT-GR routes",
    "do not silently substitute master-action routes",
    "no proof execution during review",
]

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no C_transport^phi discharge during review",
    "no theorem discharge",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
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
    / "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260701_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportTheoremLinkageObligationPacketResultReview.lean"
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


def _blocked_boundary_flags() -> dict[str, bool]:
    return {
        "review_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_transport_phi_discharged": False,
        "C_transport_phi_theorem_linkage_gap_discharged": False,
        "C_transport_phi_theorem_linkage_obligation_discharged": False,
        "C_transport_phi_proof_executed": False,
        "C_transport_phi_closure_claimed": False,
        "transport_consistency_proved": False,
        "transport_components_proved": False,
        "transport_candidate_rule_proved": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_proved": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "new_transport_formula_invented": False,
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused": False,
        "C_bridge_phi_route_reused_as_transport": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "master_action_route_substituted": False,
        "J_current_imported": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
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
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "new_physics_created": False,
    }


def _packet_valid(packet: dict[str, Any]) -> bool:
    component_forms = [row["component_form"] for row in TRANSPORT_COMPONENTS]
    return (
        packet.get("schema_id") == PREPARED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == PREPARED_PACKET_ID
        and packet.get("outcome_id") == PREPARED_PACKET_OUTCOME
        and packet.get("packet_result") == PREPARED_PACKET_OUTCOME
        and packet.get("strict_packet_result") == PREPARED_STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == CONSUMED_TARGET
        and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and packet.get("standalone_phi_transport_route") == STANDALONE_PHI_TRANSPORT_ROUTE
        and packet.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
        and packet.get("transport_constraint_equation") == TRANSPORT_CONSTRAINT_EQUATION
        and packet.get("transport_admissibility_constraint_form")
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        and packet.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
        and packet.get("transport_component_forms") == component_forms
        and packet.get("exact_prior_transport_statement") == EXACT_PRIOR_TRANSPORT_STATEMENT
        and packet.get("exact_prior_transport_target") == EXACT_PRIOR_TRANSPORT_TARGET
        and packet.get("exact_prior_transport_admissibility_target")
        == EXACT_PRIOR_TRANSPORT_ADMISSIBILITY_TARGET
        and packet.get("proof_attempt_executed") is False
        and packet.get("theorem_discharged") is False
        and packet.get("C_transport_phi_discharged") is False
        and packet.get("new_transport_formula_invented") is False
        and packet.get("master_action_promoted") is False
        and packet.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_transport_theorem_linkage_obligation_packet_result_review"
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
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_review": "PASSED_SERIAL_RERUN",
        "lean_status_wording_lines_for_review": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_transport_theorem_linkage_obligation_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    component_forms = [row["component_form"] for row in TRANSPORT_COMPONENTS]
    acceptance_criteria = {
        "consumes_expected_packet_result": _packet_valid(packet),
        "phi_transport_packet_accepted": packet.get("accepted") is True,
        "standalone_phi_transport_registry_scope_preserved": (
            packet.get("standalone_phi_transport_route")
            == STANDALONE_PHI_TRANSPORT_ROUTE
            and packet.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
            and packet.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
            and packet.get("transport_admissibility_constraint_form")
            == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "five_component_transport_tuple_preserved": (
            packet.get("transport_component_forms") == component_forms
            and packet.get("transport_component_count") == 5
        ),
        "target_C_transport_phi_zero_preserved": (
            packet.get("transport_constraint_equation") == "C_transport^phi = 0"
        ),
        "route_contamination_blocked": (
            packet.get("C_source_phi_route_reused") is False
            and packet.get("C_bridge_phi_route_reused") is False
            and packet.get("A_sector_route_imported") is False
            and packet.get("psi_A_route_imported") is False
            and packet.get("QFT_GR_route_imported") is False
            and packet.get("master_action_route_substituted") is False
            and packet.get("proof_attempt_executed") is False
            and packet.get("theorem_discharged") is False
        ),
        "review_only_no_theorem_execution": True,
        "blocked_claims_preserved": PACKET_BOUNDARY_ITEMS
        == [
            "no proof execution",
            "no theorem discharge",
            "no phi-sector closure",
            "no scalar/QFT closure",
            "no QFT-GR closure",
            "no EM-QFT closure",
            "no seam closure",
            "no general C_k closure",
            "no C_k promotion",
            "no action embedding",
            "no variation",
            "no empirical validation",
            "no master-action promotion",
        ],
        "lean_status_wording_preserved": (
            LEAN_STATUS_WORDING_LINES_FOR_PACKET
            == [
                "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
                "scoped Lean targets = PASSED_SERIAL_RERUN",
            ]
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "suggested_attempt_preparation_outcome": SUGGESTED_ATTEMPT_PREPARATION_OUTCOME,
        "strict_suggested_attempt_preparation_outcome": (
            STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME
        ),
        "prepared_packet_schema_id": PREPARED_PACKET_SCHEMA_ID,
        "prepared_packet_id": PREPARED_PACKET_ID,
        "prepared_packet_outcome": PREPARED_PACKET_OUTCOME,
        "prepared_packet_result": PREPARED_PACKET_OUTCOME,
        "prepared_packet_strict_result": PREPARED_STRICT_PACKET_RESULT,
        "prepared_packet_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "packet_scope_record": PACKET_SCOPE_RECORD,
        "recovery_items": RECOVERY_ITEMS,
        "packet_watch_items": PACKET_WATCH_ITEMS,
        "packet_boundary_items": PACKET_BOUNDARY_ITEMS,
        "selected_obligation": "C_transport^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_transport^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_transport^phi",
        "standalone_phi_transport_route": STANDALONE_PHI_TRANSPORT_ROUTE,
        "standalone_phi_transport_route_preserved": accepted,
        "exact_five_component_transport_tuple_preserved": accepted,
        "target_C_transport_phi_zero_preserved": accepted,
        "exact_prior_transport_statement_frozen": accepted,
        "exact_prior_transport_target_frozen": accepted,
        "exact_prior_transport_statement": EXACT_PRIOR_TRANSPORT_STATEMENT,
        "exact_prior_transport_target": EXACT_PRIOR_TRANSPORT_TARGET,
        "exact_prior_transport_admissibility_target": (
            EXACT_PRIOR_TRANSPORT_ADMISSIBILITY_TARGET
        ),
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_closeout_rule_classification": (
            TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
        ),
        "transport_rule_role": TRANSPORT_CLOSEOUT_RULE_ROLE,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": (
            TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": component_forms,
        "transport_components_preserved_unproved": True,
        "transport_action_variation_component_preserved": accepted,
        "transport_variation_bridge_component_preserved": accepted,
        "transport_bridge_source_component_preserved": accepted,
        "transport_source_residual_component_preserved": accepted,
        "transport_residual_regime_component_preserved": accepted,
        "transport_action_embedding_chain_form": TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "likely_plain_meaning": LIKELY_PLAIN_MEANING,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_rule_closeout_outcome": BRIDGE_RULE_CLOSEOUT_OUTCOME,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "completed_local_theorem_linkage_chain": COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
        "likely_componentwise_attempt_route": LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
        "likely_componentwise_attempt_route_count": len(
            LIKELY_COMPONENTWISE_ATTEMPT_ROUTE
        ),
        "componentwise_transport_zero_route_indexed": accepted,
        "attempt_preparation_only_selected": True,
        "review_only": True,
        "scope_only": True,
        "proof_execution_blocked": True,
        "theorem_discharge_blocked": True,
        "master_action_promotion_watch": (
            "Do not treat the action-to-regime transport match as action "
            "variation or master-action promotion. This remains only a local "
            "C_transport^phi theorem-linkage obligation."
        ),
        "route_contamination_guard": (
            "review accepts only the frozen standalone phi transport route; do "
            "not substitute C_source^phi, C_bridge^phi, A-sector, psi-A, "
            "QFT-GR, or master-action routes and do not invent a new "
            "transport formula"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below theorem discharge, phi-sector closure, scalar/QFT closure, "
            "seam closure, empirical prediction, empirical confirmation, and "
            "mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the scoped standalone phi transport "
            "theorem-linkage packet. It preserves C_transport^phi := "
            "(Transport_ACTION_VARIATION^phi, Transport_VARIATION_BRIDGE^phi, "
            "Transport_BRIDGE_SOURCE^phi, Transport_SOURCE_RESIDUAL^phi, "
            "Transport_RESIDUAL_REGIME^phi) and target C_transport^phi = 0. "
            "It does not execute a proof, discharge C_transport^phi, invent a "
            "new transport formula, claim phi-sector closure, claim scalar/QFT "
            "closure, close EM-QFT or QFT-GR, claim general C_k closure, embed "
            "or vary an action, claim empirical validation, or promote the "
            "master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_transport_theorem_linkage_obligation_packet_result",
            "fail to preserve the exact five-component C_transport^phi tuple",
            "fail to preserve C_transport^phi = 0",
            "invent a new transport formula",
            "silently reuse C_source^phi as the transport route",
            "silently reuse C_bridge^phi as the transport route",
            "silently import A-sector, psi-A, QFT-GR, or master-action routes",
            "execute the C_transport^phi proof route",
            "discharge C_transport^phi",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_status_for_review": (
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_review": "PASSED_SERIAL_RERUN",
        "aggregate_lean_validation_status_for_review": "PASSED_SERIAL_RERUN",
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiTransportTheoremLinkageObligationPacketResultReview",
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
    payload.update(_blocked_boundary_flags())
    return payload


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the standalone phi-transport C_transport^phi theorem-linkage "
            "obligation packet without executing or discharging the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = build_phi_transport_theorem_linkage_obligation_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(packet, out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "review_result": packet["review_result"],
                "selected_obligation": packet["selected_obligation"],
                "selected_next_target": packet["selected_next_target"],
                "transport_constraint_form": packet["transport_constraint_form"],
                "transport_constraint_equation": packet[
                    "transport_constraint_equation"
                ],
                "proof_attempt_executed": packet["proof_attempt_executed"],
                "theorem_discharged": packet["theorem_discharged"],
                "new_transport_formula_invented": packet[
                    "new_transport_formula_invented"
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if packet["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
