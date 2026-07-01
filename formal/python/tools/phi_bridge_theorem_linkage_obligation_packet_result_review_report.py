from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_theorem_linkage_obligation_packet_report import (
    BOUNDARY_ITEMS as PACKET_BOUNDARY_ITEMS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as PACKET_PATH,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_ID as PREPARED_PACKET_ID,
    PACKET_SCOPE_RECORD,
    RECOVERY_ITEMS,
    SCHEMA_ID as PACKET_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    STANDALONE_PHI_BRIDGE_ROUTE,
    STRICT_PACKET_RESULT,
    WATCH_ITEMS as PACKET_WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260630_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "C_BRIDGE_PHI_ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_PHI_BRIDGE_ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_obligation_packet_result_review_accepts_"
    "standalone_phi_bridge_scope_no_proof_execution"
)

NEXT_TARGET = "prepare_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route"
NEXT_TARGET_KIND = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_preparation"
)
SUGGESTED_PREPARATION_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "PREPARED_C_BRIDGE_PHI_COMPONENT_ZERO_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_"
    "OR_CK_RULE_PROMOTION"
)
STRICT_SUGGESTED_PREPARATION_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "PREPARED_MASTER_WITNESS_ROUTE_MATCH_TARGET_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)

ACCEPTED_REVIEW_FINDINGS = [
    "phi-bridge theorem-linkage obligation packet accepted",
    "C_bridge^phi route scoped from prior standalone phi bridge registry",
    "exact tuple definition preserved",
    "E_phi^master - E_phi^witness component preserved",
    "T_phi^master - T_phi^witness component preserved",
    "C_source^phi - nabla_mu T_phi^{mu nu} component preserved",
    "target C_bridge^phi = 0 preserved",
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
    "E_phi^master = E_phi^witness",
    "T_phi^master = T_phi^witness",
    "C_source^phi = nabla_mu T_phi^{mu nu}",
    "therefore: C_bridge^phi = (0, 0, 0)",
    "therefore: C_bridge^phi = 0",
]

ROUTE_PURITY_WATCH_ITEMS = [
    "do not let master/witness route match become master-action promotion",
    "local C_bridge^phi theorem-linkage obligation only",
    "no C_source^phi route substitution",
    "no A-source route substitution",
    "no psi-A route substitution",
    "no QFT-GR route substitution",
    "no proof execution during review",
]

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no C_bridge^phi discharge during review",
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
    / "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageObligationPacketResultReview.lean"
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
        "C_bridge_phi_discharged": False,
        "C_bridge_phi_theorem_linkage_gap_discharged": False,
        "C_bridge_phi_theorem_linkage_obligation_discharged": False,
        "C_bridge_phi_proof_executed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "C_source_phi_route_reused": False,
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
        "new_bridge_formula_invented": False,
        "new_physics_created": False,
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
        and packet.get("standalone_phi_bridge_route") == STANDALONE_PHI_BRIDGE_ROUTE
        and packet.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
        and packet.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
        and packet.get("bridge_admissibility_constraint_form")
        == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        and packet.get("bridge_route_field_equation_match")
        == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
        and packet.get("bridge_route_stress_energy_match")
        == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
        and packet.get("bridge_route_source_residual_match")
        == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        and packet.get("bridge_candidate_rule_plain_meaning")
        == BRIDGE_CANDIDATE_RULE_PLAIN_MEANING
        and packet.get("bridge_route_alignment_sequence")
        == BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
        and packet.get("proof_attempt_executed") is False
        and packet.get("theorem_discharged") is False
        and packet.get("C_bridge_phi_discharged") is False
        and packet.get("master_action_promoted") is False
        and packet.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_bridge_theorem_linkage_obligation_packet_result_review"
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


def build_phi_bridge_theorem_linkage_obligation_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    acceptance_criteria = {
        "consumes_expected_packet_result": _packet_valid(packet),
        "phi_bridge_packet_accepted": packet.get("accepted") is True,
        "standalone_phi_bridge_registry_scope_preserved": (
            packet.get("standalone_phi_bridge_route") == STANDALONE_PHI_BRIDGE_ROUTE
            and packet.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and packet.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
            and packet.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_components_preserved": (
            packet.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and packet.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and packet.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "route_contamination_blocked": (
            packet.get("C_source_phi_route_reused") is False
            and packet.get("A_source_route_imported") is False
            and packet.get("psi_A_sourced_Maxwell_imported") is False
            and packet.get("QFT_GR_source_route_imported") is False
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
        else "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
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
        "recovery_items": RECOVERY_ITEMS,
        "packet_watch_items": PACKET_WATCH_ITEMS,
        "packet_boundary_items": PACKET_BOUNDARY_ITEMS,
        "selected_obligation": "C_bridge^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_bridge^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_bridge^phi",
        "standalone_phi_bridge_route": STANDALONE_PHI_BRIDGE_ROUTE,
        "standalone_phi_bridge_route_preserved": accepted,
        "exact_tuple_definition_preserved": accepted,
        "target_C_bridge_phi_zero_preserved": accepted,
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_plain": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
        "bridge_component_count": 3,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "likely_componentwise_attempt_route": LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
        "likely_componentwise_attempt_route_count": len(
            LIKELY_COMPONENTWISE_ATTEMPT_ROUTE
        ),
        "master_witness_route_match_target_indexed": accepted,
        "attempt_preparation_only_selected": True,
        "review_only": True,
        "scope_only": True,
        "proof_execution_blocked": True,
        "theorem_discharge_blocked": True,
        "master_action_promotion_watch": (
            "Do not let master/witness route match become master-action "
            "promotion. This remains only a local C_bridge^phi theorem-linkage "
            "obligation."
        ),
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "master_action_route_substituted": False,
        "route_contamination_guard": (
            "review accepts only the frozen standalone phi bridge route; do "
            "not substitute C_source^phi, A-source, psi-A, QFT-GR, or "
            "master-action routes and do not treat master/witness route match "
            "as master-action promotion"
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
            "This result review accepts only the scoped standalone phi-bridge "
            "theorem-linkage obligation packet. It preserves C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu}) and target "
            "C_bridge^phi = 0, plus the three component match statements. It "
            "does not execute a proof, discharge C_bridge^phi, claim "
            "phi-sector closure, claim scalar/QFT closure, close EM-QFT or "
            "QFT-GR, claim general C_k closure, embed or vary an action, "
            "claim empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_bridge_theorem_linkage_obligation_packet_result",
            "fail to accept the phi-bridge packet scope",
            "fail to preserve exact C_bridge^phi tuple definition",
            "fail to preserve C_bridge^phi = 0",
            "silently replace a bridge component",
            "silently import C_source^phi, A-source, psi-A, QFT-GR, or master-action route substitution",
            "execute proof during review",
            "discharge C_bridge^phi during review",
            "treat master/witness route match as master-action promotion",
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
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageObligationPacketResultReview",
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
            "Review the standalone phi-bridge theorem-linkage obligation "
            "packet without executing or discharging the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_phi_bridge_theorem_linkage_obligation_packet_result_review(
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
                "bridge_constraint_form": payload["bridge_constraint_form"],
                "bridge_constraint_equation": payload["bridge_constraint_equation"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "theorem_discharged": payload["theorem_discharged"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
