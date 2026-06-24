from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_transport_consistency_ck_admissibility_rule_closeout_report import (
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLOSEOUT_OUTCOME,
    CONSUMED_TARGET as TRANSPORT_CLOSEOUT_CONSUMED_TARGET,
    DEFAULT_OUT as TRANSPORT_CLOSEOUT_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_GROUP_POLICY,
    KNOWN_A_TRANSPORT_CHAIN_FORM,
    LEAN_VALIDATION_POLICY_ID,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as TRANSPORT_CLOSEOUT_OUTCOME,
    PACKET_ID as TRANSPORT_CLOSEOUT_PACKET_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
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
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_"
    "20260624_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_v0"
PACKET_RESULT = (
    "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_PREPARED_"
    "THREE_ADMISSIBILITY_RULES_SYNTHESIZED_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet_prepared_"
    "three_admissibility_rules_synthesized_no_current_or_em_closure"
)
CONSUMED_TARGET = "prepare_toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet"
NEXT_TARGET = (
    "review_toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet_result"
)
NEXT_TARGET_KIND = (
    "toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet_result_review"
)
REVIEW_OUTCOME_HINT = (
    "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
    "ACCEPTS_THREE_RULE_SYNTHESIS_NO_CURRENT_OR_EM_CLOSURE"
)

SOURCE_RULE_ID = "A_source_admissibility_ck_rule"
SOURCE_RULE_ROLE = "source admissibility"
SOURCE_RULE_CLASSIFICATION = "source-admissibility rule"
SOURCE_RULE_DISPLAY_FORM = "C_source^A = 0"
SOURCE_RULE_PLAIN_MEANING = (
    "the vacuum gauge stress-energy route may source gravity only if conserved"
)
BRIDGE_RULE_ID = "A_bridge_admissibility_ck_rule"
BRIDGE_RULE_ROLE = "bridge admissibility"
BRIDGE_RULE_CLASSIFICATION = "bridge-admissibility rule"
BRIDGE_RULE_PLAIN_MEANING = (
    "the master-action A route must match the selected vacuum U(1) route"
)
TRANSPORT_RULE_ID = "A_transport_consistency_ck_rule"
TRANSPORT_RULE_ROLE = "transport consistency"
TRANSPORT_RULE_DISPLAY_FORM = "C_transport^A = 0"
TRANSPORT_RULE_PLAIN_MEANING = (
    "the vacuum U(1) A route must remain coherent through the derivation chain"
)
RULE_FAMILY_CLASSIFICATION = "first A-relevant three-rule C_k admissibility family"
RULE_EPISTEMIC_STATUS = "admissibility-only"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_"
    "20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeACKSourceBridgeTransportRuleFamilySynthesisPacket.lean"
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
LEAN_VALIDATION_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_VALIDATION_TIER_POLICY_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _rule_family_entries() -> list[dict[str, Any]]:
    return [
        {
            "rule_id": SOURCE_RULE_ID,
            "rule_role": SOURCE_RULE_ROLE,
            "rule_classification": SOURCE_RULE_CLASSIFICATION,
            "epistemic_status": RULE_EPISTEMIC_STATUS,
            "candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
            "constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
            "admissibility_condition": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "family_display_form": SOURCE_RULE_DISPLAY_FORM,
            "plain_meaning": SOURCE_RULE_PLAIN_MEANING,
            "admissibility_only": True,
            "action_term": False,
            "dynamical_law": False,
            "current_coupled": False,
            "sourced_maxwell": False,
            "em_closure": False,
            "qft_gr_closure": False,
            "master_action_promotion": False,
        },
        {
            "rule_id": BRIDGE_RULE_ID,
            "rule_role": BRIDGE_RULE_ROLE,
            "rule_classification": BRIDGE_RULE_CLASSIFICATION,
            "epistemic_status": RULE_EPISTEMIC_STATUS,
            "constraint_form": A_BRIDGE_CONSTRAINT_FORM,
            "constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
            "admissibility_condition": A_BRIDGE_CONSTRAINT_EQUATION,
            "family_display_form": A_BRIDGE_CONSTRAINT_EQUATION,
            "plain_meaning": BRIDGE_RULE_PLAIN_MEANING,
            "admissibility_only": True,
            "action_term": False,
            "dynamical_law": False,
            "current_coupled": False,
            "sourced_maxwell": False,
            "em_closure": False,
            "qft_gr_closure": False,
            "master_action_promotion": False,
        },
        {
            "rule_id": TRANSPORT_RULE_ID,
            "rule_role": TRANSPORT_RULE_ROLE,
            "rule_classification": TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
            "rule_subclassification": TRANSPORT_CLOSEOUT_RULE_ROLE,
            "epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
            "candidate_constraint_id": TRANSPORT_CANDIDATE_ID,
            "candidate_type": TRANSPORT_CANDIDATE_TYPE,
            "constraint_form": TRANSPORT_CONSTRAINT_FORM,
            "constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
            "admissibility_condition": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "family_display_form": TRANSPORT_RULE_DISPLAY_FORM,
            "plain_meaning": TRANSPORT_RULE_PLAIN_MEANING,
            "component_forms": [row["component_form"] for row in TRANSPORT_COMPONENTS],
            "admissibility_only": True,
            "action_term": False,
            "dynamical_law": False,
            "current_coupled": False,
            "sourced_maxwell": False,
            "em_closure": False,
            "qft_gr_closure": False,
            "master_action_promotion": False,
        },
    ]


def _synthesis_criteria() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "transport_closeout_consumed",
            "status": "accepted",
            "evidence": TRANSPORT_CLOSEOUT_OUTCOME,
            "assessment": "The packet consumes the A transport admissibility closeout.",
        },
        {
            "row_id": "source_rule_preserved",
            "status": "accepted",
            "evidence": [SOURCE_RULE_DISPLAY_FORM, SOURCE_ADMISSIBILITY_CONSTRAINT_FORM],
            "assessment": "The A source-admissibility rule is preserved.",
        },
        {
            "row_id": "bridge_rule_preserved",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_EQUATION,
            "assessment": "The A bridge-admissibility rule is preserved.",
        },
        {
            "row_id": "transport_rule_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "The A transport-consistency rule is preserved.",
        },
        {
            "row_id": "three_concrete_A_ck_roles_recorded",
            "status": "accepted",
            "evidence": [SOURCE_RULE_ROLE, BRIDGE_RULE_ROLE, TRANSPORT_RULE_ROLE],
            "assessment": "C_k now has three bounded A-relevant rule roles.",
        },
        {
            "row_id": "admissibility_only_family_classification",
            "status": "accepted",
            "evidence": RULE_EPISTEMIC_STATUS,
            "assessment": "All three A rules remain admissibility-only.",
        },
        {
            "row_id": "no_action_terms_or_dynamical_laws",
            "status": "accepted",
            "evidence": ["not_action_terms=true", "not_dynamical_laws=true"],
            "assessment": "The synthesis does not turn any rule into an action term.",
        },
        {
            "row_id": "no_current_or_sourced_maxwell_or_exchange",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current, sourced Maxwell route, or exchange theorem is introduced.",
        },
        {
            "row_id": "no_transport_proof_or_route_alignment_proof",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "full_route_alignment_proved=false",
            ],
            "assessment": "Transport proof and route-alignment proof remain blocked.",
        },
        {
            "row_id": "no_em_qft_gr_closure_semiclassical_coupling_or_master_promotion",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "Closure, coupling, and promotion remain unclaimed.",
        },
        {
            "row_id": "tiered_validation_records_full_toeformal_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate is recorded as NOT_RUN.",
        },
        {
            "row_id": "result_review_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next strict target reviews this synthesis packet.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_packet(
    *,
    transport_closeout_path: Path = TRANSPORT_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    transport_closeout = _read_json(transport_closeout_path)
    rule_family_entries = _rule_family_entries()
    synthesis_criteria = _synthesis_criteria()
    acceptance_criteria = {
        "transport_closeout_consumed": (
            transport_closeout.get("packet_id") == TRANSPORT_CLOSEOUT_PACKET_ID
            and transport_closeout.get("outcome_id") == TRANSPORT_CLOSEOUT_OUTCOME
            and transport_closeout.get("accepted") is True
            and transport_closeout.get("selected_next_target") == CONSUMED_TARGET
        ),
        "source_rule_form_preserved": (
            transport_closeout.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and transport_closeout.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and transport_closeout.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_rule_form_preserved": (
            transport_closeout.get("A_bridge_constraint_form") == A_BRIDGE_CONSTRAINT_FORM
            and transport_closeout.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and transport_closeout.get("bridge_admissibility_constraint_form")
            == A_BRIDGE_CONSTRAINT_EQUATION
        ),
        "transport_rule_form_preserved": (
            transport_closeout.get("transport_constraint_form")
            == TRANSPORT_CONSTRAINT_FORM
            and transport_closeout.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
            and transport_closeout.get("transport_admissibility_constraint_form")
            == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "rule_family_has_three_entries": len(rule_family_entries) == 3,
        "synthesis_criteria_all_accepted": all(
            row["status"] == "accepted" for row in synthesis_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "review_outcome_hint": REVIEW_OUTCOME_HINT,
        "transport_closeout_consumed_target": TRANSPORT_CLOSEOUT_CONSUMED_TARGET,
        "transport_closeout_packet_id": TRANSPORT_CLOSEOUT_PACKET_ID,
        "transport_closeout_outcome": TRANSPORT_CLOSEOUT_OUTCOME,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "bridge_rule_closeout_outcome": BRIDGE_RULE_CLOSEOUT_OUTCOME,
        "A_ck_admissibility_rule_family_count": 3,
        "rule_family_classification": RULE_FAMILY_CLASSIFICATION,
        "concrete_A_ck_rule_roles": [
            SOURCE_RULE_ROLE,
            BRIDGE_RULE_ROLE,
            TRANSPORT_RULE_ROLE,
        ],
        "rule_family_display_forms": [
            SOURCE_RULE_DISPLAY_FORM,
            A_BRIDGE_CONSTRAINT_EQUATION,
            TRANSPORT_RULE_DISPLAY_FORM,
        ],
        "source_rule_id": SOURCE_RULE_ID,
        "source_rule_role": SOURCE_RULE_ROLE,
        "source_rule_classification": SOURCE_RULE_CLASSIFICATION,
        "source_rule_epistemic_status": RULE_EPISTEMIC_STATUS,
        "source_rule_display_form": SOURCE_RULE_DISPLAY_FORM,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "source_rule_plain_meaning": SOURCE_RULE_PLAIN_MEANING,
        "bridge_rule_id": BRIDGE_RULE_ID,
        "bridge_rule_role": BRIDGE_RULE_ROLE,
        "bridge_rule_classification": BRIDGE_RULE_CLASSIFICATION,
        "bridge_rule_epistemic_status": RULE_EPISTEMIC_STATUS,
        "A_bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_rule_plain_meaning": BRIDGE_RULE_PLAIN_MEANING,
        "transport_rule_id": TRANSPORT_RULE_ID,
        "transport_rule_role": TRANSPORT_RULE_ROLE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_closeout_rule_classification": TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
        "transport_rule_subclassification": TRANSPORT_CLOSEOUT_RULE_ROLE,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_rule_display_form": TRANSPORT_RULE_DISPLAY_FORM,
        "transport_rule_plain_meaning": TRANSPORT_RULE_PLAIN_MEANING,
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [row["component_form"] for row in TRANSPORT_COMPONENTS],
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "known_A_transport_chain_form": KNOWN_A_TRANSPORT_CHAIN_FORM,
        "rule_family_entries": rule_family_entries,
        "synthesis_criteria": synthesis_criteria,
        "synthesis_criteria_count": len(synthesis_criteria),
        "synthesis_criteria_accepted_count": sum(
            1 for row in synthesis_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "synthesis_packet_prepared": True,
        "synthesis_packet_accepted": True,
        "A_ck_rule_family_synthesized": True,
        "three_rule_family_synthesized": True,
        "three_A_relevant_ck_admissibility_rules_synthesized": True,
        "source_bridge_transport_rules_synthesized": True,
        "source_admissibility_rule_synthesized": True,
        "bridge_admissibility_rule_synthesized": True,
        "transport_consistency_rule_synthesized": True,
        "source_admissibility_rule_preserved": True,
        "bridge_admissibility_rule_preserved": True,
        "transport_consistency_rule_preserved": True,
        "c_k_acquired_three_concrete_A_relevant_rule_roles": True,
        "source_rule_decides_A_conserved_vacuum_source_permission": True,
        "bridge_rule_decides_A_vacuum_route_consistency": True,
        "transport_rule_decides_A_derivation_chain_coherence": True,
        "all_three_rules_admissibility_only": True,
        "all_three_rules_not_action_terms": True,
        "all_three_rules_not_dynamical_laws": True,
        "all_three_rules_not_current_coupled": True,
        "rule_family_interprets_ck_as_seam_admissibility_layer": True,
        "result_review_authorized": True,
        "review_executed": False,
        "another_A_route_selected": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "external_current_native_derivation_selected": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_route_derived": False,
        "matter_current_exchange_route_proved": False,
        "matter_gauge_energy_exchange_proved": False,
        "constraint_as_action_term_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_law_claimed": False,
        "candidate_recorded_as_new_physical_law": False,
        "candidate_recorded_as_action_term": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_action_embedding_constructed": False,
        "C_k_variation_executed": False,
        "lambda_variation_executed": False,
        "metric_variation_executed": False,
        "A_variation_executed": False,
        "bridge_admissibility_proved": False,
        "route_alignment_verified": False,
        "full_route_alignment_proved": False,
        "full_route_alignment_proof_claimed": False,
        "source_admissibility_proved": False,
        "source_conservation_proved": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
        "transport_components_proved": False,
        "transport_candidate_functional_defined": False,
        "fully_concrete_ck_functional_defined": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "mathematical_statement": (
            "The A/C_k branch now has a three-rule admissibility family: "
            "C_source^A = 0 for vacuum source admissibility, C_bridge^A = 0 "
            "for vacuum U(1) bridge admissibility, and C_transport^A = 0 for "
            "derivation-chain transport consistency."
        ),
        "non_claim_boundary": (
            "This synthesis packet records the source, bridge, and transport "
            "A/C_k admissibility-rule family only. The three rules are vacuum "
            "U(1) admissibility-only rules, not action terms, not dynamical "
            "laws, not current-coupled rules, not sourced Maxwell, not EM "
            "closure, not QFT-GR closure, and not master-action promotion. "
            "It does not derive J^nu, does not derive a psi-current route, "
            "does not derive an external-current native route, does not prove "
            "matter/current exchange, does not execute C_k variation, does "
            "not embed any rule in an action, does not prove transport "
            "consistency, does not prove full route alignment, does not prove "
            "source admissibility, does not prove bridge admissibility, does "
            "not claim semiclassical coupling, records no Phase 2 "
            "authorization, does not claim empirical validation, and does "
            "not authorize public readiness. The full ToeFormal aggregate is "
            "recorded as NOT_RUN for this packet."
        ),
        "critical_gate_fail_conditions": [
            "claim any A/C_k rule is an action term",
            "claim any A/C_k rule is a new dynamical law",
            "execute C_k variation",
            "derive J^nu",
            "derive sourced Maxwell",
            "prove matter/current exchange",
            "claim transport proof",
            "claim full route-alignment proof",
            "claim EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "claim empirical validation",
            "authorize Phase 2",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeACKSourceBridgeTransportRuleFamilySynthesisPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "transport_closeout_file": _ptr(transport_closeout_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A/C_k source-bridge-transport "
            "rule-family synthesis packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "packet_result": packet["packet_result"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
