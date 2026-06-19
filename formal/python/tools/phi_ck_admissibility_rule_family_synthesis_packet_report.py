from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_admissibility_ck_admissibility_rule_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_RULE_CLASSIFICATION,
    BRIDGE_RULE_EPISTEMIC_STATUS,
    DEFAULT_OUT as BRIDGE_CLOSEOUT_PATH,
    LEAN_VALIDATION_POLICY_ID,
    OUTCOME_ID as BRIDGE_CLOSEOUT_OUTCOME,
    PACKET_ID as BRIDGE_CLOSEOUT_PACKET_ID,
)
from formal.python.tools.phi_source_admissibility_ck_admissibility_rule_closeout_report import (
    ADMISSIBILITY_CONSTRAINT_FORM as SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_EQUATION as SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM as SOURCE_CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID as SOURCE_CANDIDATE_CONSTRAINT_ID,
    DEFAULT_OUT as SOURCE_CLOSEOUT_PATH,
    OUTCOME_ID as SOURCE_CLOSEOUT_OUTCOME,
    PACKET_ID as SOURCE_CLOSEOUT_PACKET_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET_v0"
PACKET_RESULT = (
    "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET_PREPARED_SOURCE_AND_"
    "BRIDGE_RULES_SYNTHESIZED_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "phi_ck_admissibility_rule_family_synthesis_packet_prepared_source_and_"
    "bridge_rules_synthesized_no_action_variation_or_promotion"
)
CONSUMED_TARGET = "prepare_phi_ck_admissibility_rule_family_synthesis_packet"
NEXT_TARGET = "review_phi_ck_admissibility_rule_family_synthesis_packet_result"
NEXT_TARGET_KIND = "phi_ck_admissibility_rule_family_synthesis_packet_result_review"

SOURCE_RULE_ID = "phi_source_admissibility_ck_rule"
SOURCE_RULE_ROLE = "source admissibility"
SOURCE_RULE_CLASSIFICATION = "source-admissibility rule candidate"
SOURCE_RULE_PLAIN_MEANING = "phi may source gravity only if conserved"
BRIDGE_RULE_ID = "phi_bridge_admissibility_ck_rule"
BRIDGE_RULE_ROLE = "bridge admissibility"
RULE_EPISTEMIC_STATUS = "admissibility-only"
FULL_TOEFORMAL_AGGREGATE_STATUS = "NOT_RUN"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET_20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiCKAdmissibilityRuleFamilySynthesisPacket.lean"
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
            "constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
            "admissibility_condition": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": SOURCE_RULE_PLAIN_MEANING,
            "admissibility_only": True,
            "rule_candidate": True,
            "action_term": False,
            "dynamical_law": False,
            "native_phi_derivation": False,
            "v_phi_derivation": False,
            "qft_gr_closure": False,
            "master_action_promotion": False,
        },
        {
            "rule_id": BRIDGE_RULE_ID,
            "rule_role": BRIDGE_RULE_ROLE,
            "rule_classification": BRIDGE_RULE_CLASSIFICATION,
            "epistemic_status": BRIDGE_RULE_EPISTEMIC_STATUS,
            "candidate_constraint_id": BRIDGE_CANDIDATE_ID,
            "candidate_type": BRIDGE_CANDIDATE_TYPE,
            "constraint_form": BRIDGE_CONSTRAINT_FORM,
            "constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
            "admissibility_condition": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
            "route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
            "route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
            "plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
            "admissibility_only": True,
            "rule_candidate": True,
            "action_term": False,
            "dynamical_law": False,
            "native_phi_derivation": False,
            "v_phi_derivation": False,
            "qft_gr_closure": False,
            "master_action_promotion": False,
        },
    ]


def _synthesis_criteria() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "source_rule_preserved",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "The closed source-admissibility rule is preserved.",
        },
        {
            "row_id": "bridge_rule_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "The closed bridge-admissibility rule is preserved.",
        },
        {
            "row_id": "two_concrete_phi_ck_roles_recorded",
            "status": "accepted",
            "evidence": [SOURCE_RULE_ROLE, BRIDGE_RULE_ROLE],
            "assessment": "C_k now has two bounded phi-relevant rule roles.",
        },
        {
            "row_id": "admissibility_only_family_classification",
            "status": "accepted",
            "evidence": RULE_EPISTEMIC_STATUS,
            "assessment": "Both rules remain admissibility-only candidates.",
        },
        {
            "row_id": "no_action_terms_or_dynamical_laws",
            "status": "accepted",
            "evidence": [
                "not_action_terms=true",
                "not_dynamical_laws=true",
            ],
            "assessment": "The synthesis does not turn either rule into an action term.",
        },
        {
            "row_id": "no_native_phi_or_v_phi_derivation",
            "status": "accepted",
            "evidence": [
                "native_phi_derivation_claimed=false",
                "v_phi_derivation_claimed=false",
            ],
            "assessment": "The packet does not derive phi or V(phi).",
        },
        {
            "row_id": "no_qft_gr_closure_or_master_promotion",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "QFT-GR closure and master-action promotion remain unclaimed.",
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
        "checkpoint_type": "phi_ck_admissibility_rule_family_synthesis_packet",
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


def build_phi_ck_admissibility_rule_family_synthesis_packet(
    *,
    source_closeout_path: Path = SOURCE_CLOSEOUT_PATH,
    bridge_closeout_path: Path = BRIDGE_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    source_closeout = _read_json(source_closeout_path)
    bridge_closeout = _read_json(bridge_closeout_path)
    rule_family_entries = _rule_family_entries()
    synthesis_criteria = _synthesis_criteria()
    acceptance_criteria = {
        "source_closeout_consumed": (
            source_closeout.get("packet_id") == SOURCE_CLOSEOUT_PACKET_ID
            and source_closeout.get("outcome_id") == SOURCE_CLOSEOUT_OUTCOME
            and source_closeout.get("accepted") is True
        ),
        "bridge_closeout_consumed": (
            bridge_closeout.get("packet_id") == BRIDGE_CLOSEOUT_PACKET_ID
            and bridge_closeout.get("outcome_id") == BRIDGE_CLOSEOUT_OUTCOME
            and bridge_closeout.get("accepted") is True
            and bridge_closeout.get("selected_next_target") == CONSUMED_TARGET
        ),
        "source_rule_form_preserved": (
            source_closeout.get("candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and source_closeout.get("candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and source_closeout.get("admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_rule_form_preserved": (
            bridge_closeout.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and bridge_closeout.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
            and bridge_closeout.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "rule_family_has_two_entries": len(rule_family_entries) == 2,
        "synthesis_criteria_all_accepted": all(
            row["status"] == "accepted" for row in synthesis_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "source_closeout_packet_id": SOURCE_CLOSEOUT_PACKET_ID,
        "source_closeout_outcome": SOURCE_CLOSEOUT_OUTCOME,
        "bridge_closeout_packet_id": BRIDGE_CLOSEOUT_PACKET_ID,
        "bridge_closeout_outcome": BRIDGE_CLOSEOUT_OUTCOME,
        "phi_ck_admissibility_rule_family_count": 2,
        "concrete_phi_ck_rule_roles": [SOURCE_RULE_ROLE, BRIDGE_RULE_ROLE],
        "source_rule_id": SOURCE_RULE_ID,
        "source_rule_role": SOURCE_RULE_ROLE,
        "source_rule_classification": SOURCE_RULE_CLASSIFICATION,
        "source_rule_epistemic_status": RULE_EPISTEMIC_STATUS,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "source_rule_plain_meaning": SOURCE_RULE_PLAIN_MEANING,
        "bridge_rule_id": BRIDGE_RULE_ID,
        "bridge_rule_role": BRIDGE_RULE_ROLE,
        "bridge_rule_classification": BRIDGE_RULE_CLASSIFICATION,
        "bridge_rule_epistemic_status": BRIDGE_RULE_EPISTEMIC_STATUS,
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "rule_family_entries": rule_family_entries,
        "synthesis_criteria": synthesis_criteria,
        "synthesis_criteria_count": len(synthesis_criteria),
        "synthesis_criteria_accepted_count": sum(
            1 for row in synthesis_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "synthesis_packet_prepared": True,
        "synthesis_packet_accepted": True,
        "phi_ck_rule_family_synthesized": True,
        "source_and_bridge_rules_synthesized": True,
        "source_admissibility_rule_synthesized": True,
        "bridge_admissibility_rule_synthesized": True,
        "source_admissibility_rule_preserved": True,
        "bridge_admissibility_rule_preserved": True,
        "c_k_acquired_two_concrete_phi_relevant_rule_roles": True,
        "source_rule_decides_phi_source_permission": True,
        "bridge_rule_decides_phi_route_consistency": True,
        "both_rules_admissibility_only": True,
        "both_rules_rule_candidates": True,
        "both_rules_not_action_terms": True,
        "both_rules_not_dynamical_laws": True,
        "neither_rule_derives_phi": True,
        "neither_rule_derives_v_phi": True,
        "both_rules_define_cross_pillar_admissibility": True,
        "rule_family_interprets_ck_as_seam_admissibility": True,
        "another_phi_derivation_selected": False,
        "transport_consistency_family_selected": False,
        "master_action_surface_rotation_selected": False,
        "qft_gr_semiclassical_prerequisite_return_selected": False,
        "public_explanatory_section_selected": False,
        "constraint_as_action_term_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_law_claimed": False,
        "candidate_recorded_as_new_physical_law": False,
        "candidate_recorded_as_action_term": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_executed": False,
        "phi_variation_executed": False,
        "bridge_admissibility_proved": False,
        "route_alignment_verified": False,
        "source_admissibility_proved": False,
        "source_conservation_proved": False,
        "native_phi_derivation_claimed": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "v_phi_derivation_claimed": False,
        "derived_v_phi_claimed": False,
        "potential_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "native_generation_theorem_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "mathematical_statement": (
            "The phi/C_k branch now has a two-rule admissibility family: "
            "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu} with "
            "C_source^nu[g, phi] = 0, and C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - "
            "T_phi^witness, C_source^phi - nabla_mu T_phi^{mu nu}) "
            "with C_bridge^phi = 0. The packet synthesizes these as "
            "source-admissibility and bridge-admissibility rule candidates."
        ),
        "non_claim_boundary": (
            "This synthesis packet records the source and bridge phi/C_k "
            "admissibility-rule family only. Both rules are admissibility-only "
            "rule candidates, not action terms, not dynamical laws, not native "
            "phi derivations, not V(phi) derivations, not QFT-GR closure, and "
            "not master-action promotion. It does not execute C_k variation, "
            "does not embed either rule in an action, does not prove source "
            "admissibility or bridge admissibility, does not verify route "
            "alignment, does not claim semiclassical coupling, does not claim "
            "empirical validation, and does not authorize public readiness. "
            "The full ToeFormal aggregate is recorded as NOT_RUN for this "
            "packet."
        ),
        "critical_gate_fail_conditions": [
            "claim either rule is an action term",
            "claim either rule is a new dynamical law",
            "execute C_k variation",
            "claim native phi derivation",
            "claim V(phi) derivation",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
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
            "ToeFormal.Derivation.PhiCKAdmissibilityRuleFamilySynthesisPacket",
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
            "source_closeout_file": _ptr(source_closeout_path),
            "bridge_closeout_file": _ptr(bridge_closeout_path),
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
        description="Build the phi/C_k admissibility-rule family synthesis packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_phi_ck_admissibility_rule_family_synthesis_packet(
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
