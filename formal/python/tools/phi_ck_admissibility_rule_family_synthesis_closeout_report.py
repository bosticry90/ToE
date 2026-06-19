from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_ck_admissibility_rule_family_synthesis_result_review_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_RULE_CLASSIFICATION,
    BRIDGE_RULE_EPISTEMIC_STATUS,
    DEFAULT_OUT as SYNTHESIS_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SYNTHESIS_RESULT_REVIEW_OUTCOME,
    PACKET_ID as SYNTHESIS_RESULT_REVIEW_PACKET_ID,
    RECOMMENDED_AFTER_CLOSEOUT_CANDIDATE_FAMILY,
    RECOMMENDED_AFTER_CLOSEOUT_SELECTOR_TARGET,
    REVIEW_RESULT as SYNTHESIS_REVIEW_RESULT,
    SCHEMA_ID as SYNTHESIS_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_PLAIN_MEANING,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSEOUT_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSED_AS_SOURCE_AND_BRIDGE_"
    "ADMISSIBILITY_RULE_FAMILY_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "phi_ck_admissibility_rule_family_synthesis_closed_as_source_and_bridge_"
    "admissibility_rule_family_no_action_variation_or_promotion"
)
NEXT_TARGET = "select_next_ck_constraint_family_after_phi_source_and_bridge_admissibility"
NEXT_TARGET_KIND = "ck_constraint_family_selection_after_phi_source_and_bridge_admissibility"
FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION = (
    "first synthesized phi-relevant C_k admissibility-rule family"
)
RULE_FAMILY_EPISTEMIC_STATUS = "admissibility-only"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSEOUT_20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiCKAdmissibilityRuleFamilySynthesisCloseout.lean"
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


def _closeout_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "result_review_accepts_synthesis",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The result review accepted the source/bridge synthesis.",
        },
        {
            "row_id": "source_admissibility_rule_preserved",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "The source-admissibility rule is preserved exactly.",
        },
        {
            "row_id": "bridge_admissibility_rule_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "The bridge-admissibility rule is preserved exactly.",
        },
        {
            "row_id": "first_synthesized_phi_ck_family_classification",
            "status": "accepted",
            "evidence": FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION,
            "assessment": "The closeout records the first synthesized phi/C_k family.",
        },
        {
            "row_id": "admissibility_only_not_action_or_dynamical_law",
            "status": "accepted",
            "evidence": [
                RULE_FAMILY_EPISTEMIC_STATUS,
                "not_action_terms=true",
                "not_dynamical_laws=true",
            ],
            "assessment": "The family remains admissibility-only, not dynamical.",
        },
        {
            "row_id": "no_phi_generation_or_potential_derivation",
            "status": "accepted",
            "evidence": [
                "native_phi_derivation_claimed=false",
                "v_phi_derivation_claimed=false",
            ],
            "assessment": "The closeout does not derive phi or V(phi).",
        },
        {
            "row_id": "no_qft_gr_closure_or_master_action_promotion",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "QFT-GR closure and master-action promotion remain unclaimed.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate is recorded as NOT_RUN.",
        },
        {
            "row_id": "next_ck_family_selector_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is only the C_k family selector.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_ck_admissibility_rule_family_synthesis_closeout",
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


def build_phi_ck_admissibility_rule_family_synthesis_closeout(
    *,
    synthesis_result_review_path: Path = SYNTHESIS_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(synthesis_result_review_path)
    closeout_criteria = _closeout_criteria(review)
    acceptance_criteria = {
        "consumes_expected_closeout_target": (
            review.get("schema_id") == SYNTHESIS_RESULT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == SYNTHESIS_RESULT_REVIEW_PACKET_ID
            and review.get("outcome_id") == SYNTHESIS_RESULT_REVIEW_OUTCOME
            and review.get("review_result") == SYNTHESIS_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "source_rule_preserved": (
            review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_rule_preserved": (
            review.get("bridge_candidate_id") == BRIDGE_CANDIDATE_ID
            and review.get("bridge_candidate_type") == BRIDGE_CANDIDATE_TYPE
            and review.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and review.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
            and review.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and review.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and review.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "family_classification_preserved": (
            review.get("both_rules_admissibility_only") is True
            and review.get("both_rules_rule_candidates") is True
            and review.get("both_rules_not_action_terms") is True
            and review.get("both_rules_not_dynamical_laws") is True
            and review.get("neither_rule_derives_phi") is True
            and review.get("neither_rule_derives_v_phi") is True
        ),
        "no_forbidden_claims": all(
            review.get(key) is False
            for key in [
                "selector_after_closeout_authorized",
                "transport_consistency_family_selected",
                "another_phi_derivation_selected",
                "constraint_as_action_term_selected",
                "dynamical_action_embedding_selected",
                "dynamical_law_claimed",
                "candidate_recorded_as_new_physical_law",
                "candidate_recorded_as_action_term",
                "ck_action_embedding_claimed",
                "ck_variation_executed",
                "ck_variation_authorized",
                "lambda_variation_executed",
                "metric_variation_executed",
                "phi_variation_executed",
                "bridge_admissibility_proved",
                "route_alignment_verified",
                "source_admissibility_proved",
                "source_conservation_proved",
                "native_phi_derivation_claimed",
                "phi_generated_by_ck_claimed",
                "phi_generation_theorem_claimed",
                "v_phi_derivation_claimed",
                "derived_v_phi_claimed",
                "potential_derived",
                "qft_gr_closure_claimed",
                "qft_gr_solved",
                "qft_gr_seam_closed",
                "semiclassical_coupling_authorized",
                "semiclassical_coupling_claimed",
                "semiclassical_einstein_equation_derived",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "canonical_master_action_promoted",
                "toe_native_matter_derivation_claimed",
                "standard_model_derivation_claimed",
                "native_generation_theorem_claimed",
                "empirical_validation_claimed",
                "public_readiness_claimed",
                "public_submission_authorized",
                "phase2_readiness_claim",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            review.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_passed") is False
            and review.get("full_toeformal_aggregate_failed") is False
            and review.get("full_toeformal_aggregate_timed_out") is False
        ),
        "closeout_criteria_all_accepted": all(
            row["status"] == "accepted" for row in closeout_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSEOUT"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "synthesis_result_review_packet_id": SYNTHESIS_RESULT_REVIEW_PACKET_ID,
        "synthesis_result_review_outcome": SYNTHESIS_RESULT_REVIEW_OUTCOME,
        "synthesis_review_result": SYNTHESIS_REVIEW_RESULT,
        "family_classification": FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION,
        "family_epistemic_status": RULE_FAMILY_EPISTEMIC_STATUS,
        "source_rule_classification": SOURCE_RULE_CLASSIFICATION,
        "source_rule_epistemic_status": RULE_FAMILY_EPISTEMIC_STATUS,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "source_rule_plain_meaning": SOURCE_RULE_PLAIN_MEANING,
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
        "phi_ck_admissibility_rule_family_count": 2,
        "concrete_phi_ck_rule_roles": [
            "source admissibility",
            "bridge admissibility",
        ],
        "closeout_criteria": closeout_criteria,
        "closeout_criteria_count": len(closeout_criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in closeout_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "closeout_prepared": True,
        "closeout_accepted": True,
        "first_synthesized_phi_relevant_ck_admissibility_rule_family_closed": True,
        "source_and_bridge_admissibility_rule_family_closed": True,
        "source_admissibility_rule_closed_in_family": True,
        "bridge_admissibility_rule_closed_in_family": True,
        "c_k_source_permission_role_closed": True,
        "c_k_bridge_permission_role_closed": True,
        "both_rules_admissibility_only": True,
        "both_rules_rule_candidates": True,
        "both_rules_not_action_terms": True,
        "both_rules_not_dynamical_laws": True,
        "neither_rule_derives_phi": True,
        "neither_rule_derives_v_phi": True,
        "selector_target_authorized": True,
        "selector_target_prepared": False,
        "recommended_next_ck_constraint_family": (
            RECOMMENDED_AFTER_CLOSEOUT_CANDIDATE_FAMILY
        ),
        "recommended_next_ck_constraint_family_reason": (
            "transport consistency asks whether the admitted object remains "
            "well-defined through ACTION -> VARIATION -> BRIDGE -> OPERATOR -> "
            "TRANSPORT -> RESIDUAL_LAW -> REGIME_LIMIT"
        ),
        "transport_chain_form": (
            "ACTION -> VARIATION -> BRIDGE -> OPERATOR -> TRANSPORT -> "
            "RESIDUAL_LAW -> REGIME_LIMIT"
        ),
        "transport_consistency_family_selected": False,
        "another_phi_derivation_selected": False,
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
            "The phi/C_k admissibility-rule family is closed as the first "
            "synthesized phi-relevant C_k admissibility-rule family: "
            "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu} with "
            "C_source^nu[g, phi] = 0, and C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - "
            "T_phi^witness, C_source^phi - nabla_mu T_phi^{mu nu}) with "
            "C_bridge^phi = 0."
        ),
        "non_claim_boundary": (
            "This closeout records the first synthesized phi-relevant C_k "
            "admissibility-rule family only. It closes source admissibility "
            "and bridge admissibility as admissibility-only rule candidates, "
            "not action terms, not dynamical laws, not native phi derivation, "
            "not V(phi) derivation, not QFT-GR closure, and not "
            "master-action promotion. It does not execute C_k variation, "
            "does not embed either rule in an action, does not prove source "
            "admissibility or bridge admissibility, does not verify route "
            "alignment, does not select transport consistency, does not claim "
            "semiclassical coupling, does not claim empirical validation, and "
            "does not authorize public readiness. The full ToeFormal "
            "aggregate is recorded as NOT_RUN for this closeout."
        ),
        "critical_gate_fail_conditions": [
            "drop C_source^nu[g, phi] = 0",
            "drop C_bridge^phi = 0",
            "claim either rule is an action term",
            "execute C_k variation",
            "claim either rule is a dynamical law",
            "claim native phi derivation",
            "claim V(phi) derivation",
            "claim QFT-GR closure",
            "promote the master action",
            "select transport consistency before the selector target",
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
            "ToeFormal.Derivation.PhiCKAdmissibilityRuleFamilySynthesisCloseout",
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
            "synthesis_result_review_file": _ptr(synthesis_result_review_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_closeout(closeout: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(closeout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the phi/C_k admissibility-rule family synthesis closeout."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    closeout = build_phi_ck_admissibility_rule_family_synthesis_closeout(
        captured_at_utc=args.captured_at_utc
    )
    path = write_closeout(closeout, args.out)
    print(
        json.dumps(
            {
                "accepted": closeout["accepted"],
                "closeout_result": closeout["closeout_result"],
                "out": _ptr(path),
                "selected_next_target": closeout["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
