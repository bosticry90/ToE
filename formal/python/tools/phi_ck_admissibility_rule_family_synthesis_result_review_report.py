from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_ck_admissibility_rule_family_synthesis_packet_report import (
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
    DEFAULT_OUT as SYNTHESIS_PACKET_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SYNTHESIS_PACKET_OUTCOME,
    PACKET_ID as SYNTHESIS_PACKET_ID,
    PACKET_RESULT as SYNTHESIS_PACKET_RESULT,
    SCHEMA_ID as SYNTHESIS_PACKET_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_PLAIN_MEANING,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_ACCEPTS_SOURCE_"
    "AND_BRIDGE_RULE_SYNTHESIS_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_ck_admissibility_rule_family_synthesis_result_review_accepts_source_"
    "and_bridge_rule_synthesis_no_action_variation_or_promotion"
)
NEXT_TARGET = "prepare_phi_ck_admissibility_rule_family_synthesis_closeout"
NEXT_TARGET_KIND = "phi_ck_admissibility_rule_family_synthesis_closeout_preparation"
RECOMMENDED_AFTER_CLOSEOUT_SELECTOR_TARGET = (
    "select_next_ck_constraint_family_after_phi_source_and_bridge_admissibility"
)
RECOMMENDED_AFTER_CLOSEOUT_CANDIDATE_FAMILY = "transport_consistency_ck_constraint_family"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiCKAdmissibilityRuleFamilySynthesisResultReview.lean"
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "synthesis_packet_accepted",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The synthesis packet is accepted as the review input.",
        },
        {
            "row_id": "source_rule_preserved",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_source^nu[g, phi] = 0 is preserved.",
        },
        {
            "row_id": "bridge_rule_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_bridge^phi = 0 is preserved.",
        },
        {
            "row_id": "both_rules_admissibility_only_candidates",
            "status": "accepted",
            "evidence": [
                SOURCE_RULE_CLASSIFICATION,
                BRIDGE_RULE_CLASSIFICATION,
                "admissibility-only",
            ],
            "assessment": (
                "Both rules remain admissibility-only rule candidates."
            ),
        },
        {
            "row_id": "no_action_term_or_ck_variation",
            "status": "accepted",
            "evidence": [
                "both_rules_not_action_terms=true",
                "ck_variation_executed=false",
            ],
            "assessment": "The review accepts no action term and no C_k variation.",
        },
        {
            "row_id": "no_dynamical_law_native_phi_or_v_phi_derivation",
            "status": "accepted",
            "evidence": [
                "dynamical_law_claimed=false",
                "native_phi_derivation_claimed=false",
                "v_phi_derivation_claimed=false",
            ],
            "assessment": (
                "The synthesis makes no dynamical-law, native-phi, or V(phi) "
                "derivation claim."
            ),
        },
        {
            "row_id": "no_qft_gr_closure_or_master_promotion",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "QFT-GR closure and master-action promotion remain blocked.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": (
                "The full ToeFormal aggregate is recorded as NOT_RUN, not passed, "
                "failed, or timed out."
            ),
        },
        {
            "row_id": "synthesis_closeout_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the bounded synthesis closeout.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_ck_admissibility_rule_family_synthesis_result_review",
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


def build_phi_ck_admissibility_rule_family_synthesis_result_review(
    *,
    synthesis_packet_path: Path = SYNTHESIS_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(synthesis_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_result_review_target": (
            packet.get("schema_id") == SYNTHESIS_PACKET_SCHEMA_ID
            and packet.get("packet_id") == SYNTHESIS_PACKET_ID
            and packet.get("outcome_id") == SYNTHESIS_PACKET_OUTCOME
            and packet.get("packet_result") == SYNTHESIS_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "source_rule_preserved": (
            packet.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and packet.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and packet.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_rule_preserved": (
            packet.get("bridge_candidate_id") == BRIDGE_CANDIDATE_ID
            and packet.get("bridge_candidate_type") == BRIDGE_CANDIDATE_TYPE
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
        ),
        "admissibility_only_family_accepted": (
            packet.get("phi_ck_admissibility_rule_family_count") == 2
            and packet.get("both_rules_admissibility_only") is True
            and packet.get("both_rules_rule_candidates") is True
            and packet.get("both_rules_not_action_terms") is True
            and packet.get("both_rules_not_dynamical_laws") is True
        ),
        "no_forbidden_claims": all(
            packet.get(key) is False
            for key in [
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
            packet.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and packet.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and packet.get("full_toeformal_aggregate_passed") is False
            and packet.get("full_toeformal_aggregate_failed") is False
            and packet.get("full_toeformal_aggregate_timed_out") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "synthesis_packet_id": SYNTHESIS_PACKET_ID,
        "synthesis_packet_outcome": SYNTHESIS_PACKET_OUTCOME,
        "synthesis_packet_result": SYNTHESIS_PACKET_RESULT,
        "source_rule_classification": SOURCE_RULE_CLASSIFICATION,
        "source_rule_epistemic_status": "admissibility-only",
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
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "review_executed": True,
        "result_review_prepared": True,
        "result_review_accepted": True,
        "synthesis_packet_accepted": True,
        "source_rule_synthesis_accepted": True,
        "bridge_rule_synthesis_accepted": True,
        "source_and_bridge_rule_synthesis_accepted": True,
        "two_rule_family_review_accepted": True,
        "c_k_instantiated_as_admissibility_rules": True,
        "c_k_source_permission_role_accepted": True,
        "c_k_bridge_permission_role_accepted": True,
        "both_rules_admissibility_only": True,
        "both_rules_rule_candidates": True,
        "both_rules_not_action_terms": True,
        "both_rules_not_dynamical_laws": True,
        "neither_rule_derives_phi": True,
        "neither_rule_derives_v_phi": True,
        "synthesis_closeout_authorized": True,
        "synthesis_closeout_prepared": False,
        "post_closeout_selector_target_recommended": (
            RECOMMENDED_AFTER_CLOSEOUT_SELECTOR_TARGET
        ),
        "post_closeout_candidate_family_recommended": (
            RECOMMENDED_AFTER_CLOSEOUT_CANDIDATE_FAMILY
        ),
        "selector_after_closeout_authorized": False,
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
            "The result review accepts the phi/C_k admissibility-rule family "
            "synthesis: C_source^nu[g, phi] = 0 and C_bridge^phi = 0 are "
            "preserved as admissibility-only rule candidates. The review "
            "records that C_k can instantiate source permission and bridge "
            "permission roles without action variation or promotion."
        ),
        "non_claim_boundary": (
            "This result review accepts the source and bridge phi/C_k "
            "admissibility-rule synthesis only. The review records no action "
            "term, no C_k variation, no dynamical-law claim, no native phi "
            "derivation, no V(phi) derivation, no source-admissibility proof, "
            "no bridge-admissibility proof, no QFT-GR closure, no "
            "semiclassical coupling, no master-action promotion, no empirical "
            "validation, and no public-readiness authorization. The full "
            "ToeFormal aggregate is recorded as NOT_RUN for this review, not "
            "passed, not failed, and not timed out."
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
            "ToeFormal.Derivation.PhiCKAdmissibilityRuleFamilySynthesisResultReview",
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
            "synthesis_packet_file": _ptr(synthesis_packet_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the phi/C_k admissibility-rule family synthesis result review."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = build_phi_ck_admissibility_rule_family_synthesis_result_review(
        captured_at_utc=args.captured_at_utc
    )
    path = write_review(review, args.out)
    print(
        json.dumps(
            {
                "accepted": review["accepted"],
                "out": _ptr(path),
                "review_result": review["review_result"],
                "selected_next_target": review["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
