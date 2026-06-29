from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_result_review_report import (
    DEFAULT_OUT as SELECTOR_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH as SELECTOR_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LIKELY_POST_PACKET_REVIEW_TARGET,
    NEXT_PACKET_RECOVERY_ITEMS,
    NEXT_PACKET_SCOPE_INSTRUCTION,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SELECTOR_REVIEW_OUTCOME,
    PACKET_ID as SELECTOR_REVIEW_PACKET_ID,
    SCHEMA_ID as SELECTOR_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_ROW_ID,
    SELECTED_THEOREM_LINKAGE_GAP,
    STRICT_REVIEW_RESULT as SELECTOR_STRICT_REVIEW_RESULT,
)
from formal.python.tools.toe_native_a_route_selection_after_vacuum_source_admissibility_report import (
    A_FIELD_DOMAIN_POLICY,
    A_SOURCE_CK_RULE_CANDIDATE,
    A_SOURCE_CK_RULE_SHORT_FORM,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CURRENT_COUPLED_SCOPE_BOUNDARY,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LOCAL_SOURCE_ROUTE_SCOPE,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    ON_SHELL_VACUUM_CONSERVATION_ROUTE,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_v0"
OUTCOME_ID = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_C_SOURCE_A_ROUTE_"
    "SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_PACKET_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_A_SECTOR_SOURCE_"
    "ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_PROMOTION"
)
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_obligation_packet_scopes_standalone_C_source_A_"
    "route_no_proof_execution_or_C_k_rule_promotion"
)

NEXT_TARGET = "review_A_source_theorem_linkage_obligation_packet_result"
NEXT_TARGET_KIND = "A_source_theorem_linkage_obligation_packet_result_review"

C_SOURCE_A_CONSTRAINT_CANDIDATE = A_SOURCE_CK_RULE_CANDIDATE
C_SOURCE_A_SHORT_FORM = A_SOURCE_CK_RULE_SHORT_FORM
C_SOURCE_A_TARGET_STATEMENT = (
    "C_source^A = 0 linked to nabla_mu T_A^{mu nu} = 0 under the prior "
    "A-sector vacuum source-admissibility route"
)
STANDALONE_A_ROUTE = "vacuum U(1) source-admissibility route"
PSI_A_SOURCED_MAXWELL_ROUTE = "nabla_mu F^{mu alpha} = J^alpha"
PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD = (
    "recover exact C_source^A statement from prior A-sector registry; do not "
    "silently substitute the psi-A sourced Maxwell route"
)

PACKET_SCOPE_RECORD = [
    "selected obligation: C_source^A theorem-linkage obligation",
    "prior selector accepted",
    "A-sector source admissibility route to be recovered from prior A-sector registry",
    "exact source equation to be frozen from existing A-sector source packet",
    "assumptions/sign/domain/boundary conventions to be indexed",
    "no proof execution",
    "no theorem discharge",
]

WATCH_ITEMS = [
    "same standalone A-sector field object A",
    "same field strength F",
    "same A-sector source admissibility condition C_source^A",
    "same prior A-sector source route assumptions",
    "same vacuum/source-free A-sector equation from the registry",
    "same stress-energy divergence identity",
    "same sign convention",
    "same index placement",
    "same covariant derivative convention",
    "same domain and boundary assumptions",
    "do not substitute psi-A sourced Maxwell route",
]

BOUNDARY_ITEMS = [
    "no proof execution",
    "no theorem discharge",
    "no A-sector closure",
    "no sourced Maxwell closure",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no general C_k closure",
    "no C_k dynamical-law status",
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
    / "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageObligationPacket.lean"
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
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_source_A_discharged": False,
        "A_source_theorem_linkage_obligation_discharged": False,
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
    }


def _selector_review_valid(selector_review: dict[str, Any]) -> bool:
    return (
        selector_review.get("schema_id") == SELECTOR_REVIEW_SCHEMA_ID
        and selector_review.get("packet_id") == SELECTOR_REVIEW_PACKET_ID
        and selector_review.get("outcome_id") == SELECTOR_REVIEW_OUTCOME
        and selector_review.get("review_result") == SELECTOR_REVIEW_OUTCOME
        and selector_review.get("strict_review_result")
        == SELECTOR_STRICT_REVIEW_RESULT
        and selector_review.get("selected_next_target") == CONSUMED_TARGET
        and selector_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and selector_review.get("likely_post_packet_review_target")
        == LIKELY_POST_PACKET_REVIEW_TARGET
        and selector_review.get("selected_obligation") == SELECTED_OBLIGATION
        and selector_review.get("selected_theorem_linkage_gap")
        == SELECTED_THEOREM_LINKAGE_GAP
        and selector_review.get("selected_obligation_row_id")
        == SELECTED_OBLIGATION_ROW_ID
        and selector_review.get("accepted") is True
    )


def _prior_A_registry_snapshot() -> dict[str, Any]:
    return {
        "route_kind": STANDALONE_A_ROUTE,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "C_source_A_constraint_candidate": C_SOURCE_A_CONSTRAINT_CANDIDATE,
        "C_source_A_short_form": C_SOURCE_A_SHORT_FORM,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "accepted_source_equation_to_freeze": SOURCE_ADMISSIBILITY_CONDITION,
        "stress_energy_divergence_route": DIVERGENCE_IDENTITY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "on_shell_vacuum_conservation_identity": (
            ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "current_coupled_scope_boundary": CURRENT_COUPLED_SCOPE_BOUNDARY,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "A_source_theorem_linkage_obligation_packet",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_A_source_theorem_linkage_obligation_packet(
    *,
    selector_review_path: Path = SELECTOR_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector_review = _read_json(selector_review_path)
    prior_A_registry = _prior_A_registry_snapshot()
    acceptance_criteria = {
        "consumes_expected_selector_review": _selector_review_valid(selector_review),
        "selected_obligation_preserved": (
            SELECTED_OBLIGATION == "C_source^A theorem-linkage obligation"
            and SELECTED_THEOREM_LINKAGE_GAP == "C_source^A theorem-linkage gap"
            and SELECTED_OBLIGATION_ROW_ID == "C_source^A"
        ),
        "standalone_A_source_route_recovered": (
            prior_A_registry["source_admissibility_condition"]
            == "nabla_mu T_A^{mu nu} = 0"
            and prior_A_registry["C_source_A_short_form"]
            == "C_source^A := nabla_mu T_A^{mu nu}; C_source^A = 0"
            and prior_A_registry["stress_energy_divergence_route"]
            == "nabla_mu T_A^{mu nu} = - F^{nu}{}_{alpha} nabla_mu F^{mu alpha}"
            and prior_A_registry["vacuum_euler_lagrange_route"]
            == "nabla_mu F^{mu nu} = 0"
        ),
        "psi_A_sourced_route_not_substituted": (
            PSI_A_SOURCED_MAXWELL_ROUTE == "nabla_mu F^{mu alpha} = J^alpha"
            and SOURCE_ADMISSIBILITY_CONDITION != PSI_A_SOURCED_MAXWELL_ROUTE
            and "do not silently substitute" in PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD
        ),
        "scope_only_no_theorem_execution": True,
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW == "PASSED_SERIAL_RERUN"
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARATION",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if prepared
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "strict_packet_result": STRICT_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "selector_review_schema_id": SELECTOR_REVIEW_SCHEMA_ID,
        "selector_review_packet_id": SELECTOR_REVIEW_PACKET_ID,
        "selector_review_outcome": SELECTOR_REVIEW_OUTCOME,
        "selector_strict_review_result": SELECTOR_STRICT_REVIEW_RESULT,
        "selector_review_consumed": prepared,
        "prior_selector_accepted": prepared,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_theorem_linkage_gap": SELECTED_THEOREM_LINKAGE_GAP,
        "selected_obligation_row_id": SELECTED_OBLIGATION_ROW_ID,
        "C_source_A_theorem_linkage_obligation_selected": prepared,
        "packet_scope_record": PACKET_SCOPE_RECORD,
        "packet_scope_record_count": len(PACKET_SCOPE_RECORD),
        "scope_only": True,
        "proof_execution_blocked": True,
        "theorem_discharge_blocked": True,
        "A_sector_source_admissibility_route_to_be_recovered_from_prior_A_sector_registry": True,
        "exact_source_equation_to_be_frozen_from_existing_A_sector_source_packet": True,
        "assumptions_sign_domain_boundary_conventions_to_be_indexed": True,
        "prior_A_sector_registry": prior_A_registry,
        "standalone_A_sector_route": STANDALONE_A_ROUTE,
        "standalone_A_sector_route_preserved": prepared,
        "C_source_A_constraint_candidate": C_SOURCE_A_CONSTRAINT_CANDIDATE,
        "C_source_A_short_form": C_SOURCE_A_SHORT_FORM,
        "C_source_A_target_statement": C_SOURCE_A_TARGET_STATEMENT,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "accepted_A_sector_source_equation_to_freeze": SOURCE_ADMISSIBILITY_CONDITION,
        "stress_energy_divergence_route": DIVERGENCE_IDENTITY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "on_shell_vacuum_conservation_identity": (
            ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "current_coupled_scope_boundary": CURRENT_COUPLED_SCOPE_BOUNDARY,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "psi_A_sourced_maxwell_route": PSI_A_SOURCED_MAXWELL_ROUTE,
        "psi_A_sourced_route_substituted": False,
        "do_not_silently_substitute_psi_A_sourced_Maxwell_route": True,
        "route_contamination_guard": PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This packet scopes only the standalone A-sector C_source^A "
            "theorem-linkage obligation. It recovers the exact vacuum A-sector "
            "source-admissibility route from the prior A-sector registry and "
            "does not silently substitute the later psi-A sourced Maxwell route "
            "nabla_mu F^{mu alpha} = J^alpha. It does not execute a proof, "
            "discharge C_source^A, claim A-sector closure, close sourced or "
            "full Maxwell, close EM-QFT, close QFT-GR, close GR-QM, claim "
            "general C_k closure, embed C_k in an action, vary C_k, claim "
            "empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_A_source_theorem_linkage_obligation_packet",
            "fail to recover the standalone A-sector source registry route",
            "silently substitute nabla_mu F^{mu alpha} = J^alpha",
            "execute the C_source^A proof route",
            "discharge C_source^A",
            "claim A-sector closure",
            "claim sourced Maxwell closure",
            "claim full Maxwell closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim general C_k closure",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ASourceTheoremLinkageObligationPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selector_review_file": _ptr(selector_review_path),
            "selector_review_lean_file": _ptr(SELECTOR_REVIEW_LEAN_PACKET_PATH),
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
            "Prepare the standalone A-source C_source^A theorem-linkage "
            "obligation packet without executing the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selector-review", type=Path, default=SELECTOR_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selector_review_path = (
        args.selector_review
        if args.selector_review.is_absolute()
        else REPO_ROOT / args.selector_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = build_A_source_theorem_linkage_obligation_packet(
        selector_review_path=selector_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(packet, out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "packet_result": packet["packet_result"],
                "selected_obligation": packet["selected_obligation"],
                "selected_next_target": packet["selected_next_target"],
                "source_admissibility_condition": packet[
                    "source_admissibility_condition"
                ],
                "psi_A_sourced_route_substituted": packet[
                    "psi_A_sourced_route_substituted"
                ],
                "proof_attempt_executed": packet["proof_attempt_executed"],
                "theorem_discharged": packet["theorem_discharged"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
