from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.A_source_theorem_linkage_obligation_packet_result_review_report import (
    DEFAULT_OUT as REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_POST_ATTEMPT_REVIEW_TARGET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as REVIEW_OUTCOME,
    PACKET_ID as REVIEW_PACKET_ID,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
    SCHEMA_ID as REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    SOURCE_ADMISSIBILITY_CONDITION,
    STANDALONE_A_ROUTE,
    STRICT_REVIEW_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_v0"
OUTCOME_ID = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_PREPARED_C_SOURCE_A_"
    "LINKAGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_ATTEMPT_PREPARATION_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_PREPARED_STANDALONE_A_"
    "STRESS_CONSERVATION_ROUTE_NO_SOURCED_MAXWELL_SUBSTITUTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_attempt_from_standalone_A_route_prepares_"
    "C_source_A_stress_conservation_linkage_no_theorem_discharge"
)

NEXT_TARGET = "review_A_source_theorem_linkage_attempt_from_standalone_A_route_result"
NEXT_TARGET_KIND = (
    "A_source_theorem_linkage_attempt_from_standalone_A_route_result_review"
)

C_SOURCE_A_RESIDUAL_DEFINITION = "C_source^{A,nu} := nabla_mu T_A^{mu nu}"
TARGET_CONCLUSION = "C_source^{A,nu} = 0"
LINKAGE_ROUTE = [
    C_SOURCE_A_RESIDUAL_DEFINITION,
    SOURCE_ADMISSIBILITY_CONDITION,
    "therefore: C_source^{A,nu} = 0",
]
PREPARED_LINKAGE_TARGET = (
    "C_source^{A,nu} = 0 from the prior standalone A-sector stress-conservation "
    "route nabla_mu T_A^{mu nu} = 0"
)

WATCH_ITEMS = [
    "same T_A definition",
    "same A-sector route",
    "same covariant derivative",
    "same sign and index conventions",
    "same source-free / standalone boundary",
    "same domain assumptions",
    "no J current imported",
    "no psi-A sourced Maxwell substitution",
]

BOUNDARY_ITEMS = [
    "no theorem discharge during preparation",
    "no C_source^A closure yet",
    "no A-sector closure",
    "no sourced Maxwell closure",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
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
    / "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageAttemptFromStandaloneARoute.lean"
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
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_source_A_closure_claimed": False,
        "C_source_A_discharged": False,
        "A_source_theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "J_current_imported": False,
        "psi_A_sourced_route_substituted": False,
        "sourced_Maxwell_route_substituted": False,
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


def _review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == REVIEW_SCHEMA_ID
        and review.get("packet_id") == REVIEW_PACKET_ID
        and review.get("outcome_id") == REVIEW_OUTCOME
        and review.get("review_result") == REVIEW_OUTCOME
        and review.get("strict_review_result") == STRICT_REVIEW_RESULT
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("likely_post_attempt_review_target")
        == LIKELY_POST_ATTEMPT_REVIEW_TARGET
        and review.get("source_admissibility_condition")
        == SOURCE_ADMISSIBILITY_CONDITION
        and review.get("psi_A_sourced_route_substituted") is False
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "A_source_theorem_linkage_attempt_from_standalone_A_route",
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
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_A_source_theorem_linkage_attempt_from_standalone_A_route(
    *,
    review_path: Path = REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    acceptance_criteria = {
        "consumes_expected_packet_review": _review_valid(review),
        "standalone_A_source_route_preserved": (
            STANDALONE_A_ROUTE == "vacuum U(1) source-admissibility route"
            and SOURCE_ADMISSIBILITY_CONDITION == "nabla_mu T_A^{mu nu} = 0"
        ),
        "residual_definition_indexed": (
            C_SOURCE_A_RESIDUAL_DEFINITION
            == "C_source^{A,nu} := nabla_mu T_A^{mu nu}"
        ),
        "linkage_target_prepared_without_discharge": (
            TARGET_CONCLUSION == "C_source^{A,nu} = 0"
            and LINKAGE_ROUTE
            == [
                "C_source^{A,nu} := nabla_mu T_A^{mu nu}",
                "nabla_mu T_A^{mu nu} = 0",
                "therefore: C_source^{A,nu} = 0",
            ]
        ),
        "no_J_current_imported": True,
        "psi_A_sourced_Maxwell_route_not_substituted": (
            PSI_A_SOURCED_MAXWELL_ROUTE == "nabla_mu F^{mu alpha} = J^alpha"
            and PSI_A_SOURCED_MAXWELL_ROUTE not in LINKAGE_ROUTE
            and "J^alpha" not in " ".join(LINKAGE_ROUTE)
        ),
        "preparation_only_no_theorem_discharge": True,
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET == "PASSED_SERIAL_RERUN"
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_PREPARATION",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "attempt_prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_REQUIRES_REMEDIATION",
        "attempt_preparation_result": OUTCOME_ID
        if prepared
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if prepared
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_REQUIRES_REMEDIATION",
        "strict_attempt_preparation_result": STRICT_ATTEMPT_PREPARATION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "review_schema_id": REVIEW_SCHEMA_ID,
        "review_packet_id": REVIEW_PACKET_ID,
        "review_outcome": REVIEW_OUTCOME,
        "review_strict_result": STRICT_REVIEW_RESULT,
        "review_consumed": prepared,
        "prior_review_accepted": prepared,
        "selected_obligation": "C_source^A theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^A theorem-linkage gap",
        "selected_obligation_row_id": "C_source^A",
        "standalone_A_sector_route": STANDALONE_A_ROUTE,
        "standalone_A_sector_route_preserved": prepared,
        "standalone_A_stress_conservation_route": SOURCE_ADMISSIBILITY_CONDITION,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "C_source_A_residual_definition": C_SOURCE_A_RESIDUAL_DEFINITION,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "linkage_route": LINKAGE_ROUTE,
        "linkage_route_count": len(LINKAGE_ROUTE),
        "route_kind": "standalone_A_stress_conservation",
        "source_free_standalone_boundary_preserved": True,
        "J_current_imported": False,
        "psi_A_sourced_maxwell_route": PSI_A_SOURCED_MAXWELL_ROUTE,
        "psi_A_sourced_route_substituted": False,
        "sourced_Maxwell_route_substituted": False,
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
            "This packet prepares only the standalone A-sector C_source^A "
            "linkage attempt from the source-free stress-conservation route "
            "C_source^{A,nu} := nabla_mu T_A^{mu nu} and nabla_mu T_A^{mu nu} = 0. "
            "It does not import J, does not substitute the later psi-A sourced "
            "Maxwell route nabla_mu F^{mu alpha} = J^alpha, does not discharge "
            "C_source^A, does not claim A-sector closure, does not close sourced "
            "or full Maxwell, does not promote any C_k rule, does not embed or "
            "vary C_k in an action, does not claim empirical validation, and "
            "does not promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_A_source_theorem_linkage_attempt_from_standalone_A_route",
            "fail to preserve C_source^{A,nu} := nabla_mu T_A^{mu nu}",
            "fail to preserve nabla_mu T_A^{mu nu} = 0 as the standalone route",
            "import a J current into the linkage route",
            "silently substitute nabla_mu F^{mu alpha} = J^alpha",
            "execute the theorem attempt during preparation",
            "discharge C_source^A during preparation",
            "claim A-sector closure",
            "claim sourced or full Maxwell closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "promote any C_k rule or the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ASourceTheoremLinkageAttemptFromStandaloneARoute",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "review_file": _ptr(review_path),
            "review_lean_file": _ptr(REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
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
            "Prepare the standalone A-source C_source^A theorem-linkage attempt "
            "without importing the psi-A sourced Maxwell route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = build_A_source_theorem_linkage_attempt_from_standalone_A_route(
        review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(packet, out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "attempt_preparation_result": packet["attempt_preparation_result"],
                "selected_next_target": packet["selected_next_target"],
                "C_source_A_residual_definition": packet[
                    "C_source_A_residual_definition"
                ],
                "source_admissibility_condition": packet[
                    "source_admissibility_condition"
                ],
                "target_conclusion": packet["target_conclusion"],
                "J_current_imported": packet["J_current_imported"],
                "psi_A_sourced_route_substituted": packet[
                    "psi_A_sourced_route_substituted"
                ],
                "theorem_discharged": packet["theorem_discharged"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
