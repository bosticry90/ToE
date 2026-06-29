from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.A_source_theorem_linkage_obligation_packet_report import (
    BOUNDARY_ITEMS as PACKET_BOUNDARY_ITEMS,
    C_SOURCE_A_SHORT_FORM,
    C_SOURCE_A_TARGET_STATEMENT,
    DEFAULT_OUT as PACKET_PATH,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW as LEAN_STATUS_WORDING_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_ID as PREPARED_PACKET_ID,
    PACKET_SCOPE_RECORD,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
    SCHEMA_ID as PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW as SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    SOURCE_ADMISSIBILITY_CONDITION,
    STANDALONE_A_ROUTE,
    STRICT_PACKET_RESULT,
    WATCH_ITEMS,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_result_review_report import (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW as FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_C_SOURCE_A_"
    "ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_STANDALONE_"
    "A_SECTOR_SOURCE_ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_"
    "PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_obligation_packet_result_review_accepts_"
    "standalone_A_sector_C_source_A_scope"
)

NEXT_TARGET = "prepare_A_source_theorem_linkage_attempt_from_standalone_A_route"
NEXT_TARGET_KIND = "A_source_theorem_linkage_attempt_from_standalone_A_route_preparation"
LIKELY_POST_ATTEMPT_REVIEW_TARGET = (
    "review_A_source_theorem_linkage_attempt_from_standalone_A_route_result"
)
LIKELY_POST_ATTEMPT_REVIEW_KIND = (
    "A_source_theorem_linkage_attempt_from_standalone_A_route_result_review"
)
ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_PREPARED_C_SOURCE_A_"
    "LINKAGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_PREPARED_PRIOR_A_"
    "REGISTRY_SOURCE_ROUTE_NO_SOURCED_MAXWELL_SUBSTITUTION_OR_MASTER_ACTION_"
    "PROMOTION"
)

ACCEPTED_REVIEW_FINDINGS = [
    "A-sector source theorem-linkage obligation packet accepted",
    "C_source^A route scoped from prior standalone A-sector registry",
    "exact frozen A-sector source equation preserved",
    "later psi-A sourced Maxwell route explicitly excluded",
    "assumptions/sign/domain/boundary conventions indexed",
    "no proof execution",
    "no theorem discharge",
    "no C_k rule promotion",
    "no action embedding",
    "no variation",
    "no A-sector closure",
    "no sourced/full Maxwell closure",
    "no empirical validation",
    "no master-action promotion",
]

BLOCKED_CLAIMS = [
    "no theorem discharge during review",
    "no A-sector closure",
    "no sourced Maxwell closure by substitution",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no general C_k closure",
    "no empirical validation",
    "no master-action promotion",
]

STANDALONE_A_ROUTE_ATTEMPT_SKETCH = [
    "C_source^A := nabla_mu T_A^{mu nu}",
    "nabla_mu T_A^{mu nu} = 0",
    "therefore C_source^A = 0 under the prior standalone A-sector route",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageObligationPacketResultReview.lean"
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
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_source_A_discharged": False,
        "A_source_theorem_linkage_obligation_discharged": False,
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


def _packet_valid(packet: dict[str, Any]) -> bool:
    return (
        packet.get("schema_id") == PACKET_SCHEMA_ID
        and packet.get("packet_id") == PREPARED_PACKET_ID
        and packet.get("outcome_id") == PACKET_OUTCOME
        and packet.get("packet_result") == PACKET_OUTCOME
        and packet.get("strict_packet_result") == STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == CONSUMED_TARGET
        and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and packet.get("standalone_A_sector_route") == STANDALONE_A_ROUTE
        and packet.get("source_admissibility_condition")
        == SOURCE_ADMISSIBILITY_CONDITION
        and packet.get("psi_A_sourced_route_substituted") is False
        and packet.get("do_not_silently_substitute_psi_A_sourced_Maxwell_route")
        is True
        and packet.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "A_source_theorem_linkage_obligation_packet_result_review",
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


def build_A_source_theorem_linkage_obligation_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    acceptance_criteria = {
        "consumes_expected_packet_result": _packet_valid(packet),
        "A_source_packet_accepted": packet.get("accepted") is True,
        "standalone_A_sector_C_source_route_preserved": (
            packet.get("standalone_A_sector_route") == STANDALONE_A_ROUTE
            and packet.get("C_source_A_short_form") == C_SOURCE_A_SHORT_FORM
            and packet.get("source_admissibility_condition")
            == SOURCE_ADMISSIBILITY_CONDITION
        ),
        "exact_frozen_A_sector_source_equation_preserved": (
            packet.get("accepted_A_sector_source_equation_to_freeze")
            == "nabla_mu T_A^{mu nu} = 0"
        ),
        "psi_A_sourced_Maxwell_route_excluded": (
            packet.get("psi_A_sourced_maxwell_route") == PSI_A_SOURCED_MAXWELL_ROUTE
            and packet.get("psi_A_sourced_route_substituted") is False
            and "do not silently substitute" in PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD
        ),
        "assumptions_sign_domain_boundary_conventions_indexed": (
            packet.get("watch_items") == WATCH_ITEMS
            and packet.get("packet_scope_record") == PACKET_SCOPE_RECORD
        ),
        "review_only_no_theorem_execution": True,
        "blocked_claims_preserved": PACKET_BOUNDARY_ITEMS[:4]
        == [
            "no proof execution",
            "no theorem discharge",
            "no A-sector closure",
            "no sourced Maxwell closure",
        ],
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_post_attempt_review_target": LIKELY_POST_ATTEMPT_REVIEW_TARGET,
        "likely_post_attempt_review_kind": LIKELY_POST_ATTEMPT_REVIEW_KIND,
        "attempt_preparation_recommended_outcome": (
            ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
        ),
        "strict_attempt_preparation_recommended_outcome": (
            STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
        ),
        "standalone_A_route_attempt_sketch": STANDALONE_A_ROUTE_ATTEMPT_SKETCH,
        "prepared_packet_schema_id": PACKET_SCHEMA_ID,
        "prepared_packet_id": PREPARED_PACKET_ID,
        "prepared_packet_outcome": PACKET_OUTCOME,
        "prepared_packet_result": PACKET_OUTCOME,
        "prepared_packet_strict_result": STRICT_PACKET_RESULT,
        "prepared_packet_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "selected_obligation": "C_source^A theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^A theorem-linkage gap",
        "selected_obligation_row_id": "C_source^A",
        "standalone_A_sector_route": STANDALONE_A_ROUTE,
        "standalone_A_sector_route_preserved": accepted,
        "C_source_A_short_form": C_SOURCE_A_SHORT_FORM,
        "C_source_A_target_statement": C_SOURCE_A_TARGET_STATEMENT,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "accepted_A_sector_source_equation_to_freeze": (
            SOURCE_ADMISSIBILITY_CONDITION
        ),
        "psi_A_sourced_maxwell_route": PSI_A_SOURCED_MAXWELL_ROUTE,
        "psi_A_sourced_route_substituted": False,
        "do_not_silently_substitute_psi_A_sourced_Maxwell_route": True,
        "route_contamination_guard": PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the standalone A-sector C_source^A "
            "theorem-linkage obligation packet scope. It preserves the exact "
            "frozen A-sector source equation nabla_mu T_A^{mu nu} = 0 from the "
            "prior standalone A-sector registry and explicitly excludes the "
            "later psi-A sourced Maxwell route nabla_mu F^{mu alpha} = J^alpha. "
            "It does not execute a proof, discharge C_source^A, promote any C_k "
            "rule, embed C_k in an action, vary C_k, claim A-sector closure, "
            "close sourced or full Maxwell, close EM-QFT, close QFT-GR, close "
            "GR-QM, claim general C_k closure, claim empirical validation, or "
            "promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_A_source_theorem_linkage_obligation_packet_result",
            "fail to accept the A-source packet scope",
            "fail to preserve the standalone A-sector C_source^A route",
            "silently substitute nabla_mu F^{mu alpha} = J^alpha",
            "execute proof during review",
            "discharge C_source^A during review",
            "promote any C_k rule",
            "claim A-sector closure",
            "claim sourced Maxwell closure",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
            "claim seam closure",
            "claim empirical validation",
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
            "ToeFormal.Derivation.ASourceTheoremLinkageObligationPacketResultReview",
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
            "Review the standalone A-source C_source^A theorem-linkage obligation "
            "packet without executing the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_A_source_theorem_linkage_obligation_packet_result_review(
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
                "source_admissibility_condition": payload[
                    "source_admissibility_condition"
                ],
                "psi_A_sourced_route_substituted": payload[
                    "psi_A_sourced_route_substituted"
                ],
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
