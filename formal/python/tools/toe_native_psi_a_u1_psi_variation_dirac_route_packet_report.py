from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_current_conservation_obligation_packet_report import (
    ACTION_BLOCK_STATEMENT,
    ADJOINT_DIRAC_ROUTE_OBLIGATION,
    A_VARIATION_RESIDUAL,
    BOUNDED_ROUTE_SHAPE,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_CANDIDATE_POLICY,
    CURRENT_CONSERVATION_QUESTION,
    DEFAULT_OUT as CURRENT_CONSERVATION_OBLIGATION_PATH,
    DIRAC_ROUTE_EQUATION,
    FIELD_EQUATION_ROUTE_PREVIEW,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CURRENT_CONSERVATION_OBLIGATION_OUTCOME,
    PACKET_ID as CURRENT_CONSERVATION_OBLIGATION_PACKET_ID,
    PACKET_RESULT as CURRENT_CONSERVATION_OBLIGATION_RESULT,
    SCHEMA_ID as CURRENT_CONSERVATION_OBLIGATION_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW,
    TARGET_CONSERVATION_LAW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET_v0"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET_PREPARED_"
    "PSI_EQUATION_ROUTE_RECORDED_ADJOINT_AND_CONSERVATION_STILL_BLOCKED"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_psi_variation_dirac_route_packet_prepared_"
    "psi_equation_route_recorded_adjoint_and_conservation_still_blocked"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_adjoint_dirac_route_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_adjoint_dirac_route_packet_preparation"
FOLLOW_ON_CURRENT_CONSERVATION_TARGET = (
    "prepare_toe_native_psi_A_u1_current_conservation_from_dirac_pair_packet"
)

PRIMARY_VARIATION_VARIABLE = "psibar"
PSIBAR_VARIATION_ROUTE = (
    "delta_{psibar} S_{psi A} -> (i gamma^mu D_mu - m) psi = 0"
)
PSI_EQUATION_ROUTE = DIRAC_ROUTE_EQUATION
PSI_EQUATION_ROUTE_STATUS = (
    "bounded psi equation route recorded from psibar variation; no adjoint route "
    "or current conservation proof"
)
ADJOINT_ROUTE_PREVIEW = "delta_psi S_{psi A} -> adjoint Dirac equation route"
CURRENT_CONSERVATION_FROM_PAIR_PREVIEW = (
    "psi equation + psibar adjoint equation -> nabla_mu J^mu = 0"
)
SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW = (
    "nabla_mu F^{mu nu} = J^nu requires nabla_nu J^nu = 0"
)
EXCHANGE_ROUTE_PREVIEW = (
    "T_A and T_psi exchange through F^nu{}_alpha J^alpha after stress-energy definitions"
)
PLAIN_MEANING = (
    "The project records how the psi field is positioned to obey a bounded Dirac-like "
    "equation, while the adjoint equation and charge conservation remain future work."
)

INDEXED_FUTURE_ROUTES = [
    {
        "route_id": "adjoint_dirac_route",
        "route_shape": ADJOINT_ROUTE_PREVIEW,
        "status": "indexed_not_derived",
        "proof_claimed": False,
    },
    {
        "route_id": "current_conservation_from_dirac_pair_route",
        "route_shape": CURRENT_CONSERVATION_FROM_PAIR_PREVIEW,
        "status": "indexed_requires_psi_and_adjoint_equations",
        "proof_claimed": False,
    },
    {
        "route_id": "sourced_maxwell_compatibility_route",
        "route_shape": SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW,
        "status": "indexed_not_sourced_maxwell_closure",
        "proof_claimed": False,
    },
    {
        "route_id": "exchange_route",
        "route_shape": EXCHANGE_ROUTE_PREVIEW,
        "status": "indexed_not_stress_energy_or_exchange_proof",
        "proof_claimed": False,
    },
]

BLOCKED_CLAIMS = [
    "adjoint Dirac derivation",
    "current conservation proof",
    "sourced Maxwell closure",
    "stress-energy derivation",
    "exchange identity",
    "total conservation proof",
    "C_exchange closeout",
    "EM-QFT closure",
    "QFT-GR closure",
    "quantized electromagnetism",
    "anomaly analysis",
    "Phase 2 authorization",
    "empirical validation",
    "master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1PsiVariationDiracRoutePacket.lean"
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


def _review_criteria(current_obligation: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "current_conservation_obligation_consumed",
            "status": "accepted",
            "evidence": current_obligation.get("outcome_id"),
            "assessment": "The current-conservation obligation packet is the consumed input.",
        },
        {
            "row_id": "action_block_and_plus_sign_convention_preserved",
            "status": "accepted",
            "evidence": [ACTION_BLOCK_STATEMENT, COVARIANT_DERIVATIVE_POLICY],
            "assessment": "The bounded psi-A action block and plus-sign D_mu convention are preserved.",
        },
        {
            "row_id": "psibar_variation_route_recorded",
            "status": "accepted",
            "evidence": PSIBAR_VARIATION_ROUTE,
            "assessment": "The bounded psibar-variation route is recorded.",
        },
        {
            "row_id": "psi_equation_route_recorded",
            "status": "accepted",
            "evidence": PSI_EQUATION_ROUTE,
            "assessment": "The psi equation route is recorded without closing the adjoint route.",
        },
        {
            "row_id": "future_routes_indexed",
            "status": "accepted",
            "evidence": [route["route_shape"] for route in INDEXED_FUTURE_ROUTES],
            "assessment": "Adjoint, current-conservation, sourced-Maxwell compatibility, and exchange routes are indexed only.",
        },
        {
            "row_id": "adjoint_route_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The adjoint Dirac route packet is selected as the next strict target.",
        },
        {
            "row_id": "closure_and_promotion_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Current conservation, exchange, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_psi_variation_dirac_route_packet",
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


def build_toe_native_psi_a_u1_psi_variation_dirac_route_packet(
    *,
    current_conservation_obligation_path: Path = CURRENT_CONSERVATION_OBLIGATION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    current_obligation = _read_json(current_conservation_obligation_path)
    review_criteria = _review_criteria(current_obligation)
    acceptance_criteria = {
        "consumes_expected_current_conservation_obligation_packet": (
            current_obligation.get("schema_id")
            == CURRENT_CONSERVATION_OBLIGATION_SCHEMA_ID
            and current_obligation.get("packet_id")
            == CURRENT_CONSERVATION_OBLIGATION_PACKET_ID
            and current_obligation.get("outcome_id")
            == CURRENT_CONSERVATION_OBLIGATION_OUTCOME
            and current_obligation.get("packet_result")
            == CURRENT_CONSERVATION_OBLIGATION_RESULT
            and current_obligation.get("selected_next_target") == CONSUMED_TARGET
            and current_obligation.get("accepted") is True
        ),
        "action_block_and_conventions_preserved": (
            current_obligation.get("action_block_statement") == ACTION_BLOCK_STATEMENT
            and current_obligation.get("covariant_derivative_policy")
            == COVARIANT_DERIVATIVE_POLICY
            and current_obligation.get("field_strength_policy") == FIELD_STRENGTH_POLICY
            and current_obligation.get("gauge_transformation_policy")
            == GAUGE_TRANSFORMATION_POLICY
        ),
        "current_conservation_obligation_preserved": (
            current_obligation.get("current_candidate_policy") == CURRENT_CANDIDATE_POLICY
            and current_obligation.get("target_conservation_law")
            == TARGET_CONSERVATION_LAW
            and current_obligation.get("current_conservation_proved") is False
        ),
        "psibar_variation_route_recorded": (
            PRIMARY_VARIATION_VARIABLE == "psibar"
            and PSIBAR_VARIATION_ROUTE.endswith(PSI_EQUATION_ROUTE)
            and PSI_EQUATION_ROUTE == DIRAC_ROUTE_EQUATION
        ),
        "future_routes_indexed_without_proof": (
            len(INDEXED_FUTURE_ROUTES) == 4
            and all(route["proof_claimed"] is False for route in INDEXED_FUTURE_ROUTES)
        ),
        "adjoint_route_selected_next": (
            NEXT_TARGET == "prepare_toe_native_psi_A_u1_adjoint_dirac_route_packet"
        ),
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 14,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_current_conservation_obligation_packet_result": (
            CURRENT_CONSERVATION_OBLIGATION_OUTCOME
        ),
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "follow_on_current_conservation_target": FOLLOW_ON_CURRENT_CONSERVATION_TARGET,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "current_candidate_from_A_variation": CURRENT_CANDIDATE_FROM_A_VARIATION,
        "A_variation_residual": A_VARIATION_RESIDUAL,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY,
        "bounded_route_shape": BOUNDED_ROUTE_SHAPE,
        "target_conservation_law": TARGET_CONSERVATION_LAW,
        "current_conservation_question": CURRENT_CONSERVATION_QUESTION,
        "field_equation_route_preview": FIELD_EQUATION_ROUTE_PREVIEW,
        "sourced_maxwell_consistency_route_preview": (
            SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW
        ),
        "primary_variation_variable": PRIMARY_VARIATION_VARIABLE,
        "psibar_variation_route": PSIBAR_VARIATION_ROUTE,
        "psi_equation_route": PSI_EQUATION_ROUTE,
        "dirac_route_equation": DIRAC_ROUTE_EQUATION,
        "psi_equation_route_status": PSI_EQUATION_ROUTE_STATUS,
        "adjoint_dirac_route_obligation": ADJOINT_DIRAC_ROUTE_OBLIGATION,
        "adjoint_route_preview": ADJOINT_ROUTE_PREVIEW,
        "current_conservation_from_pair_preview": CURRENT_CONSERVATION_FROM_PAIR_PREVIEW,
        "sourced_maxwell_compatibility_route_preview": (
            SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW
        ),
        "exchange_route_preview": EXCHANGE_ROUTE_PREVIEW,
        "indexed_future_routes": INDEXED_FUTURE_ROUTES,
        "indexed_future_route_count": len(INDEXED_FUTURE_ROUTES),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "psi_variation_dirac_route_packet_prepared": accepted,
        "psibar_variation_route_recorded": accepted,
        "psi_equation_route_recorded": accepted,
        "dirac_route_from_psibar_variation_recorded": accepted,
        "adjoint_route_indexed": accepted,
        "current_conservation_route_indexed": accepted,
        "sourced_maxwell_compatibility_route_indexed": accepted,
        "exchange_route_indexed": accepted,
        "adjoint_dirac_route_packet_selected": accepted,
        "adjoint_dirac_route_packet_preparation_authorized": accepted,
        "current_conservation_from_dirac_pair_target_indexed": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "psi_variation_result_derived": False,
        "psi_field_equation_derived": False,
        "psi_equation_derived": False,
        "dirac_equation_derived": False,
        "full_dirac_derivation_closed": False,
        "adjoint_dirac_equation_derived": False,
        "adjoint_dirac_derivation_claimed": False,
        "current_conservation_proved": False,
        "sourced_maxwell_closure_claimed": False,
        "sourced_maxwell_equation_derived": False,
        "stress_energy_derived": False,
        "psi_stress_energy_derived": False,
        "exchange_identity_proved": False,
        "gauge_matter_exchange_proved": False,
        "matter_gauge_exchange_proved": False,
        "total_conservation_proved": False,
        "total_stress_energy_conservation_proved": False,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "quantized_electromagnetism_claimed": False,
        "anomaly_analysis_performed": False,
        "anomaly_cancellation_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "treat psi equation route recording as full Dirac derivation closeout",
            "derive or close the adjoint Dirac equation",
            "prove current conservation",
            "claim sourced Maxwell closure",
            "derive stress-energy or exchange",
            "prove total conservation",
            "close C_exchange",
            "claim EM-QFT or QFT-GR closure",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This packet records the bounded psibar-variation route for the selected "
            "psi-A U(1) action block: delta_{psibar} S_{psi A} -> "
            "(i gamma^mu D_mu - m) psi = 0. It indexes the adjoint equation and "
            "current-conservation routes as future obligations."
        ),
        "plain_meaning": PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a psi-variation / Dirac route packet only; it records "
            "delta_{psibar} S_{psi A} -> (i gamma^mu D_mu - m) psi = 0 as a "
            "bounded psi equation route. It records no adjoint Dirac derivation, "
            "no current conservation proof, no sourced Maxwell closure, no "
            "stress-energy derivation, no exchange identity, no total conservation "
            "proof, no C_exchange closeout, no EM-QFT closure, no QFT-GR closure, "
            "no quantized electromagnetism, no anomaly analysis, no Phase 2 "
            "authorization, no empirical validation, and no master-action promotion. "
            "The full ToeFormal aggregate is recorded as NOT_RUN for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "current_conservation_obligation_json": _ptr(
                current_conservation_obligation_path
            ),
            "current_conservation_obligation_outcome": (
                CURRENT_CONSERVATION_OBLIGATION_OUTCOME
            ),
        },
        "generated_outputs": {
            "json": _ptr(DEFAULT_OUT),
            "lean_marker": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the ToE-native psi-A U(1) psibar-variation Dirac route packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--current-conservation-obligation",
        type=Path,
        default=CURRENT_CONSERVATION_OBLIGATION_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_psi_variation_dirac_route_packet(
        current_conservation_obligation_path=args.current_conservation_obligation,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
