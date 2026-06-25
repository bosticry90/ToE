from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_current_derivation_from_A_variation_result_review_report import (
    ACTION_BLOCK_STATEMENT,
    A_VARIATION_RESIDUAL,
    BOUNDED_ROUTE_SHAPE,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_CONSERVATION_QUESTION,
    DEFAULT_OUT as CURRENT_REVIEW_PATH,
    FIELD_EQUATION_ROUTE_PREVIEW,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SYMMETRY_ROUTE_PREVIEW,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CURRENT_REVIEW_OUTCOME,
    PACKET_ID as CURRENT_REVIEW_PACKET_ID,
    REVIEW_RESULT as CURRENT_REVIEW_RESULT,
    SCHEMA_ID as CURRENT_REVIEW_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_GAUGE_ROUTE_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET_v0"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET_PREPARED_"
    "CURRENT_CONSERVATION_REQUIREMENTS_INDEXED_NO_CONSERVATION_PROOF_OR_EM_QFT_CLOSURE"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_current_conservation_obligation_packet_prepared_"
    "current_conservation_requirements_indexed_no_conservation_proof_or_em_qft_closure"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_psi_variation_dirac_route_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_psi_variation_dirac_route_packet_preparation"
ALTERNATE_NEXT_TARGET = "prepare_toe_native_psi_A_u1_current_conservation_route_packet"

CURRENT_CANDIDATE_POLICY = (
    "J^mu = q psibar gamma^mu psi; accepted as an A-variation candidate only, "
    "not yet conserved"
)
TARGET_CONSERVATION_LAW = "nabla_mu J^mu = 0"
DIRAC_ROUTE_EQUATION = "(i gamma^mu D_mu - m) psi = 0"
ADJOINT_DIRAC_ROUTE_OBLIGATION = (
    "derive the adjoint equation for psibar under the selected adjoint convention"
)
FIELD_EQUATION_ROUTE_SELECTION_REASON = (
    "current conservation usually needs the psi equation and the psibar adjoint "
    "equation, so the next bounded route should prepare psi variation"
)
SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW = (
    "nabla_mu F^{mu nu} = J^nu requires nabla_nu J^nu = 0"
)
PLAIN_MEANING = (
    "The project now knows which current must be tested for conservation, "
    "but it has not proved charge conservation."
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CurrentConservationObligationPacket.lean"
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

PROOF_ROUTES = [
    {
        "route_id": "gauge_symmetry_noether_route",
        "route_label": "Route 1: gauge-symmetry / Noether route",
        "route_shape": GAUGE_SYMMETRY_ROUTE_PREVIEW,
        "status": "indexed_not_executed",
        "proof_claimed": False,
    },
    {
        "route_id": "field_equation_route",
        "route_label": "Route 2: field-equation route",
        "route_shape": FIELD_EQUATION_ROUTE_PREVIEW,
        "requires": [
            DIRAC_ROUTE_EQUATION,
            ADJOINT_DIRAC_ROUTE_OBLIGATION,
        ],
        "status": "selected_as_cleanest_future_route_not_executed",
        "proof_claimed": False,
    },
    {
        "route_id": "sourced_maxwell_consistency_route",
        "route_label": "Route 3: sourced-Maxwell consistency route",
        "route_shape": SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW,
        "status": "indexed_as_consistency_requirement_not_closure",
        "proof_claimed": False,
    },
]

OBLIGATIONS = [
    {
        "obligation_id": "CC-O1-current-candidate",
        "statement": CURRENT_CANDIDATE_POLICY,
        "status": "indexed_from_A_variation_review",
    },
    {
        "obligation_id": "CC-O2-target-conservation-law",
        "statement": TARGET_CONSERVATION_LAW,
        "status": "indexed_not_proved",
    },
    {
        "obligation_id": "CC-O3-gauge-symmetry-route",
        "statement": GAUGE_SYMMETRY_ROUTE_PREVIEW,
        "status": "indexed_not_executed",
    },
    {
        "obligation_id": "CC-O4-field-equation-route",
        "statement": FIELD_EQUATION_ROUTE_PREVIEW,
        "status": "selected_as_cleanest_future_route_requires_psi_variation",
    },
    {
        "obligation_id": "CC-O5-sourced-maxwell-consistency-route",
        "statement": SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW,
        "status": "indexed_not_sourced_maxwell_closure",
    },
    {
        "obligation_id": "CC-O6-boundary-domain-adjoint-compatibility",
        "statement": (
            "current conservation proof must respect field domains, boundary "
            "variation policy, gamma/tetrad/spin-connection policy, and psibar adjoint policy"
        ),
        "status": "indexed_not_discharged",
    },
]

BLOCKED_CLAIMS = [
    "current conservation proof",
    "psi variation / Dirac derivation",
    "adjoint Dirac derivation",
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


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "current_result_review_consumed",
            "status": "accepted",
            "evidence": review.get("outcome_id"),
            "assessment": "The accepted A-variation current result review is the consumed input.",
        },
        {
            "row_id": "current_candidate_preserved",
            "status": "accepted",
            "evidence": CURRENT_CANDIDATE_POLICY,
            "assessment": "The accepted current candidate is restated as an obligation target.",
        },
        {
            "row_id": "target_conservation_law_indexed",
            "status": "accepted",
            "evidence": TARGET_CONSERVATION_LAW,
            "assessment": "The target conservation law is indexed but not proved.",
        },
        {
            "row_id": "three_proof_routes_indexed",
            "status": "accepted",
            "evidence": [route["route_shape"] for route in PROOF_ROUTES],
            "assessment": "Gauge-symmetry, field-equation, and sourced-Maxwell consistency routes are indexed.",
        },
        {
            "row_id": "field_equation_route_selected_next",
            "status": "accepted",
            "evidence": [DIRAC_ROUTE_EQUATION, NEXT_TARGET],
            "assessment": "The future psi variation / Dirac route is selected as the next bounded target.",
        },
        {
            "row_id": "current_conservation_proof_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "The packet records obligations only and blocks conservation, closure, and promotion claims.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_current_conservation_obligation_packet",
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


def build_toe_native_psi_a_u1_current_conservation_obligation_packet(
    *,
    current_review_path: Path = CURRENT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(current_review_path)
    review_criteria = _review_criteria(review)
    acceptance_criteria = {
        "consumes_expected_current_review": (
            review.get("schema_id") == CURRENT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == CURRENT_REVIEW_PACKET_ID
            and review.get("outcome_id") == CURRENT_REVIEW_OUTCOME
            and review.get("review_result") == CURRENT_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "current_candidate_preserved": (
            review.get("current_candidate_from_A_variation")
            == CURRENT_CANDIDATE_FROM_A_VARIATION
            and review.get("current_candidate_accepted") is True
        ),
        "target_conservation_law_indexed": TARGET_CONSERVATION_LAW == "nabla_mu J^mu = 0",
        "proof_routes_indexed_without_execution": (
            len(PROOF_ROUTES) == 3
            and all(route["proof_claimed"] is False for route in PROOF_ROUTES)
        ),
        "field_equation_route_selected_as_next": (
            NEXT_TARGET == "prepare_toe_native_psi_A_u1_psi_variation_dirac_route_packet"
        ),
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 15,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_current_derivation_result_review": CURRENT_REVIEW_OUTCOME,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "alternate_next_target": ALTERNATE_NEXT_TARGET,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "A_variation_residual": A_VARIATION_RESIDUAL,
        "current_candidate_from_A_variation": CURRENT_CANDIDATE_FROM_A_VARIATION,
        "bounded_route_shape": BOUNDED_ROUTE_SHAPE,
        "sourced_gauge_route_status": SOURCED_GAUGE_ROUTE_STATUS,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY,
        "target_conservation_law": TARGET_CONSERVATION_LAW,
        "current_conservation_question": CURRENT_CONSERVATION_QUESTION,
        "proof_routes": PROOF_ROUTES,
        "proof_route_count": len(PROOF_ROUTES),
        "gauge_symmetry_route_preview": GAUGE_SYMMETRY_ROUTE_PREVIEW,
        "field_equation_route_preview": FIELD_EQUATION_ROUTE_PREVIEW,
        "sourced_maxwell_consistency_route_preview": SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW,
        "dirac_route_equation": DIRAC_ROUTE_EQUATION,
        "adjoint_dirac_route_obligation": ADJOINT_DIRAC_ROUTE_OBLIGATION,
        "field_equation_route_selection_reason": FIELD_EQUATION_ROUTE_SELECTION_REASON,
        "obligations": OBLIGATIONS,
        "obligation_count": len(OBLIGATIONS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "current_conservation_obligation_packet_prepared": accepted,
        "current_conservation_requirements_indexed": accepted,
        "current_candidate_preserved": accepted,
        "target_conservation_law_indexed": accepted,
        "proof_routes_indexed": accepted,
        "gauge_symmetry_route_indexed": accepted,
        "field_equation_route_indexed": accepted,
        "sourced_maxwell_consistency_route_indexed": accepted,
        "field_equation_route_selected_as_next": accepted,
        "psi_variation_dirac_route_packet_selected": accepted,
        "psi_variation_dirac_route_packet_preparation_authorized": accepted,
        "current_conservation_route_executed": False,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "current_conservation_proved": False,
        "psi_variation_result_derived": False,
        "psi_field_equation_derived": False,
        "dirac_equation_derived": False,
        "adjoint_dirac_equation_derived": False,
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
            "treat obligation indexing as current conservation proof",
            "derive the psi equation or adjoint equation",
            "treat sourced-Maxwell consistency route as sourced Maxwell closure",
            "derive stress-energy or exchange",
            "close C_exchange",
            "claim EM-QFT or QFT-GR closure",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This packet indexes the current-conservation obligation nabla_mu J^mu = 0 "
            "for J^mu = q psibar gamma^mu psi and records three possible proof routes "
            "without executing any of them."
        ),
        "plain_meaning": PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a current-conservation obligation packet only; it records "
            "nabla_mu J^mu = 0 as the target law for J^mu = q psibar gamma^mu psi "
            "and indexes gauge-symmetry, field-equation, and sourced-Maxwell "
            "consistency routes. It records no current conservation proof, no psi "
            "variation or Dirac derivation, no adjoint Dirac derivation, no sourced "
            "Maxwell closure, no stress-energy derivation, no exchange identity, no "
            "total conservation proof, no C_exchange closeout, no EM-QFT closure, no "
            "QFT-GR closure, no quantized electromagnetism, no anomaly analysis, no "
            "Phase 2 authorization, no empirical validation, and no master-action "
            "promotion. The full ToeFormal aggregate is recorded as NOT_RUN for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "current_review_json": _ptr(current_review_path),
            "current_review_outcome": CURRENT_REVIEW_OUTCOME,
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
        description="Prepare the ToE-native psi-A U(1) current-conservation obligation packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--current-review", type=Path, default=CURRENT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_current_conservation_obligation_packet(
        current_review_path=args.current_review,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
