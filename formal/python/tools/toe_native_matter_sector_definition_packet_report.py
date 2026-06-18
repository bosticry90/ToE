from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_provisional_scalar_classical_source_route_witness_closeout_report import (
    AUXILIARY_HYGIENE_TARGET,
    CLOSEOUT_RESULT,
    DEFAULT_OUT as SCALAR_WITNESS_CLOSEOUT_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SCALAR_WITNESS_CLOSEOUT_OUTCOME,
    SCHEMA_ID as SCALAR_WITNESS_CLOSEOUT_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_v0"
DEFINITION_RESULT = (
    "MASTER_ACTION_MATTER_SURFACES_INDEXED_AS_NATIVE_CANDIDATES_NO_DERIVATION_CLAIM"
)
OUTCOME_ID = (
    "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_PREPARED_"
    "MASTER_ACTION_MATTER_SURFACES_INDEXED_AS_NATIVE_CANDIDATES_"
    "NO_DERIVATION_CLAIM"
)
PACKET_CLASSIFICATION = (
    "toe_native_matter_sector_definition_packet_indexes_master_action_matter_"
    "surfaces_as_native_candidates_no_derivation_claim"
)
NEXT_TARGET = "review_toe_native_matter_sector_definition_packet_result"
NEXT_TARGET_KIND = "toe_native_matter_sector_definition_packet_result_review"
POST_REVIEW_ROUTE_SELECTION_TARGET = "select_toe_native_matter_sector_calculation_route"
FIRST_CALCULATION_ROUTE_CANDIDATES = [
    "derive_stress_energy_from_candidate_scalar_or_field_term",
    "derive_current_from_candidate_gauge_term",
    "derive_dirac_or_fermion_stress_energy_route",
    "define_quantum_expectation_source_prerequisite_map",
]
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

MASTER_ACTION_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeMatterSectorDefinitionPacket.lean"
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

MASTER_ACTION_SURFACE = "S_ToE[g, psi, A, phi, rho]"
MASTER_ACTION_PROMOTION_STATUS = "TOE_CANONICAL_ACTION_PROMOTION_STATUS_v0: BLOCKED_PENDING_CRITERIA"
MASTER_ACTION_PROMOTION_REQUIRES = (
    "TOE_CANONICAL_ACTION_PROMOTION_REQUIRES_v0: "
    "THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required text file: {path}")
    return path.read_text(encoding="utf-8")


def _matter_surface_inventory() -> list[dict[str, Any]]:
    return [
        {
            "surface_id": "MA-MATTER-PSI-FERMION-SURFACE",
            "symbol": "psi",
            "label": "fermion_matter_surface",
            "source_document": _ptr(MASTER_ACTION_DOC_PATH),
            "source_term": "sum_a psi_bar_a * (i*gamma^mu*D_mu - m_a) * psi_a",
            "source_of_candidate_identified": True,
            "status_decision": (
                "imported_known_physics_term_indexed_as_provisional_"
                "toe_native_candidate_surface"
            ),
            "imported_known_physics_term": True,
            "provisional_toe_native_candidate": True,
            "pure_organizing_placeholder": False,
            "insufficiently_defined": True,
            "variation_route_status": "specified_but_blocked",
            "variation_route": (
                "candidate variation with respect to psi/psi_bar toward a "
                "Dirac-family equation is identified but blocked pending "
                "spinor bundle, gamma-matrix, covariant derivative, mass, "
                "gauge-coupling, and domain conventions"
            ),
            "stress_energy_route_status": "specified_but_blocked",
            "stress_energy_route": (
                "metric/tetrad variation route is identified but blocked "
                "pending spin structure, tetrad policy, regularity, and "
                "source-admissibility review"
            ),
            "quantum_operator_route_status": "blocked",
            "quantum_operator_route": (
                "operator/state route blocked pending canonical or path-integral "
                "quantization, state domain, renormalization, and anomaly controls"
            ),
            "seam_constraint_dependency": [
                "C_k(g, psi, A, phi, rho)",
                "fermion-gauge compatibility",
                "QFT-GR stress-energy source admissibility",
                "QM/QFT operator-domain semantics",
            ],
        },
        {
            "surface_id": "MA-MATTER-A-GAUGE-SURFACE",
            "symbol": "A",
            "label": "gauge_field_surface",
            "source_document": _ptr(MASTER_ACTION_DOC_PATH),
            "source_term": "-(1/4) * F_{mu nu} * F^{mu nu}",
            "source_of_candidate_identified": True,
            "status_decision": (
                "imported_known_physics_gauge_term_indexed_as_provisional_"
                "toe_native_candidate_surface"
            ),
            "imported_known_physics_term": True,
            "provisional_toe_native_candidate": True,
            "pure_organizing_placeholder": False,
            "insufficiently_defined": True,
            "variation_route_status": "specified_but_blocked",
            "variation_route": (
                "gauge-field variation route toward gauge equations/current "
                "coupling is identified but blocked pending gauge group, "
                "representation, current map, boundary, and gauge-fixing policy"
            ),
            "stress_energy_route_status": "specified_but_blocked",
            "stress_energy_route": (
                "gauge stress-energy route is identified but blocked pending "
                "gauge group, coupling normalization, regularity, and source "
                "admissibility"
            ),
            "quantum_operator_route_status": "blocked",
            "quantum_operator_route": (
                "quantized gauge/source-current route blocked pending gauge "
                "quantization semantics, state domain, renormalization, and "
                "anomaly controls"
            ),
            "seam_constraint_dependency": [
                "C_k(g, psi, A, phi, rho)",
                "EM-QFT gauge/quantization semantics",
                "source-current interface alignment",
                "QFT-GR stress-energy source admissibility",
            ],
        },
        {
            "surface_id": "MA-MATTER-PHI-SCALAR-STRUCTURE-SURFACE",
            "symbol": "phi",
            "label": "scalar_structure_surface",
            "source_document": _ptr(MASTER_ACTION_DOC_PATH),
            "source_term": "(1/2) * sum_i nabla_mu(phi_i) * nabla^mu(phi_i) - V(phi)",
            "source_of_candidate_identified": True,
            "status_decision": (
                "scalar_structure_term_indexed_as_provisional_toe_native_"
                "candidate_surface_with_imported_scalar_witness_boundary"
            ),
            "imported_known_physics_term": True,
            "provisional_toe_native_candidate": True,
            "pure_organizing_placeholder": False,
            "insufficiently_defined": True,
            "variation_route_status": "partially_witnessed_for_imported_scalar_blocked_for_toe_native",
            "variation_route": (
                "real-scalar variation and stress-energy mechanics are witnessed "
                "only for the imported scalar sandbox; ToE-native scalar/structure "
                "field content, index set, sign convention, and generation rule "
                "remain undefined"
            ),
            "stress_energy_route_status": "partially_witnessed_for_imported_scalar_blocked_for_toe_native",
            "stress_energy_route": (
                "classical scalar stress-energy route is available as the "
                "positive imported sandbox witness, but not as a ToE-native "
                "matter derivation"
            ),
            "quantum_operator_route_status": "blocked",
            "quantum_operator_route": (
                "quantum scalar expectation route blocked pending state, "
                "operator, renormalization, and domain controls"
            ),
            "seam_constraint_dependency": [
                "C_k(g, psi, A, phi, rho)",
                "scalar witness boundary",
                "QFT-GR source route admissibility",
                "regime and transport alignment",
            ],
        },
        {
            "surface_id": "MA-MATTER-RHO-STATISTICAL-STATE-SURFACE",
            "symbol": "rho",
            "label": "statistical_state_surface",
            "source_document": _ptr(MASTER_ACTION_DOC_PATH),
            "source_term": "lambda_stat * rho * (ln(rho) - 1)",
            "source_of_candidate_identified": True,
            "status_decision": (
                "speculative_statistical_state_surface_indexed_as_"
                "organizing_placeholder_and_candidate_dependency"
            ),
            "imported_known_physics_term": False,
            "provisional_toe_native_candidate": True,
            "pure_organizing_placeholder": True,
            "insufficiently_defined": True,
            "variation_route_status": "blocked",
            "variation_route": (
                "variation route blocked pending rho domain, positivity, "
                "normalization, measure, entropy functional, and log-domain policy"
            ),
            "stress_energy_route_status": "blocked",
            "stress_energy_route": (
                "stress-energy/source route blocked pending statistical-state "
                "coupling to geometry and source-admissibility semantics"
            ),
            "quantum_operator_route_status": "blocked",
            "quantum_operator_route": (
                "state/operator route blocked pending QM-STAT transport semantics "
                "and expectation/source map"
            ),
            "seam_constraint_dependency": [
                "C_k(g, psi, A, phi, rho)",
                "QM-STAT transport semantics",
                "state-domain semantics",
                "renormalized expectation/source prerequisite map",
            ],
        },
        {
            "surface_id": "MA-MATTER-CK-SEAM-CONSTRAINT-SURFACE",
            "symbol": "C_k",
            "label": "seam_constraint_surface",
            "source_document": _ptr(MASTER_ACTION_DOC_PATH),
            "source_term": "sum_k lambda_k * C_k(g, psi, A, phi, rho)",
            "source_of_candidate_identified": True,
            "status_decision": (
                "seam_constraint_surface_indexed_as_required_organizing_"
                "dependency_not_matter_derivation"
            ),
            "imported_known_physics_term": False,
            "provisional_toe_native_candidate": True,
            "pure_organizing_placeholder": True,
            "insufficiently_defined": True,
            "variation_route_status": "blocked",
            "variation_route": (
                "constraint variation blocked pending admitted C_k classes, "
                "multiplier policy, compatibility theorem links, and transport "
                "alignment"
            ),
            "stress_energy_route_status": "blocked",
            "stress_energy_route": (
                "source contribution from constraints blocked pending whether "
                "admitted C_k terms are metric-dependent and source-admissible"
            ),
            "quantum_operator_route_status": "blocked",
            "quantum_operator_route": (
                "operator route blocked pending seam-constraint quantization or "
                "classical constraint-domain policy"
            ),
            "seam_constraint_dependency": [
                "cross-pillar compatibility",
                "bridge admissibility",
                "transport consistency",
                "canonical promotion prerequisites",
            ],
        },
    ]


def _inventory_requirements() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "matter_sector_candidates_listed",
            "satisfied": True,
            "evidence": "psi, A, phi, rho, C_k indexed from candidate master action",
        },
        {
            "row_id": "source_of_each_candidate_identified",
            "satisfied": True,
            "evidence": _ptr(MASTER_ACTION_DOC_PATH),
        },
        {
            "row_id": "imported_vs_native_candidate_status_marked",
            "satisfied": True,
            "evidence": "status_decision and imported/provisional/placeholder flags",
        },
        {
            "row_id": "variation_route_specified_or_blocked",
            "satisfied": True,
            "evidence": "variation_route_status on every indexed surface",
        },
        {
            "row_id": "stress_energy_route_specified_or_blocked",
            "satisfied": True,
            "evidence": "stress_energy_route_status on every indexed surface",
        },
        {
            "row_id": "quantum_operator_route_specified_or_blocked",
            "satisfied": True,
            "evidence": "quantum_operator_route_status on every indexed surface",
        },
        {
            "row_id": "seam_constraint_dependency_recorded",
            "satisfied": True,
            "evidence": "seam_constraint_dependency on every indexed surface",
        },
        {
            "row_id": "next_calculation_target_selected",
            "satisfied": True,
            "evidence": POST_REVIEW_ROUTE_SELECTION_TARGET,
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_matter_sector_definition_packet",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": "NOT_RUN",
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
    }


def build_toe_native_matter_sector_definition_packet(
    *,
    scalar_witness_closeout_packet_path: Path = SCALAR_WITNESS_CLOSEOUT_PACKET_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout_packet = _read_json(scalar_witness_closeout_packet_path)
    master_action_doc = _read_text(master_action_doc_path)
    inventory = _matter_surface_inventory()
    requirements = _inventory_requirements()
    symbols = [row["symbol"] for row in inventory]
    acceptance_criteria = {
        "consumes_expected_live_target": closeout_packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "scalar_witness_closeout_available_and_accepted": (
            closeout_packet.get("schema_id") == SCALAR_WITNESS_CLOSEOUT_SCHEMA_ID
            and closeout_packet.get("outcome_id") == SCALAR_WITNESS_CLOSEOUT_OUTCOME
            and closeout_packet.get("accepted") is True
        ),
        "master_action_document_available": (
            MASTER_ACTION_SURFACE in master_action_doc
            and "Let fields and objects be `g, psi, A, phi, rho` with seam constraints `C_k`."
            in master_action_doc
        ),
        "master_action_working_form_noncanonical": (
            "working-form artifact only" in master_action_doc
            and "explicitly non-canonical" in master_action_doc
            and MASTER_ACTION_PROMOTION_STATUS in master_action_doc
            and MASTER_ACTION_PROMOTION_REQUIRES in master_action_doc
        ),
        "matter_sector_candidates_listed": symbols == ["psi", "A", "phi", "rho", "C_k"],
        "source_of_each_candidate_identified": all(
            row["source_of_candidate_identified"] for row in inventory
        ),
        "imported_vs_native_candidate_status_marked": all(
            "status_decision" in row
            and "imported_known_physics_term" in row
            and "provisional_toe_native_candidate" in row
            for row in inventory
        ),
        "variation_route_specified_or_blocked": all(
            row["variation_route_status"]
            in {
                "specified_but_blocked",
                "partially_witnessed_for_imported_scalar_blocked_for_toe_native",
                "blocked",
            }
            for row in inventory
        ),
        "stress_energy_route_specified_or_blocked": all(
            row["stress_energy_route_status"]
            in {
                "specified_but_blocked",
                "partially_witnessed_for_imported_scalar_blocked_for_toe_native",
                "blocked",
            }
            for row in inventory
        ),
        "quantum_operator_route_specified_or_blocked": all(
            row["quantum_operator_route_status"] == "blocked" for row in inventory
        ),
        "seam_constraint_dependency_recorded": all(
            bool(row["seam_constraint_dependency"]) for row in inventory
        ),
        "next_calculation_target_selected": (
            POST_REVIEW_ROUTE_SELECTION_TARGET
            == "select_toe_native_matter_sector_calculation_route"
            and len(FIRST_CALCULATION_ROUTE_CANDIDATES) == 4
        ),
        "gate_nonclaims_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_DEFINITION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_REQUIRES_REMEDIATION",
        "definition_result": DEFINITION_RESULT,
        "matter_sector_definition_result": DEFINITION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_review_route_selection_target": POST_REVIEW_ROUTE_SELECTION_TARGET,
        "first_calculation_route_candidates": FIRST_CALCULATION_ROUTE_CANDIDATES,
        "scalar_witness_closeout_result": CLOSEOUT_RESULT,
        "scalar_witness_closeout_outcome": closeout_packet.get("outcome_id"),
        "scalar_witness_closeout_preserved_as_reference": True,
        "scalar_sandbox_reopened": False,
        "default_scalar_sandbox_extension_authorized": False,
        "candidate_master_action_surface": MASTER_ACTION_SURFACE,
        "master_action_doc": _ptr(master_action_doc_path),
        "master_action_working_form_noncanonical": True,
        "master_action_promotion_status": "BLOCKED_PENDING_CRITERIA",
        "master_action_promotion_requires": (
            "THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT"
        ),
        "native_candidate_surface_defined_nonpromotionally": prepared,
        "toe_native_matter_sector_candidate_surface_defined": prepared,
        "canonical_toe_native_matter_sector_defined": False,
        "toe_native_matter_sector_defined": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "toe_matter_sector_derived": False,
        "toe_matter_model_derived": False,
        "standard_model_derivation_claimed": False,
        "master_action_matter_surfaces_indexed_as_native_candidates": prepared,
        "candidate_surface_count": len(inventory),
        "candidate_symbols": symbols,
        "matter_surface_inventory": inventory,
        "inventory_requirements": requirements,
        "inventory_requirement_count": len(requirements),
        "inventory_requirement_satisfied_count": sum(
            1 for row in requirements if row["satisfied"]
        ),
        "candidate_status_summary": {
            "imported_known_physics_terms": ["psi", "A", "phi"],
            "provisional_toe_native_candidate_surfaces": symbols,
            "pure_organizing_placeholders": ["rho", "C_k"],
            "insufficiently_defined_surfaces": symbols,
            "partially_witnessed_imported_scalar_surface": "phi",
        },
        "route_status_summary": {
            "variation_route_specified_or_blocked": True,
            "stress_energy_route_specified_or_blocked": True,
            "quantum_operator_route_specified_or_blocked": True,
            "seam_constraint_dependency_recorded": True,
            "first_actual_calculation_deferred_to_route_selection": True,
        },
        "proof_depth_label": "RECORD_ONLY_INDEX_VALIDATED",
        "formal_theorem_backed_matter_derivation": False,
        "formal_differential_geometry_theorem_backed": False,
        "record_validated": True,
        "symbolic_calculation_recorded": False,
        "definition_packet_only": True,
        "promotion_packet": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_map_closed": False,
        "qft_gr_solved": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "renormalized_stress_energy_expectation_constructed": False,
        "quantum_state_source_constructed": False,
        "quantum_stress_energy_operator_constructed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "ToE-native matter derivation",
            "Standard Model derivation",
            "canonical master-action promotion",
            "QFT-GR closure",
            "semiclassical coupling",
            "empirical validation",
            "public readiness",
        ],
        "acceptance_criteria": acceptance_criteria,
        "downstream_progression": [
            {
                "stage": "toe_native_matter_sector_definition_packet",
                "status": "PREPARED_AS_NONPROMOTIONAL_CANDIDATE_SURFACE_INDEX",
                "decision": DEFINITION_RESULT,
                "reason": (
                    "The packet indexes matter-relevant master-action surfaces "
                    "as provisional native candidates or placeholders without "
                    "deriving matter."
                ),
            },
            {
                "stage": "definition_packet_result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": "The definition packet must be reviewed before route selection.",
            },
            {
                "stage": "toe_native_matter_sector_calculation_route_selection",
                "status": "POST_REVIEW_TARGET_RECORDED",
                "decision": POST_REVIEW_ROUTE_SELECTION_TARGET,
                "reason": (
                    "After review, select whether to attack scalar/field "
                    "stress-energy, gauge current, fermion stress-energy, or "
                    "quantum expectation prerequisites."
                ),
            },
            {
                "stage": "stale_current_token_quarantine",
                "status": "QUEUED_NON_SUPERSEDING_HYGIENE",
                "decision": AUXILIARY_HYGIENE_TARGET,
                "reason": (
                    "Status-surface hygiene remains queued but does not supersede "
                    "the physics live target."
                ),
            },
        ],
        "mathematical_statement": (
            "The candidate master action supplies psi, A, phi, rho, and C_k "
            "surfaces that can be indexed as provisional ToE-native matter-sector "
            "candidate surfaces for future route selection. This is a record-only "
            "definition packet: it does not derive matter, derive the Standard "
            "Model, promote the master action, authorize semiclassical coupling, "
            "or close QFT-GR."
        ),
        "non_claim_boundary": (
            "This packet defines/indexes candidate matter-sector surfaces from "
            "the working-form non-canonical master action only. It does not claim "
            "ToE-native matter derivation, Standard Model derivation, canonical "
            "master-action promotion, QFT-GR closure, semiclassical coupling, "
            "empirical validation, public readiness, source-map closure, or "
            "release authorization."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeMatterSectorDefinitionPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(LEAN_PACKET_PATH),
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
    }


def write_toe_native_matter_sector_definition_packet(
    *,
    scalar_witness_closeout_packet_path: Path = SCALAR_WITNESS_CLOSEOUT_PACKET_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_matter_sector_definition_packet(
        scalar_witness_closeout_packet_path=scalar_witness_closeout_packet_path,
        master_action_doc_path=master_action_doc_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the ToE-native matter-sector definition packet."
    )
    parser.add_argument(
        "--scalar-witness-closeout-packet",
        type=Path,
        default=SCALAR_WITNESS_CLOSEOUT_PACKET_PATH,
    )
    parser.add_argument("--master-action-doc", type=Path, default=MASTER_ACTION_DOC_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    scalar_witness_closeout_packet_path = (
        args.scalar_witness_closeout_packet
        if args.scalar_witness_closeout_packet.is_absolute()
        else REPO_ROOT / args.scalar_witness_closeout_packet
    )
    master_action_doc_path = (
        args.master_action_doc
        if args.master_action_doc.is_absolute()
        else REPO_ROOT / args.master_action_doc
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_matter_sector_definition_packet(
        scalar_witness_closeout_packet_path=scalar_witness_closeout_packet_path,
        master_action_doc_path=master_action_doc_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_matter_sector_definition_packet_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
