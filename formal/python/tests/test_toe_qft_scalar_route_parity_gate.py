from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

REQUIRED_REFS = (
    "formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0.md",
    "formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md",
    "formal/output/toe_qft_scalar_field_equations_v0.json",
    "formal/docs/paper/toe_qft_scalar_covariance_report_v0.md",
    "formal/output/toe_qft_scalar_stress_energy_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_canonical_quantization_report_v0.md",
    "formal/output/toe_qft_scalar_canonical_quantization_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_canonical_momentum_report_v0.md",
    "formal/output/toe_qft_scalar_hamiltonian_density_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_operator_commutator_report_v0.md",
    "formal/output/toe_qft_scalar_operator_commutator_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_mode_expansion_report_v0.md",
    "formal/output/toe_qft_scalar_creation_annihilation_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_normalization_report_v0.md",
    "formal/output/toe_qft_scalar_one_particle_state_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_nonrelativistic_limit_report_v0.md",
    "formal/output/toe_qft_scalar_schrodinger_limit_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_propagator_report_v0.md",
    "formal/output/toe_qft_scalar_two_point_function_artifact_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MILESTONE_SUMMARY_v0.md",
    "formal/output/toe_qft_scalar_route_milestone_checkpoint_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_REVIEW_READINESS_v0.md",
    "formal/output/toe_qft_scalar_route_review_readiness_checkpoint_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_SKELETON_v0.md",
    "formal/output/toe_qft_scalar_route_section_map_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md",
    "formal/output/toe_qft_scalar_route_manuscript_fill_map_v0.json",
    "formal/output/toe_qft_scalar_route_citation_binding_map_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_BIBLIOGRAPHY_ALIGNMENT_v0.md",
    "formal/output/toe_qft_scalar_route_reference_map_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_v0.md",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_TECHNICAL_SIGNOFF_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_OBJECTIVE_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET07_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET07_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET08_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET08_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET08_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET09_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET09_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET09_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET10_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET10_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET10_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET11_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET11_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET11_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET12_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET12_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET12_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET13_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET13_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET13_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET14_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET14_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET14_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET15_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET15_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET16_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET16_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET16_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET17_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET17_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET17_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET18_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET18_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET18_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET19_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET19_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET19_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET20_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET20_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET20_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET21_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET21_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET22_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET22_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET22_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET23_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET23_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET23_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET24_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET24_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET24_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET25_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET25_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET25_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET26_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET26_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET26_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET27_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET27_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET27_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET28_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET28_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET28_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET29_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET29_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET29_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET30_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET30_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET30_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET31_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET31_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET31_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET32_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET32_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET32_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET33_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET33_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET33_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET34_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET34_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET34_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET35_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET35_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET35_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET36_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET36_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET36_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET37_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET37_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET37_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET38_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET38_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET39_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET39_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET39_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_BOUNDED_EXECUTION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_REVIEW_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md",
    "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md",
    "formal/output/toe_qft_scalar_route_full_technical_record_checkpoint_v0.json",
    "formal/output/toe_qft_scalar_route_scalar_inventory_manifest_v0.json",
    "formal/output/toe_qft_scalar_route_technical_signoff_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet06_objective_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet06_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet07_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet07_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet07_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet08_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet08_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet08_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet09_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet09_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet09_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet10_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet10_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet10_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet11_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet11_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet11_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet12_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet12_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet12_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet13_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet13_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet13_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet14_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet14_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet14_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet15_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet15_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet15_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet16_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet16_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet16_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet17_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet17_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet17_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet18_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet18_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet18_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet19_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet19_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet19_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet20_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet20_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet20_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet21_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet21_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet21_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet22_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet22_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet22_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet23_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet23_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet23_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet24_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet24_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet24_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet25_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet25_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet25_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet26_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet26_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet26_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet27_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet27_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet27_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet28_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet28_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet28_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet29_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet29_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet29_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet30_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet30_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet30_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet31_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet31_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet31_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet32_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet32_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet32_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet33_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet33_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet33_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet34_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet34_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet34_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet35_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet35_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet35_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet36_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet36_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet36_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet37_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet37_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet37_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet38_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet38_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet38_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet39_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet39_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet39_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet40_authorization_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet40_bounded_execution_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet40_assessment_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet41_targeted_justification_review_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet41_hold_fork_decision_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet41_reconsideration_numeric_thresholds_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet41_numeric_threshold_measurement_protocol_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet41_reconsideration_scorecard_worksheet_checkpoint_v0.json",
    "formal/output/toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json",
    "formal/python/tests/test_toe_qft_scalar_route_charter_gate.py",
    "formal/python/tests/test_toe_qft_scalar_field_equation_gate.py",
    "formal/python/tests/test_toe_qft_scalar_covariance_gate.py",
    "formal/python/tests/test_toe_qft_scalar_quantization_gate.py",
    "formal/python/tests/test_toe_qft_scalar_hamiltonian_gate.py",
    "formal/python/tests/test_toe_qft_scalar_operator_commutator_gate.py",
    "formal/python/tests/test_toe_qft_scalar_mode_expansion_gate.py",
    "formal/python/tests/test_toe_qft_scalar_normalization_gate.py",
    "formal/python/tests/test_toe_qft_scalar_nonrelativistic_limit_gate.py",
    "formal/python/tests/test_toe_qft_scalar_propagator_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_milestone_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_review_readiness_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_manuscript_skeleton_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_manuscript_draft_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_citation_binding_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_bibliography_alignment_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_parity_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_full_technical_record_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_full_technical_record_coupling_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_technical_signoff_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_reactivation_objective_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet06_objective_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet06_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet07_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet07_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet07_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet08_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet08_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet08_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet09_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet09_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet09_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet10_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet10_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet10_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet11_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet11_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet11_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet12_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet12_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet12_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet13_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet13_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet13_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet14_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet14_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet14_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet15_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet15_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet15_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet16_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet16_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet16_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet17_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet17_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet17_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet18_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet18_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet18_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet19_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet19_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet19_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet20_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet20_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet20_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet21_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet21_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet21_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet22_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet22_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet22_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet23_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet23_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet23_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet24_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet24_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet24_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet25_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet25_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet25_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet26_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet26_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet26_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet27_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet27_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet27_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet28_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet28_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet28_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet29_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet29_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet29_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet30_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet30_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet30_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet31_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet31_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet31_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet32_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet32_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet32_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet33_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet33_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet33_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet34_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet34_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet34_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet35_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet35_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet35_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet36_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet36_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet36_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet37_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet37_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet37_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet38_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet38_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet38_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet39_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet39_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet39_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet40_authorization_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet40_bounded_execution_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet40_assessment_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_convergence_termination_criterion_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet41_eligibility_review_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet41_targeted_justification_review_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet41_hold_fork_decision_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_retrospective_cumulative_delta_audit_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_numeric_thresholds_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet41_numeric_threshold_measurement_protocol_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_scorecard_worksheet_gate.py",
    "formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_scorecard_cycle01_evaluation_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_compact_state_or_inventory(
    state_text: str,
    inventory_text: str,
    token_name: str,
) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", state_text)
    if m is not None:
        return m.group(1)
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", inventory_text)
    assert m is not None, f"Missing token `{token_name}` in compact State or Inventory."
    return m.group(1)


def test_toe_qft_scalar_route_cross_surface_pointer_parity() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in REQUIRED_REFS:
        is_scalar_family_ref = (
            "scalar_route" in ref
            or "toe_qft_scalar_" in ref
            or "test_toe_qft_scalar_" in ref
        )
        if is_scalar_family_ref:
            assert ref in state_text or ref in inventory_text, (
                f"Scalar-route pointer missing from compact State/Inventory: {ref}"
            )
        assert ref in roadmap_text, f"Scalar-route pointer missing from PHYSICS_ROADMAP_v0.md: {ref}"


def test_toe_qft_scalar_route_referenced_surfaces_exist() -> None:
    for ref in REQUIRED_REFS:
        path = REPO_ROOT / ref
        assert path.exists(), f"Scalar-route parity pointer target does not exist: {ref}"


def test_toe_qft_scalar_route_full_technical_record_token_parity() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_STATUS_v0",
    )
    roadmap_status = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_STATUS_v0")
    state_coupling = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_COUPLING_STATUS_v0",
    )
    roadmap_coupling = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_COUPLING_STATUS_v0")

    state_checkpoint_file = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_CHECKPOINT_FILE_v0",
    )
    roadmap_checkpoint_file = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_CHECKPOINT_FILE_v0")
    state_manifest_file = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_MANIFEST_FILE_v0",
    )
    roadmap_manifest_file = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_MANIFEST_FILE_v0")

    assert state_status == roadmap_status == "PHASE0_PHASE1_LOCKED_AUDIT_READY_V0"
    assert state_coupling == roadmap_coupling == "ARTIFACT_AND_STATUS_PARITY_ENFORCED"
    assert state_checkpoint_file == roadmap_checkpoint_file == "toe_qft_scalar_route_full_technical_record_checkpoint_v0.json"
    assert state_manifest_file == roadmap_manifest_file == "toe_qft_scalar_route_scalar_inventory_manifest_v0.json"


def test_toe_qft_scalar_route_seam_hold_posture_is_unchanged() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    state_seam = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
