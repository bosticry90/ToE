from __future__ import annotations

"""Bridge admissibility manifest generator (quarantine-safe).

Goal
- Pin the bridge program's admissible input families and deterministic scan grids,
  plus the evidence nodes required to label the bridge family as stable.

Policy alignment
- Deterministic mapping only (no runtime discovery).
- Bookkeeping only; does not upgrade epistemic status.
- Does not import from the archive directory.

Manifest schema (v1)
{
  "schema_version": 1,
  "artifacts": {...},
  "ucff_parameter_families": [...],
  "bridge_classes": [...],
  "required_evidence": {"pytest_nodes": [...]},
  "artifact_sha256": "..."
}
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import hashlib
import json
from pathlib import Path
from typing import Optional


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_bytes(data: bytes) -> str:
    h = hashlib.sha256()
    h.update(data)
    return h.hexdigest()


def build_bridge_admissibility_manifest_payload(*, repo_root: Path) -> dict:
    _ = repo_root  # explicit; manifest content is static + deterministic

    payload = {
        "schema_version": 1,
        "artifacts": {
            "bridge_ledger": "formal/quarantine/bridge_tickets/BRIDGE_LEDGER.json",
            "bridge_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_BOUNDARY_REPORT.json",
            "bridge_toyh_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_phase_invariance_BOUNDARY_REPORT.json",
            "bridge_toyh_feasibility": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_invariance_feasibility.json",
            "bridge_toyh_current_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_invariance_BOUNDARY_REPORT.json",
            "bridge_toyh_current_feasibility": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_invariance_feasibility.json",
            "bridge_toyh_phase_anchor_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_phase_anchor_BOUNDARY_REPORT.json",
            "bridge_toyh_phase_anchor_feasibility": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_anchor_feasibility.json",
            "bridge_toyh_current_anchor_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_anchor_BOUNDARY_REPORT.json",
            "bridge_toyh_current_anchor_feasibility": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_anchor_feasibility.json",
            "bridge_toyh_orthogonality_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT.json",
            "bridge_toyh_orthogonality_mismatch_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_MISMATCH_REPORT.json",
            "bridge_toyg_feasibility_scan": "formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json",
            "bridge_toyg_c6_phase_winding_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_phase_winding_BOUNDARY_REPORT.json",
            "bridge_toyg_c6_mode_index_feasibility": "formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json",
            "bridge_toyg_c6_mode_index_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_mode_index_BOUNDARY_REPORT.json",
            "bridge_toyg_c6_unwrap_stability_feasibility": "formal/quarantine/feasibility/BRIDGE_TOYG_C6_unwrap_stability_feasibility.json",
            "bridge_toyg_c6_unwrap_stability_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_unwrap_stability_BOUNDARY_REPORT.json",
            "bridge_program_orthogonality_report": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json",
            "bridge_program_orthogonality_mismatch_report": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
            "bridge_program_mismatch_reason_summary": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json",
            "bridge_toyhg_pair_compatibility_boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYHG_C6_pair_compatibility_BOUNDARY_REPORT.json",
            "bridge_toyhg_pair_compatibility_feasibility": "formal/quarantine/feasibility/BRIDGE_TOYHG_C6_pair_compatibility_feasibility.json",
            "ucff_contract": "formal/docs/ucff_core_front_door_contract.md",
        },
        "ucff_parameter_families": [
            {
                "family_id": "ucff_lowk_linear_family_v1",
                "params": {"rho0": 1.0, "lam": 0.0, "beta": 0.0},
                "derived": {"g": "c^2"},
                "notes": [
                    "c must be selected deterministically from the BR-05 1-sigma overlap as per BRIDGE_TICKET_0002/0003",
                    "this is bookkeeping only; does not assert unit identification",
                ],
            },
            {
                "family_id": "ucff_fixed_shape_family_v1",
                "params": {"rho0": 1.0, "g": 2.0, "lam": 0.25, "beta": 0.125},
                "derived": {},
                "notes": [
                    "fixed parameters (no tuning) used for curvature/convexity bridge class",
                ],
            },
        ],
        "bridge_classes": [
            {
                "bridge_class": "regime_local_compatibility_existence",
                "tickets": ["BRIDGE_TICKET_0002", "BRIDGE_TICKET_0003"],
                "inputs": {
                    "locks": ["formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md"],
                    "contracts": ["formal/docs/ucff_core_front_door_contract.md"],
                },
                "grids": {
                    "k_grid": [0.0, 0.001, 0.002, 0.005, 0.01],
                    "fit": "least_squares_through_origin",
                    "tolerance": {"rel": 0.001, "abs_floor": 1.0},
                },
            },
            {
                "bridge_class": "shape_constraint_curvature_convexity",
                "tickets": ["BRIDGE_TICKET_0004"],
                "inputs": {
                    "locks": [
                        "formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md",
                        "formal/markdown/locks/observables/OV-BR-04b_bragg_lowk_slope_conditionB_OVERRIDE.md",
                    ],
                    "contracts": ["formal/docs/ucff_core_front_door_contract.md"],
                },
                "grids": {
                    "k_grid": {"type": "uniform", "k_min": 0.0, "k_max": "from OV-BR-04A selection.parameters.k_um_inv_max"},
                    "n_values": [5, 7, 9],
                    "convexity_eps": 1e-12,
                    "negative_control": {"operator": "diff2_wrong = -diff2", "min_threshold": 1e-8},
                },
            },
            {
                "bridge_class": "gauge_invariance_compatibility",
                "tickets": ["BRIDGE_TICKET_TOYH_0001"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_invariance_feasibility.json",
                },
                "grids": {
                    "theta_values": [0.0, 0.5235987755982988, 1.0471975511965976, 1.5707963267948966],
                    "grid_sizes": [7, 9, 11],
                    "tolerance": 1e-10,
                    "phase_sensitive_min": 1e-3,
                },
                "scope_limits": [
                    "compatibility_only",
                    "phase_invariance_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "gauge_current_invariance_compatibility",
                "tickets": ["BRIDGE_TICKET_TOYH_0002"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_invariance_feasibility.json",
                    "orthogonality_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT.json",
                    "orthogonality_mismatch_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_MISMATCH_REPORT.json",
                },
                "grids": {
                    "theta_values": [0.0, 0.5235987755982988, 1.0471975511965976, 1.5707963267948966],
                    "grid_sizes": [7, 9, 11],
                    "local_phase_shear_alpha": 0.5,
                    "tolerance": 1e-10,
                    "control_min": 1e-3,
                },
                "scope_limits": [
                    "compatibility_only",
                    "current_observable_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "gauge_phase_anchor_compatibility",
                "tickets": ["BRIDGE_TICKET_TOYH_0003"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "design_feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_anchor_feasibility.json",
                    "boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_phase_anchor_BOUNDARY_REPORT.json",
                    "mismatch_summary_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json",
                    "mismatch_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
                    "orthogonality_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json",
                },
                "grids": {
                    "theta_values": [1e-06, 1.0471975511965976],
                    "grid_sizes": [7, 9, 11],
                    "amplitude_scales": {"admissible": [1.0], "inadmissible": [1.1]},
                    "tolerances": {
                        "toyh_tolerance": 1e-10,
                        "phase_anchor_tolerance": 1e-07,
                        "min_anchor_magnitude": 1e-08,
                    },
                },
                "status": "implemented_bounded",
                "scope_limits": [
                    "compatibility_only",
                    "phase_anchor_proxy_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "gauge_current_anchor_compatibility",
                "tickets": ["BRIDGE_TICKET_TOYH_0004"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "design_feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_anchor_feasibility.json",
                    "boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_anchor_BOUNDARY_REPORT.json",
                    "mismatch_summary_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json",
                    "mismatch_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
                    "orthogonality_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json",
                },
                "grids": {
                    "theta_values": [1.0471975511965976],
                    "grid_sizes": [7, 9, 11],
                    "local_phase_shear_alpha_values": {"admissible": [1e-06], "inadmissible": [0.0]},
                    "amplitude_scales": {"admissible": [1.0], "inadmissible": [1.1]},
                    "tolerances": {
                        "toyh_tolerance": 1e-10,
                        "current_anchor_tolerance": 1e-07,
                        "current_anchor_min_response": 1e-08,
                    },
                },
                "status": "implemented_bounded",
                "scope_limits": [
                    "compatibility_only",
                    "current_anchor_proxy_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "joint_pair_compatibility_bridge",
                "tickets": ["BRIDGE_TICKET_TOYHG_0001"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "design_feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYHG_C6_pair_compatibility_feasibility.json",
                    "boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYHG_C6_pair_compatibility_BOUNDARY_REPORT.json",
                    "mismatch_summary_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json",
                    "mismatch_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
                    "orthogonality_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json",
                },
                "grids": {
                    "grid_sizes": [7, 9, 11],
                    "primary_probe_ids": ["stress_c6_amplitude_scale"],
                    "secondary_probe_ids": ["baseline_all_pass"],
                    "joint_status_signatures": {
                        "admissible": ["P-P-P", "F-F-F"],
                        "inadmissible": ["P-F-P", "P-P-F", "F-F-P"],
                    },
                    "tolerances": {"pair_signed_margin_pass": 0.0},
                },
                "status": "implemented_bounded",
                "scope_limits": [
                    "compatibility_only",
                    "joint_pair_proxy_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "topological_invariant_feasibility_scan",
                "tickets": ["BRIDGE_FEASIBILITY_TOYG_0001"],
                "inputs": {
                    "feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json",
                    "candidate_targets": ["C6", "C7", "UCFF"],
                },
                "status": "feasible_targets_only_no_bridge_ticket",
                "scope_limits": [
                    "feasibility_only",
                    "ticket_generation_requires_additional_lane",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "topological_phase_winding_quantization",
                "tickets": ["BRIDGE_TICKET_TOYG_0001"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json",
                    "boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_phase_winding_BOUNDARY_REPORT.json",
                },
                "grids": {
                    "loop_length": 6.283185307179586,
                    "grid_sizes": [7, 9, 11],
                    "winding_targets": {"admissible": [1.0], "inadmissible": [1.25]},
                    "tolerances": {"tol_winding": 0.05, "unwrap_margin": 1e-6},
                },
                "scope_limits": [
                    "compatibility_only",
                    "integer_attractor_proxy_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "bridge_program_independence_audit",
                "tickets": [
                    "BRIDGE_TICKET_TOYH_0002",
                    "BRIDGE_TICKET_TOYH_0003",
                    "BRIDGE_TICKET_TOYH_0004",
                    "BRIDGE_TICKET_TOYHG_0001",
                    "BRIDGE_TICKET_TOYG_0001",
                    "BRIDGE_TICKET_TOYG_0002",
                    "BRIDGE_TICKET_TOYG_0003",
                ],
                "inputs": {
                    "orthogonality_report": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json",
                    "mismatch_report": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
                },
                "status": "nonredundancy_audited",
                "scope_limits": [
                    "program_level_bookkeeping_only",
                    "independence_and_mismatch_localization_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "topological_mode_index_quantization",
                "tickets": ["BRIDGE_TICKET_TOYG_0002"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "design_feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json",
                    "boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_mode_index_BOUNDARY_REPORT.json",
                    "program_mismatch_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
                },
                "grids": {
                    "loop_length": 6.283185307179586,
                    "grid_sizes": [7, 9, 11],
                    "mode_targets": {"admissible": [1.0], "inadmissible": [1.25]},
                    "tolerances": {"tol_mode": 0.1, "min_peak_fraction": 0.7},
                },
                "status": "implemented_bounded",
                "scope_limits": [
                    "compatibility_only",
                    "integer_attractor_proxy_only",
                    "no_physics_claim",
                ],
            },
            {
                "bridge_class": "topological_unwrap_stability_compatibility",
                "tickets": ["BRIDGE_TICKET_TOYG_0003"],
                "inputs": {
                    "surfaces": ["formal/python/crft/cp_nlse_2d.py"],
                    "design_feasibility_artifact": "formal/quarantine/feasibility/BRIDGE_TOYG_C6_unwrap_stability_feasibility.json",
                    "boundary_report": "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_unwrap_stability_BOUNDARY_REPORT.json",
                    "mismatch_summary_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json",
                    "mismatch_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
                    "orthogonality_report_source": "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json",
                },
                "grids": {
                    "grid_sizes": [7, 9, 11],
                    "theta_values": [1.0471975511965976],
                    "primary_probe_ids": ["stress_toyg_unwrap"],
                    "secondary_probe_ids": ["stress_toyg_integer"],
                    "tolerances": {
                        "toyg_unwrap_margin": 1e-6,
                        "toyg_tol_winding": 0.05,
                        "toyg_tol_mode": 0.1,
                        "toyg_peak_fraction_min": 0.7,
                        "toyg_tol_unwrap_step_mean": 0.05,
                        "toyg_tol_unwrap_step_std": 0.05,
                        "toyg_min_near_pi_fraction": 0.8,
                        "toyg_pi_edge_eps": 0.15,
                    },
                },
                "status": "implemented_bounded",
                "scope_limits": [
                    "compatibility_only",
                    "unwrap_stability_proxy_only",
                    "no_physics_claim",
                ],
            },
        ],
        "required_evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_ledger_generate_determinism.py::test_bridge_ledger_is_deterministic",
                "formal/python/tests/test_bridge_ledger_evidence_pointers_exist.py::test_bridge_ledger_evidence_pointers_exist",
                "formal/python/tests/test_bridge_boundary_report_generate_determinism.py::test_bridge_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_boundary_report_evidence_pointers_exist.py::test_bridge_boundary_report_evidence_pointers_exist",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance_boundary_report_generate_determinism.py::test_bridge_toyh_c6_phase_invariance_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance_boundary_report_pointers_exist.py::test_bridge_toyh_c6_phase_invariance_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance_boundary_report_generate_determinism.py::test_bridge_toyh_c6_current_invariance_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance_boundary_report_pointers_exist.py::test_bridge_toyh_c6_current_invariance_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_admissibility_manifest_generate_determinism.py::test_bridge_admissibility_manifest_is_deterministic",
                "formal/python/tests/test_bridge_admissibility_manifest_pointers_exist.py::test_bridge_admissibility_manifest_pointers_exist",
                "formal/python/tests/test_bridge_c6_ucff_dispersion_square.py::test_bridge_c6_ucff_omega2_equals_square_of_linear_c6_omega",
                "formal/python/tests/test_bridge_br05_ucff_lowk_slope.py::test_bridge_br05_ucff_lowk_slope_intervals_overlap_and_ucff_can_match",
                "formal/python/tests/test_bridge_br05_ucff_lowk_slope_robustness.py::test_bridge_br05_ucff_lowk_slope_robustness_and_falsification",
                "formal/python/tests/test_bridge_br05_ucff_lowk_curvature.py::test_bridge_br_lowk_window_ucff_omega2_is_convex_on_pinned_grid",
                "formal/python/tests/test_bridge_br05_ucff_lowk_curvature.py::test_bridge_br_lowk_window_ucff_omega2_convexity_negative_control_operator_sanity",
                "formal/python/tests/test_bridge_br05_ucff_lowk_slope_boundary_scan.py::test_bridge_br05_ucff_lowk_slope_boundary_scan",
                "formal/python/tests/test_bridge_br05_ucff_lowk_curvature_grid_density_scan.py::test_bridge_br05_ucff_lowk_curvature_grid_density_scan",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance_feasibility_determinism.py::test_bridge_toyh_c6_phase_invariance_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_invariant_observables",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_negative_control_amplitude_scaling",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_negative_control_phase_sensitive_observable",
                "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_resolution_scan",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance_feasibility_determinism.py::test_bridge_toyh_c6_current_invariance_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_invariant_observables",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_negative_control_amplitude_scaling",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_negative_control_local_phase_shear",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_resolution_scan",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_determinism.py::test_bridge_toyh_c6_phase_anchor_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_pointers_exist.py::test_bridge_toyh_c6_phase_anchor_feasibility_artifact_pointers_exist",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_determinism.py::test_bridge_toyh_c6_phase_anchor_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_determinism.py::test_bridge_toyh_c6_phase_anchor_invariant_observables",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_determinism.py::test_bridge_toyh_c6_phase_anchor_resolves_small_theta_control_case",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_negative_controls.py::test_bridge_toyh_c6_phase_anchor_negative_control_amplitude_scaling",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_negative_controls.py::test_bridge_toyh_c6_phase_anchor_negative_control_wrong_operator_sign",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_resolution_scan.py::test_bridge_toyh_c6_phase_anchor_resolution_scan",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_generate_determinism.py::test_bridge_toyh_c6_phase_anchor_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_pointers_exist.py::test_bridge_toyh_c6_phase_anchor_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_report_generate_determinism.py::test_bridge_toyh_c6_orthogonality_report_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_report_pointers_exist.py::test_bridge_toyh_c6_orthogonality_report_pointers_exist",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_independence.py::test_bridge_toyh_c6_orthogonality_independence",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_report_generate_determinism.py::test_bridge_toyh_c6_orthogonality_mismatch_report_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_report_pointers_exist.py::test_bridge_toyh_c6_orthogonality_mismatch_report_pointers_exist",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_semantics.py::test_bridge_toyh_c6_orthogonality_mismatch_report_contains_only_disagreements",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_semantics.py::test_bridge_toyh_c6_orthogonality_mismatch_report_has_signed_margins_and_reason_codes",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_robustness_guard.py::test_bridge_toyh_c6_orthogonality_nonredundancy_robustness_guard",
                "formal/python/tests/test_bridge_toyg_canonical_feasibility_scan_determinism.py::test_bridge_toyg_canonical_feasibility_scan_is_deterministic",
                "formal/python/tests/test_bridge_toyg_canonical_feasibility_artifact_pointers_exist.py::test_bridge_toyg_canonical_feasibility_artifact_pointers_exist",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_determinism.py::test_bridge_toyg_c6_phase_winding_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_perturbation_stability.py::test_bridge_toyg_c6_phase_winding_perturbation_stability",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py::test_bridge_toyg_c6_phase_winding_negative_control_quantization_failure",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py::test_bridge_toyg_c6_phase_winding_negative_control_wrong_operator_sign",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_resolution_scan.py::test_bridge_toyg_c6_phase_winding_resolution_scan",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_generate_determinism.py::test_bridge_toyg_c6_phase_winding_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_pointers_exist.py::test_bridge_toyg_c6_phase_winding_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_program_orthogonality_report_generate_determinism.py::test_bridge_program_orthogonality_report_is_deterministic",
                "formal/python/tests/test_bridge_program_orthogonality_report_pointers_exist.py::test_bridge_program_orthogonality_report_pointers_exist",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_expected_probe_signatures",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_nonredundancy_summary",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_mode_index_resolves_targeted_winding_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_unwrap_resolves_targeted_bridge_only_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_phase_anchor_resolves_targeted_phase_control_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_current_anchor_resolves_targeted_current_control_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_pair_channel_resolves_targeted_pair_vs_bridge_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_mismatch_report_generate_determinism.py::test_bridge_program_orthogonality_mismatch_report_is_deterministic",
                "formal/python/tests/test_bridge_program_orthogonality_mismatch_report_pointers_exist.py::test_bridge_program_orthogonality_mismatch_report_pointers_exist",
                "formal/python/tests/test_bridge_program_orthogonality_mismatch_semantics.py::test_bridge_program_orthogonality_mismatch_report_contains_only_signature_disagreements",
                "formal/python/tests/test_bridge_program_orthogonality_mismatch_semantics.py::test_bridge_program_orthogonality_mismatch_signed_margins_are_structured",
                "formal/python/tests/test_bridge_program_orthogonality_robustness_guard.py::test_bridge_program_orthogonality_nonredundancy_robustness_guard",
                "formal/python/tests/test_bridge_program_post_toyg0002_regression_lock.py::test_bridge_program_post_toyg0002_regression_lock",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_resolution_regression_lock.py::test_bridge_toyg_c6_mode_index_boundary_and_resolution_lock",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_determinism.py::test_bridge_toyg_c6_mode_index_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist.py::test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_determinism.py::test_bridge_toyg_c6_mode_index_quantization_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_perturbation_stability.py::test_bridge_toyg_c6_mode_index_quantization_perturbation_stability",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_negative_controls.py::test_bridge_toyg_c6_mode_index_quantization_negative_control_integer_closeness_failure",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_negative_controls.py::test_bridge_toyg_c6_mode_index_quantization_negative_control_wrong_operator_sign",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_resolution_scan.py::test_bridge_toyg_c6_mode_index_quantization_resolution_scan",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_generate_determinism.py::test_bridge_toyg_c6_mode_index_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist.py::test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_program_mismatch_reason_summary_determinism.py::test_bridge_program_mismatch_reason_summary_is_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_feasibility_determinism.py::test_bridge_toyg_c6_unwrap_stability_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_feasibility_pointers_exist.py::test_bridge_toyg_c6_unwrap_stability_feasibility_artifact_pointers_exist",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_determinism.py::test_bridge_toyg_c6_unwrap_stability_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_perturbation_stability.py::test_bridge_toyg_c6_unwrap_stability_perturbation_stability",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py::test_bridge_toyg_c6_unwrap_stability_negative_control_not_boundary_sensitive",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py::test_bridge_toyg_c6_unwrap_stability_negative_control_wrong_operator_sign",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_resolution_scan.py::test_bridge_toyg_c6_unwrap_stability_resolution_scan",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_generate_determinism.py::test_bridge_toyg_c6_unwrap_stability_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist.py::test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_resolution_regression_lock.py::test_bridge_toyg_c6_unwrap_resolution_regression_lock",
                "formal/python/tests/test_bridge_program_post_toyh0003_regression_lock.py::test_bridge_program_post_toyh0003_regression_lock",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_invariant_observables",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_resolves_small_alpha_control_case",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_zero_alpha_response_min",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_amplitude_scaling",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_wrong_operator_sign",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_resolution_scan.py::test_bridge_toyh_c6_current_anchor_resolution_scan",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_feasibility_determinism.py::test_bridge_toyh_c6_current_anchor_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_feasibility_pointers_exist.py::test_bridge_toyh_c6_current_anchor_feasibility_artifact_pointers_exist",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_boundary_report_generate_determinism.py::test_bridge_toyh_c6_current_anchor_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_boundary_report_pointers_exist.py::test_bridge_toyh_c6_current_anchor_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_deterministic",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_accepts_uniform_pass_vector",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_phase_current_vs_toyg",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_current_only",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_toyg_only",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_resolution_scan.py::test_bridge_toyhg_c6_pair_compatibility_resolution_signature_map",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_feasibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_feasibility_pointers_exist.py::test_bridge_toyhg_c6_pair_compatibility_feasibility_artifact_pointers_exist",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_boundary_report_generate_determinism.py::test_bridge_toyhg_c6_pair_compatibility_boundary_report_is_deterministic",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_boundary_report_pointers_exist.py::test_bridge_toyhg_c6_pair_compatibility_boundary_report_pointers_exist",
                "formal/python/tests/test_bridge_program_post_toyh0004_regression_lock.py::test_bridge_program_post_toyh0004_regression_lock",
                "formal/python/tests/test_bridge_program_post_toyhg0001_regression_lock.py::test_bridge_program_post_toyhg0001_regression_lock",
            ]
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate the deterministic bridge admissibility manifest JSON (schema v1).")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_ADMISSIBILITY_MANIFEST.json",
        help=(
            "Repo-relative output JSON path (default: formal/quarantine/bridge_tickets/BRIDGE_ADMISSIBILITY_MANIFEST.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_admissibility_manifest_payload(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
