from __future__ import annotations

"""Bridge ledger generator (quarantine-safe).

Goal
- Freeze the current bridge-ticket family (BRIDGE_TICKET_0001+) into a tiny,
  deterministic JSON ledger with explicit evidence pointers.

Policy alignment
- Deterministic mapping only (no runtime discovery).
- Bookkeeping only; does not upgrade epistemic status.
- Does not import from the archive directory.

Ledger schema (v1)
{
  "schema_version": 1,
  "items": [
    {
      "ticket_id": "BRIDGE_TICKET_0001",
      "ticket_path": "formal/quarantine/bridge_tickets/...md",
      "ticket_sha256": "...",
      "bridge_class": "algebraic_relation",
      "evidence_strength": "bounded_single|bounded_guard",
      "evidence": {"pytest_nodes": ["path/to/test.py::test_fn"]},
      "inputs": {"locks": [...], "contracts": [...]},
      "canonical_surfaces": [...],
      "degrees_of_freedom": [...],
      "falsification_mode": "...",
      "scope_limits": [...]
    }
  ],
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


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _ticket_items(repo_root: Path) -> list[dict]:
    """Deterministic ticket registry.

    IMPORTANT: This is intentionally static (no runtime discovery).
    If you add a new bridge ticket, extend this mapping explicitly.
    """

    t1 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_0001_c6_ucff_dispersion_square.md"
    t2 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_0002_br05_ucff_lowk_slope.md"
    t3 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_0003_br05_ucff_lowk_slope_robustness.md"
    t4 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_0004_br05_ucff_lowk_curvature.md"
    t5 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0001_c6_phase_invariance.md"
    t6 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0002_c6_current_invariance.md"
    t7 = "formal/quarantine/bridge_tickets/BRIDGE_FEASIBILITY_TOYG_0001_canonical_surface_scan.md"
    t8 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYG_0001_c6_phase_winding_quantization.md"
    t9 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYG_0002_c6_mode_index_quantization.md"
    t10 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYG_0003_c6_unwrap_stability.md"
    t11 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0003_c6_phase_anchor.md"
    t12 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0004_c6_current_anchor.md"
    t13 = "formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYHG_0001_c6_pair_compatibility.md"

    return [
        {
            "ticket_id": "BRIDGE_TICKET_0001",
            "ticket_path": t1,
            "ticket_sha256": _sha256_path(repo_root / t1),
            "bridge_class": "algebraic_relation",
            "evidence_strength": "bounded_single",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_c6_ucff_dispersion_square.py::test_bridge_c6_ucff_omega2_equals_square_of_linear_c6_omega"
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py", "formal/python/toe/ucff/core_front_door.py"],
            "degrees_of_freedom": ["none"],
            "falsification_mode": "pytest node failure eliminates this mapping under current canonical surfaces",
            "scope_limits": ["bounded", "structural_only", "no_physics_claim", "no_empirical_claim"],
        },
        {
            "ticket_id": "BRIDGE_TICKET_0002",
            "ticket_path": t2,
            "ticket_sha256": _sha256_path(repo_root / t2),
            "bridge_class": "regime_local_compatibility_existence",
            "evidence_strength": "bounded_single",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_br05_ucff_lowk_slope.py::test_bridge_br05_ucff_lowk_slope_intervals_overlap_and_ucff_can_match"
                ]
            },
            "inputs": {
                "locks": ["formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md"],
                "contracts": ["formal/docs/ucff_core_front_door_contract.md"],
            },
            "canonical_surfaces": ["formal/python/toe/ucff/core_front_door.py"],
            "degrees_of_freedom": ["deterministic c_star selection from Bragg 1-sigma overlap; set g=c_star^2"],
            "falsification_mode": "empty Bragg overlap eliminates ticket; inability to reproduce chosen low-k slope eliminates mapping",
            "scope_limits": ["bounded", "structural_only", "external_anchor_via_OV_BR_05", "no_units_claim"],
        },
        {
            "ticket_id": "BRIDGE_TICKET_0003",
            "ticket_path": t3,
            "ticket_sha256": _sha256_path(repo_root / t3),
            "bridge_class": "robustness_guard",
            "evidence_strength": "bounded_guard",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_br05_ucff_lowk_slope_robustness.py::test_bridge_br05_ucff_lowk_slope_robustness_and_falsification"
                ]
            },
            "inputs": {
                "locks": ["formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md"],
                "contracts": ["formal/docs/ucff_core_front_door_contract.md"],
            },
            "canonical_surfaces": ["formal/python/toe/ucff/core_front_door.py"],
            "degrees_of_freedom": ["none (deterministic interior/exterior sampling from overlap endpoints)"],
            "falsification_mode": "exterior samples must violate Bragg-window compatibility; interior samples must succeed reproducibly",
            "scope_limits": ["bounded", "guard_only", "structural_only", "no_status_upgrade"],
        },
        {
            "ticket_id": "BRIDGE_TICKET_0004",
            "ticket_path": t4,
            "ticket_sha256": _sha256_path(repo_root / t4),
            "bridge_class": "shape_constraint_curvature_convexity",
            "evidence_strength": "bounded_single",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_br05_ucff_lowk_curvature.py::test_bridge_br_lowk_window_ucff_omega2_is_convex_on_pinned_grid",
                    "formal/python/tests/test_bridge_br05_ucff_lowk_curvature.py::test_bridge_br_lowk_window_ucff_omega2_convexity_negative_control_operator_sanity",
                ]
            },
            "inputs": {
                "locks": [
                    "formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md",
                    "formal/markdown/locks/observables/OV-BR-04b_bragg_lowk_slope_conditionB_OVERRIDE.md",
                ],
                "contracts": ["formal/docs/ucff_core_front_door_contract.md"],
            },
            "canonical_surfaces": ["formal/python/toe/ucff/core_front_door.py"],
            "degrees_of_freedom": ["none"],
            "falsification_mode": "negative discrete second difference beyond tolerance eliminates mapping",
            "scope_limits": ["bounded", "structural_only", "shape_constraint_only", "no_units_claim"],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYH_0001",
            "ticket_path": t5,
            "ticket_sha256": _sha256_path(repo_root / t5),
            "bridge_class": "gauge_invariance_compatibility",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_invariant_observables",
                    "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_negative_control_amplitude_scaling",
                    "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_negative_control_phase_sensitive_observable",
                    "formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_resolution_scan",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "global phase theta pinned",
                "plane-wave initial condition pinned",
                "grid sizes bounded",
            ],
            "falsification_mode": "phase invariance checks fail under pinned transforms",
            "scope_limits": ["bounded", "structural_only", "symmetry_only", "no_physics_claim"],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYH_0002",
            "ticket_path": t6,
            "ticket_sha256": _sha256_path(repo_root / t6),
            "bridge_class": "gauge_current_invariance_compatibility",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_invariant_observables",
                    "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_negative_control_amplitude_scaling",
                    "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_negative_control_local_phase_shear",
                    "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_resolution_scan",
                    "formal/python/tests/test_bridge_toyh_c6_orthogonality_independence.py::test_bridge_toyh_c6_orthogonality_independence",
                    "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_semantics.py::test_bridge_toyh_c6_orthogonality_mismatch_report_contains_only_disagreements",
                    "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_semantics.py::test_bridge_toyh_c6_orthogonality_mismatch_report_has_signed_margins_and_reason_codes",
                    "formal/python/tests/test_bridge_toyh_c6_orthogonality_robustness_guard.py::test_bridge_toyh_c6_orthogonality_nonredundancy_robustness_guard",
                    "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_nonredundancy_summary",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "global phase theta pinned",
                "local phase shear alpha pinned",
                "plane-wave initial condition pinned",
                "grid sizes bounded",
            ],
            "falsification_mode": "current invariance checks fail under pinned transforms",
            "scope_limits": ["bounded", "structural_only", "current_observable_only", "no_physics_claim"],
        },
        {
            "ticket_id": "BRIDGE_FEASIBILITY_TOYG_0001",
            "ticket_path": t7,
            "ticket_sha256": _sha256_path(repo_root / t7),
            "bridge_class": "topological_invariant_feasibility_scan",
            "evidence_strength": "bounded_feasibility",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyg_canonical_feasibility_scan_determinism.py::test_bridge_toyg_canonical_feasibility_scan_is_deterministic",
                    "formal/python/tests/test_bridge_toyg_canonical_feasibility_artifact_pointers_exist.py::test_bridge_toyg_canonical_feasibility_artifact_pointers_exist",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": [
                "formal/python/crft/cp_nlse_2d.py",
                "formal/python/crft/acoustic_metric.py",
                "formal/python/toe/ucff/core_front_door.py",
            ],
            "degrees_of_freedom": ["none (target set pinned to C6/C7/UCFF capability scan)"],
            "falsification_mode": "feasibility scan reports found=false for all canonical targets",
            "scope_limits": [
                "bounded",
                "feasibility_only",
                "no_bridge_ticket_generated",
                "no_physics_claim",
            ],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYG_0001",
            "ticket_path": t8,
            "ticket_sha256": _sha256_path(repo_root / t8),
            "bridge_class": "topological_phase_winding_quantization",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyg_c6_phase_winding_determinism.py::test_bridge_toyg_c6_phase_winding_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_phase_winding_perturbation_stability.py::test_bridge_toyg_c6_phase_winding_perturbation_stability",
                    "formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py::test_bridge_toyg_c6_phase_winding_negative_control_quantization_failure",
                    "formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py::test_bridge_toyg_c6_phase_winding_negative_control_wrong_operator_sign",
                    "formal/python/tests/test_bridge_toyg_c6_phase_winding_resolution_scan.py::test_bridge_toyg_c6_phase_winding_resolution_scan",
                    "formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_generate_determinism.py::test_bridge_toyg_c6_phase_winding_boundary_report_is_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_pointers_exist.py::test_bridge_toyg_c6_phase_winding_boundary_report_pointers_exist",
                    "formal/python/tests/test_bridge_program_orthogonality_report_generate_determinism.py::test_bridge_program_orthogonality_report_is_deterministic",
                    "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_expected_probe_signatures",
                    "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_nonredundancy_summary",
                    "formal/python/tests/test_bridge_program_orthogonality_mismatch_report_generate_determinism.py::test_bridge_program_orthogonality_mismatch_report_is_deterministic",
                    "formal/python/tests/test_bridge_program_orthogonality_mismatch_semantics.py::test_bridge_program_orthogonality_mismatch_report_contains_only_signature_disagreements",
                    "formal/python/tests/test_bridge_program_orthogonality_mismatch_semantics.py::test_bridge_program_orthogonality_mismatch_signed_margins_are_structured",
                    "formal/python/tests/test_bridge_program_orthogonality_robustness_guard.py::test_bridge_program_orthogonality_nonredundancy_robustness_guard",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "loop length pinned",
                "winding target pinned",
                "grid sizes bounded",
                "tolerance and unwrap guard pinned",
            ],
            "falsification_mode": "phase-winding admissibility fails on pinned quantized probes or passes on pinned non-quantized probes",
            "scope_limits": [
                "bounded",
                "structural_only",
                "topological_proxy_only",
                "no_physics_claim",
            ],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYG_0002",
            "ticket_path": t9,
            "ticket_sha256": _sha256_path(repo_root / t9),
            "bridge_class": "topological_mode_index_quantization",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_determinism.py::test_bridge_toyg_c6_mode_index_quantization_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_perturbation_stability.py::test_bridge_toyg_c6_mode_index_quantization_perturbation_stability",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_negative_controls.py::test_bridge_toyg_c6_mode_index_quantization_negative_control_integer_closeness_failure",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_negative_controls.py::test_bridge_toyg_c6_mode_index_quantization_negative_control_wrong_operator_sign",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_resolution_scan.py::test_bridge_toyg_c6_mode_index_quantization_resolution_scan",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_generate_determinism.py::test_bridge_toyg_c6_mode_index_boundary_report_is_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist.py::test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist",
                    "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_mode_index_resolves_targeted_winding_mismatch",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "periodic loop length pinned",
                "mode targets pinned",
                "integer-closeness and peak-fraction thresholds pinned",
                "grid sizes bounded",
            ],
            "falsification_mode": "mode-index admissibility fails on pinned quantized probes or passes on pinned non-quantized controls",
            "scope_limits": [
                "bounded",
                "structural_only",
                "topological_proxy_only",
                "no_physics_claim",
            ],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYG_0003",
            "ticket_path": t10,
            "ticket_sha256": _sha256_path(repo_root / t10),
            "bridge_class": "topological_unwrap_stability_compatibility",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_determinism.py::test_bridge_toyg_c6_unwrap_stability_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_perturbation_stability.py::test_bridge_toyg_c6_unwrap_stability_perturbation_stability",
                    "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py::test_bridge_toyg_c6_unwrap_stability_negative_control_not_boundary_sensitive",
                    "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py::test_bridge_toyg_c6_unwrap_stability_negative_control_wrong_operator_sign",
                    "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_resolution_scan.py::test_bridge_toyg_c6_unwrap_stability_resolution_scan",
                    "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_generate_determinism.py::test_bridge_toyg_c6_unwrap_stability_boundary_report_is_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist.py::test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist",
                    "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_unwrap_resolves_targeted_bridge_only_mismatch",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "periodic loop length pinned",
                "unwrap targets pinned",
                "unwrap thresholds pinned",
                "grid sizes bounded",
            ],
            "falsification_mode": "unwrap-stability admissibility fails on pinned boundary-sensitive probes or passes on non-boundary controls",
            "scope_limits": [
                "bounded",
                "structural_only",
                "topological_proxy_only",
                "no_physics_claim",
            ],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYH_0003",
            "ticket_path": t11,
            "ticket_sha256": _sha256_path(repo_root / t11),
            "bridge_class": "gauge_phase_anchor_compatibility",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_determinism.py::test_bridge_toyh_c6_phase_anchor_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_determinism.py::test_bridge_toyh_c6_phase_anchor_invariant_observables",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_determinism.py::test_bridge_toyh_c6_phase_anchor_resolves_small_theta_control_case",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_negative_controls.py::test_bridge_toyh_c6_phase_anchor_negative_control_amplitude_scaling",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_negative_controls.py::test_bridge_toyh_c6_phase_anchor_negative_control_wrong_operator_sign",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_resolution_scan.py::test_bridge_toyh_c6_phase_anchor_resolution_scan",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_generate_determinism.py::test_bridge_toyh_c6_phase_anchor_boundary_report_is_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_pointers_exist.py::test_bridge_toyh_c6_phase_anchor_boundary_report_pointers_exist",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_determinism.py::test_bridge_toyh_c6_phase_anchor_feasibility_is_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_pointers_exist.py::test_bridge_toyh_c6_phase_anchor_feasibility_artifact_pointers_exist",
                    "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_phase_anchor_resolves_targeted_phase_control_mismatch",
                    "formal/python/tests/test_bridge_program_post_toyh0003_regression_lock.py::test_bridge_program_post_toyh0003_regression_lock",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "global phase theta pinned",
                "phase-anchor tolerance pinned",
                "amplitude scaling controls pinned",
                "grid sizes bounded",
            ],
            "falsification_mode": "phase-anchor admissibility fails for pinned small-theta probes or passes under pinned wrong-operator controls",
            "scope_limits": [
                "bounded",
                "structural_only",
                "phase_anchor_proxy_only",
                "no_physics_claim",
            ],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYH_0004",
            "ticket_path": t12,
            "ticket_sha256": _sha256_path(repo_root / t12),
            "bridge_class": "gauge_current_anchor_compatibility",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_invariant_observables",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_resolves_small_alpha_control_case",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_zero_alpha_response_min",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_amplitude_scaling",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_wrong_operator_sign",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_resolution_scan.py::test_bridge_toyh_c6_current_anchor_resolution_scan",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_boundary_report_generate_determinism.py::test_bridge_toyh_c6_current_anchor_boundary_report_is_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_boundary_report_pointers_exist.py::test_bridge_toyh_c6_current_anchor_boundary_report_pointers_exist",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_feasibility_determinism.py::test_bridge_toyh_c6_current_anchor_feasibility_is_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_current_anchor_feasibility_pointers_exist.py::test_bridge_toyh_c6_current_anchor_feasibility_artifact_pointers_exist",
                    "formal/python/tests/test_bridge_program_post_toyh0004_regression_lock.py::test_bridge_program_post_toyh0004_regression_lock",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "global phase theta pinned",
                "local phase shear alpha pinned",
                "current-anchor tolerance pinned",
                "grid sizes bounded",
            ],
            "falsification_mode": "current-anchor admissibility fails for pinned tiny-shear probes or passes under wrong-operator controls",
            "scope_limits": [
                "bounded",
                "structural_only",
                "current_anchor_proxy_only",
                "no_physics_claim",
            ],
        },
        {
            "ticket_id": "BRIDGE_TICKET_TOYHG_0001",
            "ticket_path": t13,
            "ticket_sha256": _sha256_path(repo_root / t13),
            "bridge_class": "joint_pair_compatibility_bridge",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_deterministic",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_accepts_uniform_pass_vector",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_phase_current_vs_toyg",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_current_only",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_toyg_only",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_resolution_scan.py::test_bridge_toyhg_c6_pair_compatibility_resolution_signature_map",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_boundary_report_generate_determinism.py::test_bridge_toyhg_c6_pair_compatibility_boundary_report_is_deterministic",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_boundary_report_pointers_exist.py::test_bridge_toyhg_c6_pair_compatibility_boundary_report_pointers_exist",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_feasibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_feasibility_is_deterministic",
                    "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_feasibility_pointers_exist.py::test_bridge_toyhg_c6_pair_compatibility_feasibility_artifact_pointers_exist",
                    "formal/python/tests/test_bridge_program_post_toyhg0001_regression_lock.py::test_bridge_program_post_toyhg0001_regression_lock",
                ]
            },
            "inputs": {"locks": [], "contracts": []},
            "canonical_surfaces": ["formal/python/crft/cp_nlse_2d.py"],
            "degrees_of_freedom": [
                "joint pass/fail signature map pinned",
                "localization rule pinned",
                "probe set bounded",
            ],
            "falsification_mode": "pair channel admits inconsistent signatures or rejects consistent signatures under pinned inputs",
            "scope_limits": [
                "bounded",
                "structural_only",
                "joint_pair_proxy_only",
                "no_physics_claim",
            ],
        },
    ]


def build_bridge_ledger_payload(*, repo_root: Path) -> dict:
    items = _ticket_items(repo_root)

    payload = {
        "schema_version": 1,
        "items": items,
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate the deterministic bridge ledger JSON (schema v1).")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_LEDGER.json",
        help="Repo-relative output JSON path (default: formal/quarantine/bridge_tickets/BRIDGE_LEDGER.json)",
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_ledger_payload(repo_root=repo_root)

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
