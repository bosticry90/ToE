from __future__ import annotations

"""Toy-law ledger generator (quarantine-safe).

Goal
- Freeze toy-law evidence pointers into a tiny deterministic ledger.

Policy alignment
- Deterministic mapping only (no runtime discovery).
- Bookkeeping only; does not upgrade epistemic status.
- Does not import from the archive directory.

Ledger schema (v1)
{
  "schema": "TOY/toy_law_ledger/v1",
  "items": [
    {
      "toy_law_id": "TOY-A1-viability-gradient-step",
      "front_door": {
        "tool_module": "formal.python.tools.toy_viability_flow_front_door",
        "report_schema": "TOY/viability_gradient_step_report/v1",
        "report_output_path": "formal/output/toy_viability_gradient_step_report.json"
      },
      "evidence": {
        "pytest_nodes": [...],
        "evidence_strength": "bounded_multi"
      },
      "scope_limits": [
        "structure_only; no physics claim",
        "bounded evidence only; consequence engine"
      ]
    }
  ],
  "fingerprint": "..."
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


SCHEMA_ID = "TOY/toy_law_ledger/v1"


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _canonical_json(payload: object) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _items() -> list[dict]:
    return [
        {
            "toy_law_id": "TOY-A1-viability-gradient-step",
            "front_door": {
                "tool_module": "formal.python.tools.toy_viability_flow_front_door",
                "report_schema": "TOY/viability_gradient_step_report/v1",
                "report_output_path": "formal/output/toy_viability_gradient_step_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_viability_flow_front_door_determinism.py::test_toy_viability_flow_front_door_is_deterministic",
                    "formal/python/tests/test_toy_viability_flow_boundary_localization.py::test_toy_viability_flow_boundary_localization_identity_grad",
                    "formal/python/tests/test_toy_viability_flow_negative_controls.py::test_toy_viability_flow_negative_control_wrong_sign",
                    "formal/python/tests/test_toy_viability_flow_negative_controls.py::test_toy_viability_flow_negative_control_parameter_tamper",
                    "formal/python/tests/test_toy_viability_flow_resolution_scan.py::test_toy_viability_flow_resolution_scan_multistep_converges",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-B1-coherence-transport",
            "front_door": {
                "tool_module": "formal.python.tools.toy_coherence_transport_front_door",
                "report_schema": "TOY/coherence_transport_report/v1",
                "report_output_path": "formal/output/toy_coherence_transport_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_coherence_transport_front_door_determinism.py::test_toy_coherence_transport_front_door_is_deterministic",
                    "formal/python/tests/test_toy_coherence_transport_boundary_localization.py::test_toy_coherence_transport_boundary_localization",
                    "formal/python/tests/test_toy_coherence_transport_negative_controls.py::test_toy_coherence_transport_negative_control_wrong_sign",
                    "formal/python/tests/test_toy_coherence_transport_negative_controls.py::test_toy_coherence_transport_negative_control_bad_params",
                    "formal/python/tests/test_toy_coherence_transport_resolution_scan.py::test_toy_coherence_transport_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-B2-coherence-transport-proxy",
            "front_door": {
                "tool_module": "formal.python.tools.toy_coherence_transport_front_door",
                "report_schema": "TOY/coherence_transport_report/v1",
                "report_output_path": "formal/output/toy_coherence_transport_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_coherence_transport_b2_determinism.py::test_toy_coherence_transport_b2_is_deterministic",
                    "formal/python/tests/test_toy_coherence_transport_b2_boundary_localization.py::test_toy_coherence_transport_b2_boundary_localization",
                    "formal/python/tests/test_toy_coherence_transport_b2_negative_controls.py::test_toy_coherence_transport_b2_negative_control_wrong_sign",
                    "formal/python/tests/test_toy_coherence_transport_b2_negative_controls.py::test_toy_coherence_transport_b2_negative_control_bad_params",
                    "formal/python/tests/test_toy_coherence_transport_b2_resolution_scan.py::test_toy_coherence_transport_b2_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-C1-metric-closure",
            "front_door": {
                "tool_module": "formal.python.tools.toy_metric_closure_front_door",
                "report_schema": "TOY/metric_closure_report/v1",
                "report_output_path": "formal/output/toy_metric_closure_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_metric_closure_front_door_determinism.py::test_toy_metric_closure_front_door_is_deterministic",
                    "formal/python/tests/test_toy_metric_closure_boundary_localization.py::test_toy_metric_closure_boundary_localization",
                    "formal/python/tests/test_toy_metric_closure_negative_controls.py::test_toy_metric_closure_negative_control_operator_sanity",
                    "formal/python/tests/test_toy_metric_closure_negative_controls.py::test_toy_metric_closure_negative_control_bad_params",
                    "formal/python/tests/test_toy_metric_closure_resolution_scan.py::test_toy_metric_closure_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-C2-metric-closure-curvature-proxy",
            "front_door": {
                "tool_module": "formal.python.tools.toy_metric_closure_front_door",
                "report_schema": "TOY/metric_closure_report/v1",
                "report_output_path": "formal/output/toy_metric_closure_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_metric_closure_c2_determinism.py::test_toy_metric_closure_c2_is_deterministic",
                    "formal/python/tests/test_toy_metric_closure_c2_boundary_localization.py::test_toy_metric_closure_c2_boundary_localization",
                    "formal/python/tests/test_toy_metric_closure_c2_negative_controls.py::test_toy_metric_closure_c2_negative_control_operator_sanity",
                    "formal/python/tests/test_toy_metric_closure_c2_negative_controls.py::test_toy_metric_closure_c2_negative_control_bad_params",
                    "formal/python/tests/test_toy_metric_closure_c2_negative_controls.py::test_toy_metric_closure_c2_negative_control_bad_state_floor",
                    "formal/python/tests/test_toy_metric_closure_c2_resolution_scan.py::test_toy_metric_closure_c2_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-D1-regime-switching",
            "front_door": {
                "tool_module": "formal.python.tools.toy_regime_switching_front_door",
                "report_schema": "TOY/regime_switching_report/v1",
                "report_output_path": "formal/output/toy_regime_switching_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_regime_switching_front_door_determinism.py::test_toy_regime_switching_front_door_is_deterministic",
                    "formal/python/tests/test_toy_regime_switching_boundary_localization.py::test_toy_regime_switching_boundary_localization",
                    "formal/python/tests/test_toy_regime_switching_negative_controls.py::test_toy_regime_switching_negative_control_inverted_selector",
                    "formal/python/tests/test_toy_regime_switching_negative_controls.py::test_toy_regime_switching_negative_control_bad_params_no_switch",
                    "formal/python/tests/test_toy_regime_switching_resolution_scan.py::test_toy_regime_switching_resolution_scan",
                    "formal/python/tests/test_toy_regime_switching_hysteresis_protocol.py::test_toy_regime_switching_hysteresis_protocol",
                    "formal/python/tests/test_toy_regime_switching_hysteresis_protocol.py::test_toy_regime_switching_hysteresis_negative_control_swapped_thresholds",
                    "formal/python/tests/test_toy_regime_switching_hysteresis_protocol.py::test_toy_regime_switching_hysteresis_negative_control_no_gap",
                    "formal/python/tests/test_toy_regime_switching_hysteresis_robustness_guard.py::test_toy_regime_switching_hysteresis_robustness_guard",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-E1-scale-flow",
            "front_door": {
                "tool_module": "formal.python.tools.toy_scale_flow_front_door",
                "report_schema": "TOY/scale_flow_report/v1",
                "report_output_path": "formal/output/toy_scale_flow_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_scale_flow_front_door_determinism.py::test_toy_scale_flow_front_door_is_deterministic",
                    "formal/python/tests/test_toy_scale_flow_boundary_localization.py::test_toy_scale_flow_boundary_localization",
                    "formal/python/tests/test_toy_scale_flow_negative_controls.py::test_toy_scale_flow_negative_control_operator_sanity",
                    "formal/python/tests/test_toy_scale_flow_negative_controls.py::test_toy_scale_flow_negative_control_bad_params",
                    "formal/python/tests/test_toy_scale_flow_resolution_scan.py::test_toy_scale_flow_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-F1-stochastic-selection",
            "front_door": {
                "tool_module": "formal.python.tools.toy_stochastic_selection_front_door",
                "report_schema": "TOY/stochastic_selection_report/v1",
                "report_output_path": "formal/output/toy_stochastic_selection_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_stochastic_selection_front_door_determinism.py::test_toy_stochastic_selection_front_door_is_deterministic",
                    "formal/python/tests/test_toy_stochastic_selection_boundary_localization.py::test_toy_stochastic_selection_boundary_localization",
                    "formal/python/tests/test_toy_stochastic_selection_negative_controls.py::test_toy_stochastic_selection_negative_control_operator_sanity",
                    "formal/python/tests/test_toy_stochastic_selection_negative_controls.py::test_toy_stochastic_selection_negative_control_noise_disabled",
                    "formal/python/tests/test_toy_stochastic_selection_resolution_scan.py::test_toy_stochastic_selection_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-G1-topological-invariants",
            "front_door": {
                "tool_module": "formal.python.tools.toy_topological_invariants_front_door",
                "report_schema": "TOY/topological_invariants_report/v1",
                "report_output_path": "formal/output/toy_topological_invariants_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_topological_invariants_front_door_determinism.py::test_toy_topological_invariants_front_door_is_deterministic",
                    "formal/python/tests/test_toy_topological_invariants_perturbation_stability.py::test_toy_topological_invariants_perturbation_stability",
                    "formal/python/tests/test_toy_topological_invariants_negative_controls.py::test_toy_topological_invariants_negative_control_wrong_detector",
                    "formal/python/tests/test_toy_topological_invariants_negative_controls.py::test_toy_topological_invariants_negative_control_wrong_update",
                    "formal/python/tests/test_toy_topological_invariants_resolution_scan.py::test_toy_topological_invariants_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-H1-gauge-redundancy",
            "front_door": {
                "tool_module": "formal.python.tools.toy_gauge_redundancy_front_door",
                "report_schema": "TOY/gauge_redundancy_report/v1",
                "report_output_path": "formal/output/toy_gauge_redundancy_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_gauge_redundancy_front_door_determinism.py::test_toy_gauge_redundancy_front_door_is_deterministic",
                    "formal/python/tests/test_toy_gauge_redundancy_invariance.py::test_toy_gauge_redundancy_invariance",
                    "formal/python/tests/test_toy_gauge_redundancy_negative_controls.py::test_toy_gauge_redundancy_negative_control_wrong_transform",
                    "formal/python/tests/test_toy_gauge_redundancy_negative_controls.py::test_toy_gauge_redundancy_negative_control_noninvariant_observable",
                    "formal/python/tests/test_toy_gauge_redundancy_resolution_scan.py::test_toy_gauge_redundancy_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
        {
            "toy_law_id": "TOY-H2-gauge-redundancy-local",
            "front_door": {
                "tool_module": "formal.python.tools.toy_gauge_redundancy_front_door",
                "report_schema": "TOY/gauge_redundancy_report/v1",
                "report_output_path": "formal/output/toy_gauge_redundancy_report.json",
            },
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_toy_gauge_redundancy_h2_determinism.py::test_toy_gauge_redundancy_h2_is_deterministic",
                    "formal/python/tests/test_toy_gauge_redundancy_h2_invariance.py::test_toy_gauge_redundancy_h2_invariance_local_gauge",
                    "formal/python/tests/test_toy_gauge_redundancy_h2_negative_controls.py::test_toy_gauge_redundancy_h2_negative_control_wrong_transform",
                    "formal/python/tests/test_toy_gauge_redundancy_h2_negative_controls.py::test_toy_gauge_redundancy_h2_negative_control_noninvariant_observable",
                    "formal/python/tests/test_toy_gauge_redundancy_h2_resolution_scan.py::test_toy_gauge_redundancy_h2_resolution_scan",
                ],
                "evidence_strength": "bounded_multi",
            },
            "scope_limits": [
                "structure_only; no physics claim",
                "bounded evidence only; consequence engine",
            ],
        },
    ]


def build_toy_law_ledger_payload(*, repo_root: Path) -> dict:
    _ = repo_root
    payload = {
        "schema": SCHEMA_ID,
        "items": _items(),
    }

    payload["fingerprint"] = _sha256_text(_canonical_json(payload))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate the deterministic toy-law ledger JSON (schema v1).")
    p.add_argument(
        "--out",
        default="formal/quarantine/toy_laws/TOY_LAW_LEDGER.json",
        help="Repo-relative output JSON path (default: formal/quarantine/toy_laws/TOY_LAW_LEDGER.json)",
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_toy_law_ledger_payload(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
