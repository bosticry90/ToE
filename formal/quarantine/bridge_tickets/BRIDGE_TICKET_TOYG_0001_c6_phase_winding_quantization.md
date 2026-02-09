# BRIDGE_TICKET_TOYG_0001 — C6 phase-winding quantization proxy (Toy-G)

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-04

## Bridge family taxonomy (governance; docs-only)

- Bridge class: topological_phase_winding_quantization
- Evidence strength: bounded_multi
- Degrees of freedom: loop length pinned; grid sizes bounded; winding targets pinned; tolerances pinned
- Falsification mode: phase-winding admissibility fails on pinned quantized targets or passes on pinned non-quantized controls
- Non-implication clause: passing implies only structural compatibility of a discrete winding proxy on the canonical C6 surface; it does not imply physical quantization or empirical anchoring

## Claim (falsifiable; structural)

Given the canonical C6 CP-NLSE 2D surface and a pinned periodic loop specimen, the phase winding

    w = round(Theta / 2pi),   Theta = sum_i principal_unwrap(arg(psi_{i+1}) - arg(psi_i))

is admissible as an integer-attractor proxy when the winding target is pinned to a quantized value, remains stable under pinned small perturbations, and fails under pinned non-quantized controls.

This is a **structural compatibility** statement only. It does **not** assert physical quantization.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`
- Feasibility gate: `formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json`

## Admissibility rule (pinned)

- `abs(raw_winding - nearest_int) <= tol_winding`
- `max_abs_delta <= pi - unwrap_margin`

where `raw_winding = Theta/(2pi)` and `nearest_int = round(raw_winding)`.

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyg_c6_phase_winding_determinism.py::test_bridge_toyg_c6_phase_winding_deterministic`
- `formal/python/tests/test_bridge_toyg_c6_phase_winding_perturbation_stability.py::test_bridge_toyg_c6_phase_winding_perturbation_stability`
- `formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py::test_bridge_toyg_c6_phase_winding_negative_control_quantization_failure`
- `formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py::test_bridge_toyg_c6_phase_winding_negative_control_wrong_operator_sign`
- `formal/python/tests/test_bridge_toyg_c6_phase_winding_resolution_scan.py::test_bridge_toyg_c6_phase_winding_resolution_scan`
- `formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_generate_determinism.py::test_bridge_toyg_c6_phase_winding_boundary_report_is_deterministic`
- `formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_pointers_exist.py::test_bridge_toyg_c6_phase_winding_boundary_report_pointers_exist`

## Boundary report artifact

- `formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_phase_winding_BOUNDARY_REPORT.json`

## Exit condition

- Passes deterministically under pinned admissibility rules and retains clean fail localization under controls.

## Failure posture

- If the admissibility rule fails for pinned quantized probes, or passes for pinned non-quantized controls, this ticket is eliminated under current surfaces.
