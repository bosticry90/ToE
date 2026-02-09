# BRIDGE_TICKET_TOYG_0002 — C6 mode-index quantization proxy (Toy-G)

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-04

## Bridge family taxonomy (governance; docs-only)

- Bridge class: topological_mode_index_quantization
- Evidence strength: bounded_multi
- Degrees of freedom: loop length pinned; grid sizes bounded; mode targets pinned; integer-closeness + peak-fraction thresholds pinned
- Falsification mode: mode-index admissibility fails on pinned quantized targets or passes on pinned non-quantized controls
- Non-implication clause: passing implies only structural compatibility of a discrete mode-index proxy on the canonical C6 surface; it does not imply physical quantization or empirical anchoring

## Claim (falsifiable; structural)

Given the canonical C6 CP-NLSE 2D surface and a pinned periodic loop specimen, the dominant FFT mode index is an admissible integer-attractor proxy when the mode target is pinned to a quantized value, remains stable under pinned small perturbations, and fails under pinned non-quantized controls.

This is a **structural compatibility** statement only. It does **not** assert physical quantization.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`
- Feasibility gate: `formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json`

## Admissibility rule (pinned)

- `abs(mode_target - nearest_int) <= tol_mode`
- `peak_index_signed == nearest_int`
- `peak_fraction >= min_peak_fraction`

where `peak_index_signed` is the signed argmax bin of `|FFT(psi_loop)|^2` on the pinned periodic loop.

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_determinism.py::test_bridge_toyg_c6_mode_index_quantization_deterministic`
- `formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_perturbation_stability.py::test_bridge_toyg_c6_mode_index_quantization_perturbation_stability`
- `formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_negative_controls.py::test_bridge_toyg_c6_mode_index_quantization_negative_control_integer_closeness_failure`
- `formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_negative_controls.py::test_bridge_toyg_c6_mode_index_quantization_negative_control_wrong_operator_sign`
- `formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_resolution_scan.py::test_bridge_toyg_c6_mode_index_quantization_resolution_scan`
- `formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_generate_determinism.py::test_bridge_toyg_c6_mode_index_boundary_report_is_deterministic`
- `formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist.py::test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist`

## Boundary report artifact

- `formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_mode_index_BOUNDARY_REPORT.json`

## Program-level impact check

- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`

Expected impact under pinned probes:
- program-level `nonredundant` remains true
- Toy-G `fail_not_integer_close` winding mismatch region is reduced by mode-index bridge support

## Exit condition

- Passes deterministically under pinned admissibility rules and retains clean fail localization under controls.

## Failure posture

- If the admissibility rule fails for pinned quantized probes, or passes for pinned non-quantized controls, this ticket is eliminated under current surfaces.
