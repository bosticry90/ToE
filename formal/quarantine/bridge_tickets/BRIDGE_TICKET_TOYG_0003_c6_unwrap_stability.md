# BRIDGE_TICKET_TOYG_0003 — C6 unwrap-stability proxy (Toy-G)

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-04

## Bridge family taxonomy (governance; docs-only)

- Bridge class: topological_unwrap_stability_compatibility
- Evidence strength: bounded_multi
- Degrees of freedom: loop length pinned; grid sizes bounded; unwrap targets pinned; unwrap thresholds pinned
- Falsification mode: unwrap-stability admissibility fails on pinned boundary-sensitive probes or passes on pinned non-boundary controls
- Non-implication clause: passing implies only structural compatibility of an unwrap-stability proxy on the canonical C6 surface; it does not imply physical quantization or empirical anchoring

## Claim (falsifiable; structural)

Given the canonical C6 CP-NLSE 2D surface and a pinned periodic loop specimen, a boundary-sensitive unwrap-stability observable can remain admissible on pinned unwrap-target probes, fail cleanly on pinned non-boundary controls, and provide an additional nonredundant Toy-G compatibility channel.

This is a **structural compatibility** statement only. It does **not** assert physical quantization.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`
- Pre-gate feasibility: `formal/quarantine/feasibility/BRIDGE_TOYG_C6_unwrap_stability_feasibility.json`

## Admissibility rule (pinned)

- `near_pi_fraction >= min_near_pi_fraction`
- `mean_abs_step_error <= tol_step_mean`
- `step_std <= tol_step_std`

where principal phase increments are computed on the periodic loop and compared against the pinned unwrap-target step profile.

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyg_c6_unwrap_stability_determinism.py::test_bridge_toyg_c6_unwrap_stability_deterministic`
- `formal/python/tests/test_bridge_toyg_c6_unwrap_stability_perturbation_stability.py::test_bridge_toyg_c6_unwrap_stability_perturbation_stability`
- `formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py::test_bridge_toyg_c6_unwrap_stability_negative_control_not_boundary_sensitive`
- `formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py::test_bridge_toyg_c6_unwrap_stability_negative_control_wrong_operator_sign`
- `formal/python/tests/test_bridge_toyg_c6_unwrap_stability_resolution_scan.py::test_bridge_toyg_c6_unwrap_stability_resolution_scan`
- `formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_generate_determinism.py::test_bridge_toyg_c6_unwrap_stability_boundary_report_is_deterministic`
- `formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist.py::test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist`

## Boundary report artifact

- `formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_unwrap_stability_BOUNDARY_REPORT.json`

## Program-level impact check

- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`

Expected impact under pinned probes:
- program-level `nonredundant` remains true
- the previous `mismatch_toyg_bridge_only` region is resolved by the unwrap channel under pinned probes

## Exit condition

- Passes deterministically under pinned admissibility rules and retains clean fail localization under controls.

## Failure posture

- If the admissibility rule fails for pinned unwrap-target probes, or passes for pinned non-boundary controls, this ticket is eliminated under current surfaces.
