# BRIDGE_TICKET_TOYH_0002 — C6 current invariance (Toy-H orthogonal gauge bridge)

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-04

## Bridge family taxonomy (governance; docs-only)

- Bridge class: gauge_current_invariance_compatibility
- Evidence strength: bounded_multi
- Degrees of freedom: global phase theta pinned; local phase-shear alpha pinned; plane-wave initial condition pinned; grid sizes bounded
- Falsification mode: pytest node failure eliminates this mapping under current canonical surfaces
- Non-implication clause: passing implies only structural compatibility under the stated mapping; it does not imply physical truth or empirical anchoring

## Claim (falsifiable; structural)

Given the canonical C6 CP-NLSE 2D surface, global phase rotation of the pinned plane-wave initial condition

    phi0 -> e^{i theta} phi0

should preserve a second, orthogonal gauge-compatible observable: the L2 magnitude of the derived current field.

This is a **structural compatibility** statement only. It does **not** assert physical equivalence or empirical anchoring.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_deterministic`
- `formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_invariant_observables`
- `formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_negative_control_amplitude_scaling`
- `formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_negative_control_local_phase_shear`
- `formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_resolution_scan`

## Exit condition

- Passes deterministically.

## Failure posture

- If the test fails, the ticket is **Eliminated** (the structural mapping is not supported under current surfaces).
