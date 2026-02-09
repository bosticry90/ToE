# BRIDGE_TICKET_TOYH_0001 — C6 phase invariance (toy gauge redundancy bridge)

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-03

## Bridge family taxonomy (governance; docs-only)

- Bridge class: gauge_invariance_compatibility
- Evidence strength: bounded_multi
- Degrees of freedom: global phase theta pinned; plane-wave initial condition pinned; grid sizes bounded
- Falsification mode: pytest node failure eliminates this mapping under current canonical surfaces
- Non-implication clause: passing implies only structural compatibility under the stated mapping; it does not imply physical truth or empirical anchoring

## Claim (falsifiable; structural)

Given the canonical C6 CP–NLSE 2D surface, global phase rotation of the pinned plane-wave initial condition

    phi0 -> e^{i theta} phi0

should preserve phase-invariant diagnostics (norm, energy, rhs equivariance) under the stated deterministic checks.

This is a **structural compatibility** statement only. It does **not** assert physical equivalence or empirical anchoring.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_deterministic`
- `formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_invariant_observables`
- `formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_negative_control_amplitude_scaling`
- `formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_negative_control_phase_sensitive_observable`
- `formal/python/tests/test_bridge_toyh_c6_phase_invariance.py::test_bridge_toyh_c6_phase_invariance_resolution_scan`

## Exit condition

- Passes deterministically.

## Failure posture

- If the test fails, the ticket is **Eliminated** (the structural mapping is not supported under current surfaces).
