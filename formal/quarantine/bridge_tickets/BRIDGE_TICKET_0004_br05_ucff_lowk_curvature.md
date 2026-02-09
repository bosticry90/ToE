# BRIDGE_TICKET_0004 — BR low-k window ↔ UCFF curvature/convexity constraint (bounded)

Created: 2026-02-01
Status: Active (structural-only; falsifiable; bounded)

## Bridge family taxonomy (governance; docs-only)

- Bridge class: shape constraint (curvature/convexity)
- Evidence strength: bounded_single
- Degrees of freedom: none (fixed low-k window parameters; fixed UCFF params; fixed deterministic grid)
- Falsification mode: if the UCFF report violates the declared curvature inequality on the pinned grid, the mapping is eliminated
- Non-implication clause: passing implies only compatibility with this bounded shape constraint; it does not imply physical truth, units correctness, or empirical anchoring

## Purpose (bounded)

Add a genuinely new bridge class that is orthogonal to slope/dispersion equality checks:

- slope constraints test first-derivative behavior,
- curvature/convexity constraints test second-derivative (shape) behavior.

This is a **compatibility constraint**, not a truth claim.

## Inputs (pinned)

### Bragg low-k window definition

Use the lane’s pinned low-k selection rule parameters (rule_id `lowk_window_v1`) from the enabled-gate locks:

- `formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md`
- `formal/markdown/locks/observables/OV-BR-04b_bragg_lowk_slope_conditionB_OVERRIDE.md`

Policy: BRIDGE_TICKET_0004 reads the low-k window *only* from these pinned selection parameters; it does not tune the window.

### UCFF core front door

- Contract: `formal/docs/ucff_core_front_door_contract.md`
- Implementation: `formal/python/toe/ucff/core_front_door.py`

## Declared mapping (structural-only)

Compute UCFF $\omega^2(k)$ on a deterministic grid over the Bragg lane’s low-k window and enforce a curvature/convexity inequality.

We use a discrete second-difference approximation on a uniform grid $k_0 < k_1 < \dots < k_n$:

$$
\Delta^2 \omega^2_i = \omega^2(k_{i+1}) - 2\,\omega^2(k_i) + \omega^2(k_{i-1}).
$$

## Pass / fail criterion (falsifiable)

**PASS** iff the UCFF low-k shape is **convex** on the pinned grid:

- $\Delta^2 \omega^2_i \ge -\varepsilon$ for all interior grid points.

**FAIL (eliminated)** otherwise.

Notes:
- This is selection-free: no $c_\star$ is chosen.
- The only tolerance is the numeric guard band $\varepsilon$ (fixed constant).

## Evidence (deterministic)

- Pytest node: `formal/python/tests/test_bridge_br05_ucff_lowk_curvature.py::test_bridge_br_lowk_window_ucff_omega2_is_convex_on_pinned_grid`
- Harness negative control (operator sanity): `formal/python/tests/test_bridge_br05_ucff_lowk_curvature.py::test_bridge_br_lowk_window_ucff_omega2_convexity_negative_control_operator_sanity`

## Scope limits / non-claims

- Bounded, structural-only mapping.
- The Bragg lane provides the low-k window definition; UCFF provides the report-only dispersion polynomial.
- Does not assert any unit identification between Bragg k-units and UCFF k-units.
- Intended as an orthogonal constraint axis for the bridge family.
