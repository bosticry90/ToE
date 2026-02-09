# BRIDGE_TICKET_0001 — C6 ↔ UCFF dispersion (structural square)

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-01

## Bridge family taxonomy (governance; docs-only)

- Bridge class: algebraic relation
- Evidence strength: bounded_single
- Degrees of freedom: none (fixed baseline parameters; fixed deterministic k-grid)
- Falsification mode: pytest node failure eliminates this mapping under current canonical surfaces
- Non-implication clause: passing implies only structural compatibility under the stated mapping; it does not imply physical truth or empirical anchoring

## Claim (falsifiable; structural)

In the linear CP–NLSE limit ($g_\mathrm{eff}=0$), the C6 plane-wave dispersion is

$$
\omega_{C6}(k) = \tfrac12 k^2, \quad k^2 = k_x^2 + k_y^2.
$$

In the UCFF core front door with $(g,\lambda,\beta)=(0,0,0)$, the reported dispersion polynomial is

$$
\omega^2_{UCFF}(k) = (k^2/2)^2.
$$

Bridge assertion:

$$
\omega^2_{UCFF}(k) = \omega_{C6}(k)^2
$$

for a bounded deterministic sample of $k$ values.

This is a **structural compatibility** statement only. It does **not** assert physical equivalence or empirical anchoring.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`
- UCFF core surface: `formal/python/toe/ucff/core_front_door.py`

## Evidence (pytest)

- `formal/python/tests/test_bridge_c6_ucff_dispersion_square.py::test_bridge_c6_ucff_omega2_equals_square_of_linear_c6_omega`

## Exit condition

- Passes deterministically.

## Failure posture

- If the test fails, the ticket is **Eliminated** (the structural mapping is not supported under current surfaces).
