# BRIDGE_TICKET_0002 — OV-BR-05 ↔ UCFF low-k slope compatibility (bounded)

Created: 2026-02-01
Status: Active (structural-only; falsifiable; bounded)

## Bridge family taxonomy (governance; docs-only)

- Bridge class: regime-local compatibility (existence)
- Evidence strength: bounded_single
- Degrees of freedom: deterministic selection of $c_\star$ from the Bragg 1σ overlap interval; then set UCFF $(\rho_0,\lambda,\beta)=(1,0,0)$ and $g=c_\star^2$
- Falsification mode: if the Bragg 1σ overlap is empty, the ticket is eliminated; if the UCFF surface cannot reproduce the chosen low-k slope on the pinned grid, the mapping is eliminated
- Non-implication clause: passing implies only that a compatible low-k slope exists under the stated mapping; it does not imply physical truth or unit correctness

## Purpose (bounded)

Define a **bridge attempt** between:

- Bragg external anchor lane low‑$k$ slope summary (OV-BR-05), and
- UCFF core front door dispersion bookkeeping surface.

This ticket is a **compatibility constraint** only. It does **not** claim empirical equivalence or physical truth.

## Inputs (pinned)

### Bragg slope summary

- Lock (override, gates enabled): `formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md`

This lock is explicitly computed under the enabled admissibility manifest referenced inside the record’s `status.admissibility_manifest`.

### UCFF core front door

- Contract: `formal/docs/ucff_core_front_door_contract.md`
- Implementation: `formal/python/toe/ucff/core_front_door.py`

## Declared mapping (structural-only)

Interpretation for this ticket (bookkeeping convention, not a unit claim):

- Treat the Bragg slope $s$ reported by OV-BR-05 as a low‑$k$ estimate of a linear dispersion slope
  $$\omega(k) \approx s\,k.$$
- Treat the UCFF core polynomial output as
  $$\omega^2(k) = (k^2/2)^2 + (g\,\rho_0)k^2 + \lambda k^4 + \beta k^6.$$

We restrict to the minimal low‑$k$ linear regime family by setting $\lambda = \beta = 0$ and using $g\ge 0$.

In that family, as $k\to 0$:

$$\omega(k) \sim \sqrt{g\,\rho_0}\,k.$$

So the UCFF “effective slope” is $c = \sqrt{g\,\rho_0}$.

## Pass / fail criterion (falsifiable)

Let OV-BR-05 report two slopes (condition A and condition B) with standard errors:

- $(s_A, \mathrm{se}_A)$
- $(s_B, \mathrm{se}_B)$

Define the 1‑sigma intervals:

- $I_A = [s_A-\mathrm{se}_A,\; s_A+\mathrm{se}_A]$
- $I_B = [s_B-\mathrm{se}_B,\; s_B+\mathrm{se}_B]$

**PASS** iff $I_A \cap I_B$ is non-empty (i.e., there exists a single slope consistent with both Bragg conditions at 1‑sigma).

If PASS, select a deterministic target slope:

$$c_\star = \tfrac{1}{2}(\max I_A\cap I_B + \min I_A\cap I_B)$$

and set $\rho_0=1$, $\lambda=\beta=0$, $g=c_\star^2$.

**FAIL (eliminated)** iff $I_A \cap I_B$ is empty.

Notes:
- This ticket’s discriminative content is primarily the **cross-condition compatibility** of the anchored Bragg slopes.
- The UCFF step is bookkeeping: it checks that the core surface can represent the compatible slope via the expected low‑$k$ limit.

## Evidence (deterministic)

- Pytest node: `formal/python/tests/test_bridge_br05_ucff_lowk_slope.py::test_bridge_br05_ucff_lowk_slope_intervals_overlap_and_ucff_can_match`

## Scope limits / non-claims

- Bounded, structural-only mapping.
- Uses only pinned in-repo locks and deterministic computation.
- Does not imply any physical interpretation of UCFF parameters.
- Does not imply empirical anchoring beyond OV-BR-05’s external evidence chain.
