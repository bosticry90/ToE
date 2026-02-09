# BRIDGE_TICKET_0003 — BR-05 ↔ UCFF low-k slope robustness + falsification (bounded)

Created: 2026-02-01
Status: Active (guard / non-fitting check; bounded)

## Bridge family taxonomy (governance; docs-only)

- Bridge class: robustness + falsification guard (non-fitting check)
- Evidence strength: bounded_guard
- Degrees of freedom: none (deterministic interior/exterior sampling based only on the overlap interval endpoints)
- Falsification mode: exterior samples must violate the Bragg window compatibility constraint; interior samples must satisfy the UCFF low-k slope reproduction check
- Non-implication clause: passing strengthens confidence that the bridge behaves like a constraint (not a tuned fit); it does not upgrade any physical interpretation

## Purpose (bounded)

This ticket is a **robustness + falsification guard** for BRIDGE_TICKET_0002.

It targets the main skeptical failure mode:

> BRIDGE_TICKET_0002 can look like “parameter picking” because it selects a slope $c_\star$ inside the intersection of Bragg 1σ windows.

This ticket does **not** strengthen the physical claim. It strengthens the **engineering/scientific posture** by demonstrating:

1. Robustness: multiple deterministic interior choices behave consistently.
2. Falsification: deterministic exterior choices fail cleanly (they violate the Bragg window constraint).

## Inputs (pinned)

- OV-BR-05 lock (override): `formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md`
- UCFF core contract: `formal/docs/ucff_core_front_door_contract.md`
- UCFF implementation: `formal/python/toe/ucff/core_front_door.py`

## Definitions

Let OV-BR-05 provide, for conditions A and B:

- $(s_A, \mathrm{se}_A)$ and $(s_B, \mathrm{se}_B)$

Define 1σ windows:

- $I_A = [s_A-\mathrm{se}_A,\; s_A+\mathrm{se}_A]$
- $I_B = [s_B-\mathrm{se}_B,\; s_B+\mathrm{se}_B]$

Let $I = I_A \cap I_B = [L, H]$.

## Robustness behavior

Choose three deterministic interior samples:

- $c_{0.25} = L + 0.25(H-L)$
- $c_{0.50} = L + 0.50(H-L)$
- $c_{0.75} = L + 0.75(H-L)$

For each sample, define UCFF params in the low‑$k$ linear family:

- $\rho_0 = 1$, $\lambda=0$, $\beta=0$, $g = c^2$

Compute $\omega^2(k)$ on a tiny deterministic grid near $k\approx 0$, take $\omega = \sqrt{\omega^2}$, and fit a slope through the origin.

Expectation: each interior sample reproduces its own target slope within a declared tolerance.

## Falsification behavior

Choose two deterministic exterior samples using the overlap width $w=H-L$:

- $c_L = L - 0.5w$
- $c_R = H + 0.5w$

Expectation: each exterior sample is **not** in the intersection $I$ (equivalently, it violates at least one of the 1σ Bragg windows). This provides a clean failure mode.

Note: UCFF can always represent a chosen slope in the $\lambda=\beta=0$ family by setting $g=c^2$; that is not the claim. The claim is the **Bragg window compatibility constraint**.

## Evidence (deterministic)

- Pytest node: `formal/python/tests/test_bridge_br05_ucff_lowk_slope_robustness.py::test_bridge_br05_ucff_lowk_slope_robustness_and_falsification`

## Scope limits / non-claims

- Guard ticket only; bounded, structural-only.
- No empirical or interpretive upgrade.
- Uses only pinned locks and deterministic computation.
