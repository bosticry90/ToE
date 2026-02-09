# OV-01g Fit-family robustness gate (linear vs curved) — DR-02/03/04c/05

Date: 2026-01-18

## Purpose

This report turns the qualitative observation “curved reduces multi-window spread” into an explicit, decision-grade **fit-family admissibility gate** for the canonical OV-01 robustness workflow.

We compare two DR-fit families over the same 4 frozen window artifacts (DR-02/03/04c/05):

- **Linear family** (OV-01d): through-origin $\omega \approx c_s k$ and OV-01 observable $O = g\,c_s^2$.
- **Curved family** (OV-01e): proxy curvature model $\omega/k = c_0 + \beta k^2$ and BR-01 mapping uses $c_0$ as $c_s(k\to 0)$, so $O = g\,c_0^2$.

Multi-fit spread is summarized using the existing normalized residual envelope:

$$r_{ij} = \frac{|O_i - O_j|}{\max(|O_i|, |O_j|, \epsilon)}$$

with $R_{\max} = \max r_{ij}$ and $R_{\mathrm{rms}} = \sqrt{\langle r_{ij}^2 \rangle}$.

## Gate rule (provisional)

Let:

- $R_{\max}^{(\mathrm{lin})}$ be the 4-fit envelope for the linear family.
- $R_{\max}^{(\mathrm{curv})}$ be the 4-fit envelope for the curved family.
- $Q = R_{\max}^{(\mathrm{curv})} / R_{\max}^{(\mathrm{lin})}$.

Decision:

- **prefer curved** iff $Q \le 0.9$ AND all curved fits pass DQ-01 adequacy under the selected policy.
- Otherwise **robustness failed** for fit-family selection, and downstream must treat OV-based pruning as non-decisive.

## Frozen envelope values (g = 0.3)

Linear (OV-01d):

- $R_{\max}^{(\mathrm{lin})} = 0.17135992314004558$
- $R_{\mathrm{rms}}^{(\mathrm{lin})} = 0.10182223237183996$

Curved (OV-01e):

- $R_{\max}^{(\mathrm{curv})} = 0.08515650570604293$
- $R_{\mathrm{rms}}^{(\mathrm{curv})} = 0.05468331594484720$

Ratio:

- $Q = 0.49694528420421813$

Curved-fit adequacy:

- DQ-01_v1 (strict): PASS for the full 4-window set.
- DQ-01_v2 (tiered): PASS for the full 4-window set (retained for auditability/back-compat).

## Gate decision

- Under **DQ-01_v1**, $Q \le 0.9$ and curved adequacy passes → **PREFER CURVED**.

## Notes

- Under OV-01 Option A, normalized residuals cancel multiplicative $g$ for all $g>0$; the selection is therefore invariant across non-degenerate g.
- With the DR-04c replacement, the curved family also satisfies the current $\tau=0.10$ retain gate (see OV-01 stability locks for DR-02/03/04c/05).
