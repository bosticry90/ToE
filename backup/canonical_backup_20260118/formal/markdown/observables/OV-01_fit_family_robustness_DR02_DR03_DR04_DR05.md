# OV-01g Fit-family robustness gate (linear vs curved) — DR-02/03/04/05

Date: 2026-01-17

## Purpose

This report turns the qualitative observation “curved reduces multi-window spread” into an explicit, decision-grade **fit-family admissibility gate** for the canonical OV-01 robustness workflow.

We compare two DR-fit families over the same 4 frozen window artifacts (DR-02/03/04/05):

- **Linear family** (OV-01d): through-origin $omega \approx c_s k$ and OV-01 observable $O = g\,c_s^2$.
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

- $R_{\max}^{(\mathrm{lin})} = 0.29003318302945985$
- $R_{\mathrm{rms}}^{(\mathrm{lin})} = 0.18477504796266590$

Curved (OV-01e):

- $R_{\max}^{(\mathrm{curv})} = 0.22969472619504086$
- $R_{\mathrm{rms}}^{(\mathrm{curv})} = 0.15288066430819110$

Ratio:

- $Q = 0.7919540125501154$

Curved-fit adequacy:

- DQ-01_v1 (strict): FAIL for the full 4-window set (DR-04 curved is underpowered: $N=4$).
- DQ-01_v2 (tiered): PASS for the full 4-window set (DR-04 is admitted as low-N with β ignored).

## Gate decision

- Under **DQ-01_v2**, $Q \le 0.9$ and curved adequacy passes → **PREFER CURVED**.

## Notes

- Under OV-01 Option A, normalized residuals cancel multiplicative $g$ for all $g>0$; the selection is therefore invariant across non-degenerate g, and g-grid tables are bookkeeping completeness (see OV-01f).
- This gate does not claim robustness is “achieved” (both families still fail the current $\tau=0.10$ retain criterion); it only makes the **family preference** explicit and decision-grade.
