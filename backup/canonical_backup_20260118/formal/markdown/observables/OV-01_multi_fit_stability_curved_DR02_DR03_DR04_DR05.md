# OV-01 multi-fit stability (curved DR) — DR-02/03/04/05

Date: 2026-01-18

## Definition

We replace the linear-through-origin DR fit with a curvature-aware proxy fit:

$$\frac{\omega}{k} = c_0 + \beta k^2$$

For each DR window (DR-02/03/04/05), we compute $(c_0,\beta)$ deterministically from the same `sample_kw` points.

We then construct BR-01 metric using the curved front door, which maps $c_0$ to an effective $c_s(k\to 0)$ for the existing unit-density mapping.

Finally, we compute the OV-01 observable value for each curved fit and summarize multi-fit spread using pairwise normalized residuals

$$r_{ij} = \frac{|O_i - O_j|}{\max(|O_i|, |O_j|, \epsilon)}$$

and report $R_{\max} = \max r_{ij}$ and $R_{\mathrm{rms}} = \sqrt{\langle r_{ij}^2 \rangle}$.

Gate rule: retain if $R_{\max} \le \tau$ with $\tau=0.10$.

## Locked values

- Curved envelope (4-fit):
  - $R_{\max} \approx 0.2296947$
  - $R_{\mathrm{rms}} \approx 0.1528807$
  - decision: **PRUNE** under $\tau=0.10$

## Interpretation

Curvature-aware fitting reduces (but does not collapse) the multi-window spread relative to the linear-through-origin family. This is evidence that model-brittleness contributes to the drift, but the curved family still fails the current robustness gate at $\tau=0.10$.
