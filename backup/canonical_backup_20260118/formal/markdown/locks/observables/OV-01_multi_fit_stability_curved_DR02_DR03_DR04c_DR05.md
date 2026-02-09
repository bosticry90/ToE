# OV-01 multi-fit stability (curved DR) — DR-02/03/04c/05

Date: 2026-01-18

## Definition

We replace the linear-through-origin DR fit with a curvature-aware proxy fit:

$$\frac{\omega}{k} = c_0 + \beta k^2$$

For each DR window (DR-02/03/04c/05), we compute $(c_0,\beta)$ deterministically from the same `sample_kw` points.

We then construct BR-01 metric using the curved front door, which maps $c_0$ to an effective $c_s(k\to 0)$ for the existing unit-density mapping.

Finally, we compute the OV-01 observable value for each curved fit and summarize multi-fit spread using pairwise normalized residuals

$$r_{ij} = \frac{|O_i - O_j|}{\max(|O_i|, |O_j|, \epsilon)}$$

and report $R_{\max} = \max r_{ij}$ and $R_{\mathrm{rms}} = \sqrt{\langle r_{ij}^2 \rangle}$.

Gate rule: retain if $R_{\max} \le \tau$ with $\tau=0.10$.

## Locked values

- Curved envelope (4-fit):
  - $R_{\max} \approx 0.08515651$
  - $R_{\mathrm{rms}} \approx 0.05468332$
  - decision: **RETAIN** under $\tau=0.10$

## Interpretation

With the DR-04c replacement (N=7), the curved family’s 4-fit envelope falls below the current τ=0.10 gate, making curvature-aware OV-based pruning decision-grade without requiring a low-N exception policy.
