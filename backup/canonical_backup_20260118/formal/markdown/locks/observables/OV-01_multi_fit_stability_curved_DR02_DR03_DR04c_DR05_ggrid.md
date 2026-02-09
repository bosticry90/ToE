# OV-01 multi-fit stability g-grid discriminator (linear vs curved) — DR-02/03/04c/05

Date: 2026-01-18

This report is an evidence-only g-grid scan for the 4-fit OV-01 envelope, presented as a direct linear-vs-curved comparison. It includes g=0.0 explicitly, reports per-g observable values, and records the locked $R_{\max}/R_{\mathrm{rms}}$ envelope values.

Under OV-01 Option A, the observable is:

- Linear: $O = g\,c_s^2$
- Curved: $O = g\,c_0^2$

Pairwise normalized residuals are

$$r_{ij} = \frac{|O_i - O_j|}{\max(|O_i|, |O_j|, \epsilon)}$$

and we report $R_{\max}$ and $R_{\mathrm{rms}}$.

Note: For all g>0, normalized residuals cancel multiplicative g, so envelope values are invariant across g (g-grid is bookkeeping completeness and explicit g=0 handling).

Windows used:

- DR-02a: k<=3.2
- DR-03a: k<=2.1
- DR-04c: k<=2.5
- DR-05a: k<=1.8

G grid: g ∈ {0.0, 0.1, 0.3, 0.6, 1.0}

## Table

| g | linear O values (DR-02/03/04c/05) | linear R_max | linear R_rms | linear retain (τ=0.10) | curved O values (DR-02/03/04c/05) | curved R_max | curved R_rms | curved retain (τ=0.10) |
|---:|---|---:|---:|:---:|---|---:|---:|:---:|
| 0.0 | [0, 0, 0, 0] | 0.0 | 0.0 | yes | [0, 0, 0, 0] | 0.0 | 0.0 | yes |
| 0.1 | [4.791467505125257e-07, 4.435801708934157e-07, 4.4130067230077946e-07, 3.9704020017189676e-07] | 0.17135992314004550 | 0.10182223237183990 | no | [4.136931906292640e-07, 4.177347443975989e-07, 4.2317868422068215e-07, 4.5220105210294716e-07] | 0.08515650570604280 | 0.05468331594484713 | yes |
| 0.3 | [1.4374402515375773e-06, 1.3307405126802470e-06, 1.3239020169023383e-06, 1.1911206005156903e-06] | 0.17135992314004558 | 0.10182223237183996 | no | [1.2410795718877917e-06, 1.2532042331927965e-06, 1.2695360526620462e-06, 1.3566031563088414e-06] | 0.08515650570604293 | 0.05468331594484720 | yes |
| 0.6 | [2.8748805030751546e-06, 2.6614810253604940e-06, 2.6478040338046766e-06, 2.3822412010313806e-06] | 0.17135992314004558 | 0.10182223237183996 | no | [2.4821591437755834e-06, 2.5064084663855930e-06, 2.5390721053240925e-06, 2.7132063126176830e-06] | 0.08515650570604293 | 0.05468331594484720 | yes |
| 1.0 | [4.7914675051252575e-06, 4.4358017089341570e-06, 4.4130067230077940e-06, 3.9704020017189680e-06] | 0.17135992314004556 | 0.10182223237183993 | no | [4.1369319062926390e-06, 4.1773474439759890e-06, 4.2317868422068210e-06, 4.5220105210294710e-06] | 0.08515650570604283 | 0.05468331594484713 | yes |

## Interpretation

- For g>0, the envelope is invariant across g by construction.
- Under this DR window set (with DR-04c), the curved family passes the current τ=0.10 gate while the linear family does not.
