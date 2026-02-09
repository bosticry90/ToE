# OV-01 multi-fit stability g-grid scan — linear vs curved (DR-02/03/04/05)

Date: 2026-01-17

This report extends the OV-01d (linear DR) and OV-01e (curved DR) 4-fit envelopes into an explicit **g-grid scan**, including **g=0.0**, using the same provisional gate:

- retain iff $R_{\max} \le \tau$ with $\tau = 0.10$

OV-01 Option A (unchanged):

- $O = g\,c_s^2$

Multi-fit spread uses pairwise normalized residuals:

$$r_{ij} = \frac{|O_i - O_j|}{\max(|O_i|, |O_j|, \epsilon)}$$

and summary statistics $R_{\max} = \max r_{ij}$ and $R_{\mathrm{rms}} = \sqrt{\langle r_{ij}^2 \rangle}$.

Note: because $O$ is multiplicative in $g$, the normalized residuals are constant for all $g>0$ (they cancel $g$). The $g=0$ row is a degenerate case with all observables 0, yielding all residuals 0 by construction.

## Inputs

Linear DR artifacts:

- DR-02a: `dr01_fit_artifact.json`
- DR-03a: `dr03_fit_artifact.json`
- DR-04a: `dr04_fit_artifact.json`
- DR-05a: `dr05_fit_artifact.json`

Curved DR artifacts:

- DR-02a: `dr01_fit_artifact_curved.json`
- DR-03a: `dr03_fit_artifact_curved.json`
- DR-04a: `dr04_fit_artifact_curved.json`
- DR-05a: `dr05_fit_artifact_curved.json`

g-grid (canonical): $g \in \{0.0, 0.1, 0.3, 0.6, 1.0\}$

## Fit-derived values

### Linear (from OV-01d)

$c_s^2$:

- DR-02a: $4.7914675051252575\times 10^{-6}$
- DR-03a: $4.4358017089341570\times 10^{-6}$
- DR-04a: $3.4017829332315543\times 10^{-6}$
- DR-05a: $3.9704020017189680\times 10^{-6}$

Pairwise residuals (ordering 02,03,04,05):

- $r_{02,03} = 0.07422899055678828$
- $r_{02,04} = 0.29003318302945985$
- $r_{02,05} = 0.17135992314004556$
- $r_{03,04} = 0.23310752904485865$
- $r_{03,05} = 0.10491896116046550$
- $r_{04,05} = 0.14321448262448797$

Summary:

- $R_{\max} = 0.29003318302945985$
- $R_{\mathrm{rms}} = 0.18477504796266590$

### Curved (from frozen curved artifacts)

Curved proxy model:

$$\frac{\omega}{k} = c_0 + \beta k^2$$

BR-01 maps $c_0 \mapsto c_s(k\to 0)$, so $c_s^2 = c_0^2$ for OV-01.

$c_0^2$:

- DR-02a: $4.136931906292639\times 10^{-6}$
- DR-03a: $4.177347443975989\times 10^{-6}$
- DR-04a: $5.370509649840601\times 10^{-6}$
- DR-05a: $4.522010521029471\times 10^{-6}$

Pairwise residuals (ordering 02,03,04,05):

- $r_{02,03} = 0.009674928462469904$
- $r_{02,04} = 0.22969472619504086$
- $r_{02,05} = 0.08515650570604293$
- $r_{03,04} = 0.22216926952175312$
- $r_{03,05} = 0.07621899052437806$
- $r_{04,05} = 0.15799229200459830$

Summary:

- $R_{\max} = 0.22969472619504086$
- $R_{\mathrm{rms}} = 0.15288066430819110$

## g-grid scan (tau_obs = 0.10)

### Linear

| g | O_DR02 | O_DR03 | O_DR04 | O_DR05 | R_max | R_rms | retain |
|---:|---:|---:|---:|---:|---:|---:|:---:|
| 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | yes |
| 0.1 | 4.791467505125257e-07 | 4.435801708934157e-07 | 3.401782933231554e-07 | 3.970402001718968e-07 | 0.29003318302945985 | 0.18477504796266590 | no |
| 0.3 | 1.4374402515375773e-06 | 1.330740512680247e-06 | 1.0205348799694663e-06 | 1.1911206005156903e-06 | 0.29003318302945985 | 0.18477504796266590 | no |
| 0.6 | 2.8748805030751546e-06 | 2.661481025360494e-06 | 2.0410697599389326e-06 | 2.3822412010313806e-06 | 0.29003318302945985 | 0.18477504796266590 | no |
| 1.0 | 4.7914675051252575e-06 | 4.435801708934157e-06 | 3.4017829332315543e-06 | 3.970402001718968e-06 | 0.29003318302945985 | 0.18477504796266590 | no |

### Curved

| g | O_DR02 | O_DR03 | O_DR04 | O_DR05 | R_max | R_rms | retain |
|---:|---:|---:|---:|---:|---:|---:|:---:|
| 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | yes |
| 0.1 | 4.136931906292640e-07 | 4.177347443975989e-07 | 5.370509649840601e-07 | 4.522010521029472e-07 | 0.22969472619504086 | 0.15288066430819110 | no |
| 0.3 | 1.2410795718877917e-06 | 1.2532042331927965e-06 | 1.6111528949521802e-06 | 1.3566031563088414e-06 | 0.22969472619504086 | 0.15288066430819110 | no |
| 0.6 | 2.4821591437755834e-06 | 2.506408466385593e-06 | 3.2223057899043603e-06 | 2.713206312617683e-06 | 0.22969472619504086 | 0.15288066430819110 | no |
| 1.0 | 4.136931906292639e-06 | 4.177347443975989e-06 | 5.370509649840601e-06 | 4.522010521029471e-06 | 0.22969472619504086 | 0.15288066430819110 | no |

## Side-by-side discriminator

| g | R_max (linear) | retain (linear) | R_max (curved) | retain (curved) | R_max ratio (curved/linear) |
|---:|---:|:---:|---:|:---:|---:|
| 0.0 | 0.0 | yes | 0.0 | yes | n/a |
| 0.1 | 0.29003318302945985 | no | 0.22969472619504086 | no | 0.7919540125501154 |
| 0.3 | 0.29003318302945985 | no | 0.22969472619504086 | no | 0.7919540125501154 |
| 0.6 | 0.29003318302945985 | no | 0.22969472619504086 | no | 0.7919540125501154 |
| 1.0 | 0.29003318302945985 | no | 0.22969472619504086 | no | 0.7919540125501154 |

## Interpretation

- For all non-degenerate $g>0$, the OV-01 normalized multi-fit residuals are constant across the grid (by construction), so the **comparative discriminator** is entirely in the per-family envelope values.
- Curved fitting reduces $R_{\max}$ from $\approx 0.2900$ to $\approx 0.2297$ (about a 21% reduction), but the envelope still fails the current $\tau=0.10$ gate.
