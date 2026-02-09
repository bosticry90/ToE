# DQ-01 Curved-fit adequacy table — DR-02/03/04/05 (curved)

Date: 2026-01-17

This report records a deterministic adequacy gate for curvature-aware DR fits (proxy model $\omega/k = c_0 + \beta k^2$) using only each frozen curved artifact’s stamped y-space diagnostics and parameters.

Policy: **DQ-01_v1 (strict)**.

Adequacy checks (provisional defaults):

- $N \ge 5$
- $\mathrm{RMSE}(\omega/k) \le 4\times 10^{-4}$ m/s
- $\mathrm{stderr}(c_0) \le 3\times 10^{-4}$ m/s
- $\beta$ identifiability: pass iff $|\beta|/\mathrm{stderr}(\beta) \ge 2$ OR $\mathrm{stderr}(\beta) \le 2\times 10^{-16}$ s/m²

Notes:
- $R^2(y)$ is intentionally **not** used as a required adequacy check in y=ω/k space.
- The goal is not to prove curvature is real; it is to prevent “curved family preferred” from becoming operational when curvature inference is underpowered.

Sources:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.json`

## Table

| Window | N | RMSE(ω/k) [m/s] | stderr(c0) [m/s] | β [s/m²] | stderr(β) [s/m²] | β_snr | pass | reason codes |
|---|---:|---:|---:|---:|---:|---:|:---:|---|
| DR-02 curved (k≤3.2) | 9 | 2.3307872481327850e-04 | 1.3820079782343050e-04 | 2.3789270790166762e-17 | 2.7529466483225495e-17 | 0.8641384606803861 | yes |  |
| DR-03 curved (k≤2.1) | 6 | 2.8242195854024087e-04 | 2.2824378232785442e-04 | 2.0543090235917590e-17 | 9.5830763157086800e-17 | 0.2143684299189305 | yes |  |
| DR-04 curved (k≤1.6) | 4 | 2.2921439968839546e-04 | 2.7513695206787586e-04 | -3.2630267536535073e-16 | 2.3486522927841644e-16 | 1.3893187866414298 | no | n_points_lt_min; beta_not_identifiable |
| DR-05 curved (k≤1.8) | 5 | 2.8791840665289654e-04 | 2.7364851593466450e-04 | -6.1687621091483440e-17 | 1.5868946466088918e-16 | 0.3887316730402144 | yes |  |
