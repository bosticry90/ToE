# DR fit-quality comparison (curved DR) — DR-02/03/04/05

Date: 2026-01-18

## Model

Curvature-aware proxy fit on digitized samples:

$$\frac{\omega}{k} = c_0 + \beta k^2$$

Quality metrics are computed deterministically in $y=\omega/k$ space:
- $N$ points
- RMSE(y)
- stderr($c_0$), stderr($\beta$)
- $R^2$ (y-space)

## Notes

Because $\omega/k$ varies weakly across the digitized samples relative to its mean, $R^2$ can be numerically small even when the parameter estimates are stable. RMSE(y) and parameter standard errors are therefore treated as the primary diagnostics.

## Frozen values

Sources:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.json`

Summary (all values deterministic):

| Window | N | RMSE(ω/k) [m/s] | stderr(c0) [m/s] | stderr(β) [s/m²] | R²(y) |
|---|---:|---:|---:|---:|---:|
| DR-02 curved (k≤3.2) | 9 | 2.3307872481327850e-04 | 1.3820079782343050e-04 | 2.7529466483225495e-17 | 9.639354544997059e-02 |
| DR-03 curved (k≤2.1) | 6 | 2.8242195854024087e-04 | 2.2824378232785442e-04 | 9.5830763157086800e-17 | 1.1357970394077044e-02 |
| DR-04 curved (k≤1.6) | 4 | 2.2921439968839546e-04 | 2.7513695206787586e-04 | 2.3486522927841644e-16 | 4.9112091111562650e-01 |
| DR-05 curved (k≤1.8) | 5 | 2.8791840665289654e-04 | 2.7364851593466450e-04 | 1.5868946466088918e-16 | 4.7955229323712770e-02 |
