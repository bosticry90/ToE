# DR-04d Curved Fit Artifact — Minimal N≥5 Low-k Window (Steinhauer Fig. 3a)

Date: 2026-01-18

This file records a curvature-aware DR fit artifact computed deterministically from the frozen `sample_kw` points in the corresponding linear DR-04d window artifact.

## Fit definition

We fit the proxy model (with u fixed to 0, as in the linear artifacts):

- ω/k = c0 + β k²

## Result

- c0 = 0.002126501944750926 m/s
- beta = -6.168762109148344e-17 s/m²

## Fit quality (y = ω/k space)

- N_points = 5
- RMSE(ω/k) = 0.00028791840665289654 m/s
- stderr(c0) = 0.0002736485159346645 m/s
- stderr(beta) = 1.5868946466088918e-16 s/m²
- R²(y-space) = 0.04795522932371277

## Provenance hash

- data_fingerprint (sha256): 4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8
- fit_quality_fingerprint (sha256): 6dca51e7264fb7fa3847faab8645ccd6ea0933e70ea0c94649be5e420fd42b68

The complete artifact (including the sample) is stored in:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04d_fit_artifact_curved.json`
