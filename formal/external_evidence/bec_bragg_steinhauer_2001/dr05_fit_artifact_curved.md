# DR05 Curved Fit Artifact  Derived from Steinhauer Fig. 3a

Date: 2026-01-18

This file records a curvature-aware DR fit artifact computed deterministically from the frozen sample_kw points in the corresponding linear DR window artifact.

## Fit definition

We fit the proxy model:

- ω/k = c0 + β k

with u fixed to 0 (as in the linear artifacts).

## Result

- c0 = 0.002126501944750926 m/s
- beta = -6.168762109148344e-17 s/m

## Fit quality (y = ω/k space)

- N_points = 5
- RMSE(ω/k) = 0.00028791840665289654 m/s
- stderr(c0) = 0.0002736485159346645 m/s
- stderr(beta) = 1.5868946466088918e-16 s/m
- R(y-space) = 0.04795522932371277

## Provenance hash

- data_fingerprint (sha256): 4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8
- fit_quality_fingerprint (sha256): 6dca51e7264fb7fa3847faab8645ccd6ea0933e70ea0c94649be5e420fd42b68

The complete artifact (including the sample) is stored in:

- ormal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.json
