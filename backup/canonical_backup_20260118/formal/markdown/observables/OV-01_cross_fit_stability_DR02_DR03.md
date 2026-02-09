# OV-01 cross-fit stability (DR-02a vs DR-03a)

Status: evidence-only discriminator gate (OV-01b).

Purpose: convert OV-01 from “observable exists and changes” into an explicit robustness check: for a fixed FN hypothesis, measure how stable the OV-01 observable is under a reasonable DR fit-window perturbation (DR-02a vs DR-03a) derived from the same dataset.

## Definition

For a fixed FN artifact (here P_cubic with parameter `g`) and two DR fit artifacts:

- `obs_02 = OV-01(fn, DR-02a).obs_value`
- `obs_03 = OV-01(fn, DR-03a).obs_value`

Cross-fit stability residual:

- `R_obs_cross = |obs_02 - obs_03| / max(|obs_02|, |obs_03|, epsilon)`

Parameters:

- `epsilon = 1e-12`
- Provisional gate threshold `tau_obs = 0.10`

Prune/retain rule (Rule A, provisional):

- **retain** iff `R_obs_cross <= tau_obs`

## Inputs

- DR-02a: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json
- DR-03a: formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json
- FN artifacts: P_cubic (promoted) with varying `g`

## Grid (deterministic)

Computed via the OV-01 and OV-01b front doors (BR-01 → MT-01 metric → OV-01 observable).

| g | obs_02 | obs_03 | R_obs_cross | retain (tau=0.10) |
|---:|------:|------:|------------:|:------------------:|
| 0.0 | 0 | 0 | 0 | yes |
| 0.1 | 4.791467505125257e-07 | 4.435801708934157e-07 | 0.07422899055678818 | yes |
| 0.3 | 1.437440251537577e-06 | 1.330740512680247e-06 | 0.07422899055678828 | yes |
| 0.6 | 2.874880503075155e-06 | 2.661481025360494e-06 | 0.07422899055678828 | yes |
| 1.0 | 4.791467505125257e-06 | 4.435801708934157e-06 | 0.07422899055678828 | yes |

## Notes

- For this OV-01 definition (`obs = g*c_s2`), `R_obs_cross` is independent of `g` for any nonzero g (the g factor cancels in the normalization), so the robustness gate is really testing DR-window stability of the DR→metric path expressed through an FN-coupled observable.
- The threshold `tau_obs` is explicitly provisional: its value is not claimed to be physically correct; it exists to force a concrete prune/retain decision into the loop.
