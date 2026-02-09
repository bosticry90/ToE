# DQ-01 Variant A (DR-04-only N=4) — curved-fit adequacy delta

Date: 2026-01-18

## Scope (hard constraint)

This report applies **only** to the case:

- `policy = DQ-01_variantA`
- window corresponds to **DR-04**
- curved-fit point count `N = 4`

All other windows remain evaluated under the default DQ-01 policy (no general N=4 allowance).

## Variant A rule (decision-grade)

For DR-04 at N=4:

- Fit quality must exist; else **FAIL** with `missing_fit_quality`.
- Strict bounds:
  - require `rmse_omega_over_k_m_per_s <= 2.50e-4`
  - require `c0_stderr_m_per_s <= 2.80e-4`
- β is **not used for inference** at N=4:
  - `beta_used_for_inference = 0.0`
  - include reason code `beta_ignored_low_n`
  - β identifiability cannot fail the fit under Variant A.

## DR-04 curved-fit adequacy under Variant A

Source artifact:
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.json`

Observed metrics (curved):

| Window | N | rmse(ω/k) [m/s] | stderr(c0) [m/s] | pass | reason codes |
|---|---:|---:|---:|:---:|---|
| DR-04 (k≤1.6) | 4 | 2.292144e-4 | 2.7513695e-4 | yes | beta_ignored_low_n |

Required recorded statement:

> DR-04 passes Variant A only under β-not-used-for-inference at N=4.
