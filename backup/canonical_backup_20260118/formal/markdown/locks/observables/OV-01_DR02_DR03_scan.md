# OV-01 observable residual scan (DR-02a vs DR-03a)

Status: evidence-only observable scan (FN-dependent, metric-dependent).

Purpose: record a minimal but real observable that depends on FN parameters and on the BR-01/MT-01 metric derived from data-backed DR fits, and compare its values under DR-02a vs DR-03a.

Definition (Option A: consistency residual):

- Observable: obs = g * c_s2
- Target: 0
- Residual: R = |obs|

where c_s2 is extracted from the BR-01-derived MT-01 metric (unit-density gauge).

## Inputs

- DR-02a: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json
- DR-03a: formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json
- FN artifact family: P_cubic with varied g (promoted artifact constructor)

## Metric scalars (from BR-01)

- DR-02a: c_s2 = 4.7914675051252575e-06, g_tt = -4.7914675051252575e-06
- DR-03a: c_s2 = 4.435801708934157e-06, g_tt = -4.435801708934157e-06

## Scan

All values deterministic.

| g | obs(DR-02a) = g*c_s2 | R(DR-02a) | obs(DR-03a) = g*c_s2 | R(DR-03a) |
|---:|---------------------:|---------:|---------------------:|---------:|
| 0.1 | 4.7914675051252576e-07 | 4.7914675051252576e-07 | 4.4358017089341573e-07 | 4.4358017089341573e-07 |
| 0.3 | 1.4374402515375773e-06 | 1.4374402515375773e-06 | 1.3307405126802472e-06 | 1.3307405126802472e-06 |
| 0.6 | 2.8748805030751545e-06 | 2.8748805030751545e-06 | 2.6614810253604943e-06 | 2.6614810253604943e-06 |

## Notes

- This observable is probe-relative and intentionally minimal; it is not a physical claim.
- It is FN-sensitive (changes with g) and metric-sensitive (changes under DR-02a vs DR-03a via c_s2 drift).
- Future upgrades can replace the simple product g*c_s2 with a physically motivated observable while preserving the report + fingerprint pattern.
