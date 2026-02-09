# FN-01 cross-fit metric residual (DR-02a vs DR-03a)

Status: evidence-only discriminator report (metric-coupled).

Purpose: define and record a single scalar metric-sensitive residual that changes when swapping the DR fit window choice (DR-02a vs DR-03a), and thread an FN artifact fingerprint for lineage.

## Inputs

- FN artifact: P_cubic (promoted), g = 0.3
- DR artifacts:
  - DR-02a: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json
  - DR-03a: formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json

## Definition

Let BR-01 map a DR fit artifact to an MT-01 metric and extract the scalar component `g_tt` from the constant-field 1D metric.

Define:

- g_tt^02 = g_tt(BR-01(DR-02a))
- g_tt^03 = g_tt(BR-01(DR-03a))

Residual:

- R_metric = |g_tt^02 - g_tt^03| / max(|g_tt^02|, |g_tt^03|, epsilon)

with epsilon = 1e-12.

Composite (FN-tagged) score (MVP):

- Score = R_metric * W(FN)
- W(FN) = 1.0

## Results (deterministic)

- g_tt^02 = -4.7914675051252575e-06
- g_tt^03 = -4.435801708934157e-06
- epsilon = 1e-12
- R_metric = 0.07422899055678828
- W(FN) = 1.0
- Score = 0.07422899055678828

## Fingerprints (lineage)

FN fingerprint (FN01Artifact1D canonical JSON sha256):

- e7777a6932478ade74e4a8463a5ed023fa238a85a394c5135c1c7c001c32156d

DR-02a fingerprint (DR01Fit1D.fingerprint()):

```
DR02_Steinhauer_Fig3a_lowk_linearization_2026-01-17|u=0|c_s=0.002188942097252748|source_kind=csv|source_ref=Steinhauer PRL 88, 120407 (2002), Fig 3a; digitized from arXiv 0111438v1; formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv; low-k window k<= 3.2 um^-1; fit through origin; omega=2*pi*f; date 2026-01-17|fit_method=low-k through-origin omega~=c_s*k on k<= 3.2 um^-1; u fixed to 0|data_fingerprint=80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af
```

DR-03a fingerprint (DR01Fit1D.fingerprint()):

```
DR03_Steinhauer_Fig3a_lowk_linearization_kmax_2p1_2026-01-17|u=0|c_s=0.0021061343045813|source_kind=csv|source_ref=Steinhauer PRL 88, 120407 (2002), Fig 3a; digitized from arXiv 0111438v1; formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv; low-k window k<= 2.1 um^-1; fit through origin; omega=2*pi*f; date 2026-01-17|fit_method=low-k through-origin omega~=c_s*k on k<= 2.1 um^-1; u fixed to 0|data_fingerprint=eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24
```

## Notes

- Under the current BR-01 unit-density gauge and u = 0, the metric component g_tt is numerically equivalent to -c_s^2; therefore this discriminator currently measures (normalized) cross-window drift in c_s^2 expressed in MT-01 metric coordinates.
- This report intentionally includes no timestamps to remain deterministic under version control.
