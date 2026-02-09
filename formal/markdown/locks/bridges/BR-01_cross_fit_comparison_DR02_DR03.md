# BR-01 Cross-Fit Comparison (DR-02 vs DR-03)

Date: 2026-01-17

Purpose: evidence-only comparison of BR-01 output metrics when driven by two different frozen DR fit artifacts derived from the Steinhauer Fig. 3a digitization.

## Inputs

- DR-02a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json`
  - tag: `DR02_Steinhauer_Fig3a_lowk_linearization_2026-01-17`
  - data_fingerprint: `80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af`
  - c_s = 0.0021889420972527477 m/s

- DR-03 artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json`
  - tag: `DR03_Steinhauer_Fig3a_lowk_linearization_kmax_2p1_2026-01-17`
  - data_fingerprint: `eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24`
  - c_s = 0.0021061343045813002 m/s

## BR-01 reports (consistency)

BR-01 maps DR01Fit1D -> MT-01 AcousticMetric1D using the unit-density candidate.
The internal consistency check reports exact agreement (within tol = 1e-12) for both artifacts:

- DR-02: max_abs_residual = 0.0
- DR-03: max_abs_residual = 0.0

## Output metrics (1D, constant fields)

For u = 0, the BR-01 unit-density construction produces:

- g_tx = 0
- g_xx = 1
- g_tt = -c_s^2
- c_s2 = c_s^2

Numerical values:

- DR-02 metric:
  - c_s2 = 4.7914675051252575e-06
  - g_tt = -4.7914675051252575e-06

- DR-03 metric:
  - c_s2 = 4.435801708934157e-06
  - g_tt = -4.435801708934157e-06

Delta (DR-03 minus DR-02):

- delta c_s = -8.280779267144742e-05 m/s
- delta c_s2 = -3.5566579619110064e-07
- delta g_tt = +3.5566579619110064e-07

Notes:

- Differences are entirely driven by the different low-k window choices used to derive c_s.
- This is a bookkeeping comparison; it does not interpret which window is "better".
