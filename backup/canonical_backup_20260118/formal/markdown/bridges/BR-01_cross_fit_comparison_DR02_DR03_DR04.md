# BR-01 Cross-Fit Comparison (DR-02 vs DR-03 vs DR-04)

Date: 2026-01-17

Purpose: evidence-only comparison of BR-01 output metrics when driven by three different frozen DR fit artifacts derived from the Steinhauer Fig. 3a digitization.

## Inputs

- DR-02a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json`
  - tag: `DR02_Steinhauer_Fig3a_lowk_linearization_2026-01-17`
  - data_fingerprint: `80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af`
  - c_s = 0.0021889420972527477 m/s

- DR-03a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json`
  - tag: `DR03_Steinhauer_Fig3a_lowk_linearization_kmax_2p1_2026-01-17`
  - data_fingerprint: `eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24`
  - c_s = 0.0021061343045813002 m/s

- DR-04a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact.json`
  - tag: `DR04_Steinhauer_Fig3a_lowk_linearization_kmax_1p6_2026-01-17`
  - data_fingerprint: `c8971d8ba913dcc08e11e6995f72ee8ccecab832bc24483a94026b52045d804c`
  - c_s = 0.0018443922937465213 m/s

## Output metrics (1D, constant fields)

For u = 0, the BR-01 unit-density construction produces:

- g_tx = 0
- g_xx = 1
- g_tt = -c_s^2
- c_s2 = c_s^2

Numerical values:

| Fit | c_s2 | g_tt |
|---:|---:|---:|
| DR-02a | 4.7914675051252575e-06 | -4.7914675051252575e-06 |
| DR-03a | 4.4358017089341570e-06 | -4.4358017089341570e-06 |
| DR-04a | 3.4017829332315543e-06 | -3.4017829332315543e-06 |

Pairwise deltas (j - i):

- (03 - 02): delta c_s2 = -3.5566579619110064e-07, delta g_tt = +3.5566579619110064e-07
- (04 - 02): delta c_s2 = -1.3896845718937032e-06, delta g_tt = +1.3896845718937032e-06
- (04 - 03): delta c_s2 = -1.0340187757026027e-06, delta g_tt = +1.0340187757026027e-06

Notes:

- Differences are entirely driven by the different low-k window choices used to derive c_s.
- This is a bookkeeping comparison; it does not interpret which window is "better".
