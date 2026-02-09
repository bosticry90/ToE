# BR-01 Cross-Fit Comparison (DR-02 vs DR-03 vs DR-04 vs DR-05)

Date: 2026-01-17

Purpose: evidence-only comparison of BR-01 output metrics when driven by four different frozen DR fit artifacts derived from the Steinhauer Fig. 3a digitization.

## Inputs

- DR-02a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json`
  - c_s = 0.0021889420972527477 m/s

- DR-03a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json`
  - c_s = 0.0021061343045813002 m/s

- DR-05a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact.json`
  - c_s = 0.0019925867614031183 m/s

- DR-04a artifact: `formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact.json`
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
| DR-05a | 3.9704020017189680e-06 | -3.9704020017189680e-06 |
| DR-04a | 3.4017829332315543e-06 | -3.4017829332315543e-06 |

Notes:

- Differences are entirely driven by the different low-k window choices used to derive c_s.
- This is a bookkeeping comparison; it does not interpret which window is "better".
