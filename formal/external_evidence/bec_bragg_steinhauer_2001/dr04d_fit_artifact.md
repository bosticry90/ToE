# DR-04d Fit Artifact — Minimal N≥5 Low-k Window (Steinhauer Fig. 3a)

Date: 2026-01-18

This file records a frozen `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using the **smallest available k-max cutoff that yields N≥5** under the frozen digitization.

This is the least invasive auditable rule change from the legacy DR-04a choice (k ≤ 1.6 µm⁻¹, N=4): we keep the frozen CSV unchanged and relax the low-k window definition to the minimal feasible cutoff.

## Source

- Dataset: `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`
- Paper: Steinhauer PRL 88, 120407 (2002), Fig. 3a (arXiv:0111438v1)

## Fit definition

We construct a 1D DR-01 fit artifact of the form:

- ω(k) = u·k + c_s·|k|

This dataset contains only k > 0 points, so u and c_s are not separately identifiable from ω(k) alone. For this DR-04d artifact we therefore fix:

- u = 0

and fit c_s from a deterministic low-k window using a through-origin least squares fit:

- ω ≈ c_s · k  (through origin)
- window: k ≤ 1.75000027210818 µm⁻¹  (smallest k-max giving N≥5 in the frozen CSV)
- ω is angular frequency: ω = 2πf, with f = ω/(2π) taken from the CSV.

Units used in the sample:

- k in m⁻¹ (converted from µm⁻¹)
- ω in rad/s (converted from kHz via ω = 2π·(kHz·1e3))

## Result

- c_s = 0.0019925867614031183 m/s

## Fit quality (through-origin)

Computed deterministically from the frozen `sample_kw` points:

- N_points = 5
- RMSE(ω) = 242.76304066265237 rad/s
- slope_stderr (≈ c_s stderr) = 0.0001037106770711398 m/s
- R² (through-origin) = 0.989280075868062

## Provenance hash

This artifact is data-backed via a content hash of the canonical (k, ω) sample encoding.

- data_fingerprint (sha256): 4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8

The complete artifact (including the sample) is stored in:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04d_fit_artifact.json`
