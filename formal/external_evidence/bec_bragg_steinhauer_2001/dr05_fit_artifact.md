# DR-05 Fit Artifact (Intermediate Window) — Derived from DR-02 Dataset

Date: 2026-01-17

This file records a fourth frozen `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using an intermediate low-k window intended to distinguish monotone drift vs isolated-window outliers.

## Source

- Dataset: `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`
- Paper: Steinhauer PRL 88, 120407 (2002), Fig. 3a (arXiv:0111438v1)

## Fit definition

We construct a 1D DR-01 fit artifact of the form:

- omega(k) = u*k + c_s*|k|

This dataset contains only k > 0 points, so u and c_s are not separately identifiable from omega(k) alone.
For this DR-05 artifact we therefore fix:

- u = 0

and fit c_s from a deterministic low-k window using a through-origin least squares fit:

- omega ~= c_s * k  (through origin)
- window: k <= 1.8 um^-1
- omega is angular frequency: omega = 2*pi*f, with f = omega/(2*pi) from the CSV.

Units used in the sample:

- k in m^-1 (converted from um^-1)
- omega in rad/s (converted from kHz via omega = 2*pi*(kHz*1e3))

## Result

- c_s = 0.0019925867614031183 m/s

## Fit quality (through-origin)

Computed deterministically from the frozen `sample_kw` points:

- N_points = 5
- RMSE(omega) = 242.76304066265237 rad/s
- slope_stderr (≈ c_s stderr) = 0.0001037106770711398 m/s
- R^2 (through-origin) = 0.989280075868062

## Provenance hash

This artifact is "data-backed" via a content hash of the canonical (k, omega) sample encoding.

- data_fingerprint (sha256): 4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8

The complete artifact (including the sample) is stored in:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact.json`
