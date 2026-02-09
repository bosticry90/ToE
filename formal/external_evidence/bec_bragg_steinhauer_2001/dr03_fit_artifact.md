# DR-03 Fit Artifact (Alternate Window) — Derived from DR-02 Dataset

Date: 2026-01-17

This file records a second frozen `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using a deliberately different (more restrictive) low-k window.

## Source

- Dataset: `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`
- Paper: Steinhauer PRL 88, 120407 (2002), Fig. 3a (arXiv:0111438v1)

## Fit definition

We construct a 1D DR-01 fit artifact of the form:

- omega(k) = u*k + c_s*|k|

This dataset contains only k > 0 points, so u and c_s are not separately identifiable from omega(k) alone.
For this DR-03 artifact we therefore fix:

- u = 0

and fit c_s from a deterministic alternate low-k window using a through-origin least squares fit:

- omega ~= c_s * k  (through origin)
- window: k <= 2.1 um^-1
- omega is angular frequency: omega = 2*pi*f, with f = omega/(2*pi) from the CSV.

Units used in the sample:

- k in m^-1 (converted from um^-1)
- omega in rad/s (converted from kHz via omega = 2*pi*(kHz*1e3))

## Result

- c_s = 0.0021061343045813002 m/s

## Fit quality (through-origin)

Computed deterministically from the frozen `sample_kw` points:

- N_points = 6
- RMSE(omega) = 294.70780462524556 rad/s
- slope_stderr (≈ c_s stderr) = 9.634918571711478e-05 m/s
- R^2 (through-origin) = 0.9896444499714963

## Provenance hash

This artifact is "data-backed" via a content hash of the canonical (k, omega) sample encoding.

- data_fingerprint (sha256): eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24

The complete artifact (including the sample) is stored in:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json`
