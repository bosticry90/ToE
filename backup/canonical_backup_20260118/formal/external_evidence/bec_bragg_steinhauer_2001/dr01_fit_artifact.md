# Canonical DR-01 Fit Artifact (Derived from DR-02)

Date: 2026-01-17

This file records a frozen `DR01Fit1D`-compatible linearization derived from the DR-02 external anchor dataset (Steinhauer et al., Fig. 3a).

## Source

- Dataset: `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`
- Paper: Steinhauer PRL 88, 120407 (2002), Fig. 3a (arXiv:0111438v1)

## Fit definition

We construct a 1D DR-01 fit artifact of the form:

- omega(k) = u*k + c_s*|k|

This dataset contains only k > 0 points, so u and c_s are not separately identifiable from omega(k) alone.
For this canonical artifact we therefore fix:

- u = 0

and fit c_s from a deterministic low-k window using a through-origin least squares fit:

- omega ~= c_s * k  (through origin)
- window: k <= 3.2 um^-1
- omega is angular frequency: omega = 2*pi*f, with f = omega/(2*pi) from the CSV.

Units used in the sample:

- k in m^-1 (converted from um^-1)
- omega in rad/s (converted from kHz via omega = 2*pi*(kHz*1e3))

## Result

- c_s = 0.0021889420972527477 m/s

## Fit quality (through-origin)

Computed deterministically from the frozen `sample_kw` points:

- N_points = 9
- RMSE(omega) = 296.12925363791106 rad/s
- slope_stderr (≈ c_s stderr) = 5.3234711357089647e-05 m/s
- R^2 (through-origin) = 0.9952906478115147

## Provenance hash

This artifact is "data-backed" via a content hash of the canonical (k, omega) sample encoding.

- data_fingerprint (sha256): 80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af

The complete artifact (including the sample) is stored in:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json`
