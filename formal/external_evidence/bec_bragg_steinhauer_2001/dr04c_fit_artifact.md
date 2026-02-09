# DR-04c Fit Artifact — Derived from DR-02 Dataset

Date: 2026-01-17

This file records a frozen `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using an alternate low-k window choice.

This DR-04c artifact is introduced to provide an N≥5 window option for strict curved-fit adequacy (DQ-01_v1) while retaining a 4-window robustness set.

## Source

- Dataset: `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`
- Paper: Steinhauer PRL 88, 120407 (2002), Fig. 3a (arXiv:0111438v1)

## Fit definition

We construct a 1D DR-01 fit artifact of the form:

- omega(k) = u*k + c_s*|k|

This dataset contains only k > 0 points, so u and c_s are not separately identifiable from omega(k) alone.
For this DR-04c artifact we therefore fix:

- u = 0

and fit c_s from a deterministic low-k window using a through-origin least squares fit:

- omega ~= c_s * k  (through origin)
- window: k <= 2.5 um^-1
- omega is angular frequency: omega = 2*pi*f, with f = omega/(2*pi) from the CSV.

Units used in the sample:

- k in m^-1 (converted from um^-1)
- omega in rad/s (converted from kHz via omega = 2*pi*(kHz*1e3))

## Result

- c_s = 0.002100715764449773 m/s

## Fit quality (through-origin)

Computed deterministically from the frozen `sample_kw` points:

- N_points = 7
- RMSE(omega) = 273.0934995832537 rad/s
- slope_stderr (≈ c_s stderr) = 7.102510929890895e-05 m/s
- R^2 (through-origin) = 0.9931880419508932

## Provenance hash

This artifact is data-backed via a content hash of the canonical (k, omega) sample encoding.

- data_fingerprint (sha256): 68480ae926b58d56a9dee08263584aedc9167460ecb470539c0c2a47a0a1ee01

The complete artifact (including the sample) is stored in:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact.json`
