# FN-01 Candidate Pruning Outcomes (Mode-Closure Gate) — DR-02 vs DR-03

Date: 2026-01-17

This is an evidence-only pruning table based on the FN-01 plane-wave mode-closure diagnostic.

Important scope note:

- The current FN-01 mode-closure diagnostic evaluates P[psi] on a fixed plane wave and checks whether P(psi) remains proportional to psi.
- This diagnostic depends on the candidate P and the plane-wave template, not on BR-01/MT-01 metric fields.
- Therefore the mode-closure outcome is identical under DR-02 -> BR-01 and DR-03 -> BR-01.

## Gate definition

A candidate is marked MODE-CLOSED on the tested plane wave if:

- leak_ratio := ||P(psi) - alpha*psi|| / ||P(psi)|| is near 0.

A candidate is marked MODE-LEAKING if leak_ratio ~ 1.

Configuration and per-candidate alpha/leak_ratio are recorded in:

- `formal/markdown/locks/functionals/FN-01_plane_wave_mode_closure_diagnostic.md`

## Pruning table

| candidate | MODE-CLOSED (DR-02) | MODE-CLOSED (DR-03) | comment |
|---|---:|---:|---|
| P_cubic | yes | yes | proportional to psi on a plane wave |
| P_conj | no | no | mixes k and -k (mode leakage) |
| P_xpsi | no | no | explicit x-dependence (mode leakage) |
| P_lap | yes | yes | proportional on plane waves, but linear derivative term |
| P_dxx | yes | yes | proportional on plane waves, anisotropic derivative term |
| P_dxx_minus_dyy | yes | yes | proportional on plane waves, anisotropic derivative term |
| P_constant_source | no | no | injects k=0 forcing (mode leakage) |

## Leading survivor (by combined FN gates)

Cross-reference with the FN-01 gate outcome table (CT-01 / CAUS C1 / SYM):

- The only candidate that is simultaneously (a) mode-closed on plane waves and (b) passes CT-01, CAUS C1, and all SYM gates in the registered table is:
  - P_cubic

This document does not upgrade status; it records a deterministic pruning outcome.
