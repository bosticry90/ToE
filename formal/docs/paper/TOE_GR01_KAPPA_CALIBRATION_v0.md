# TOE-GR-01 Kappa Calibration v0

Spec ID:
- `TOE_GR01_KAPPA_CALIBRATION_v0`

Purpose:
- Make the weak-field Poisson coupling `kappa` dimensionally explicit and calibration-ready.
- Separate symbolic equation shape from physically calibrated parameter posture.

Target form:
- `nabla^2 Phi = kappa * rho`

Dimensional scaffold (SI posture):
- `[Phi] = m^2 s^-2`
- `[rho] = kg m^-3`
- `[kappa] = m^3 kg^-1 s^-2`

Reference mapping (Newtonian weak-field correspondence):
- `kappa = 4 * pi * G_N`
- `G_N` anchor value (CODATA-style reference posture): `6.67430e-11 m^3 kg^-1 s^-2`

Calibration protocol (v0):
1. Choose one anchor regime and one reference observable for `kappa`.
2. Fix `kappa` once on the selected regime.
3. Produce at least one additional quantitative output without refitting `kappa`.
4. Record scope limits and non-claims in the paper table/state inventory.

Deterministic calibration output (v0):
- Tool: `formal/python/tools/toe_gr01_kappa_calibration_record.py`
- Artifact: `formal/output/toe_gr01_kappa_calibration_v0.json`
- Lock: `formal/markdown/locks/functionals/TOE-GR-01_kappa_calibration_v0.md`
- Fingerprint: `ecc77d503f76d25c9e3c573a4a9a9ab11f65820ae3d1b96cdd596d42b6c2a555`
- Residual diagnostics (pinned):
  - `residual_l2_abs = 1.0374290719861313e-23`
  - `residual_linf_abs = 4.084204274480574e-24`

Dependencies:
- theory spec: `formal/docs/paper/THEORY_SPEC_v1.md`
- derivation target: `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md`

Non-claim:
- This v0 artifact is a calibration protocol declaration, not a completed multi-regime fit.
