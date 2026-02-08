# Set B Numeric Tolerance Policy

Environment variable: `TOE_NUMERIC_TOLERANCE_PROFILE`

Allowed values:

- `pinned`: single pinned environment; tight regression tolerances.
- `portable`: multi-environment portability lane; relaxed engineering tolerances.

Current Set B test policy:

- `test_setb_probe_stress_lanes.py` reads this profile and applies the corresponding
  tolerance table for:
  - dispersion closure (`omega_error`, `omega_drift`)
  - phase-path invariance (`norm_abs`, `sym_phase`, `sym_constancy`)
  - sampling consistency (`sample_match`)
  - dissipative aggregate consistency (`diss_delta_match`)

Default behavior:

- If the variable is unset, the profile is `pinned`.
