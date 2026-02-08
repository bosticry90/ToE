# CV01 Numeric Tolerance Policy

Environment variable: `TOE_CV01_TOLERANCE_PROFILE`

Allowed values:

- `pinned`: single pinned environment; tight tolerances.
- `portable`: multi-environment portability lane; relaxed engineering tolerances.

Tolerance table:

- `pinned`
  - `metric_identity = 1e-12`
  - `unit_gxx = 1e-12`
  - `declared_speed_match = 1e-12`
  - `cross_artifact_speed = 2e-4`
- `portable`
  - `metric_identity = 1e-10`
  - `unit_gxx = 1e-10`
  - `declared_speed_match = 1e-10`
  - `cross_artifact_speed = 5e-4`

Default behavior:

- If the variable is unset, profile is `pinned`.
