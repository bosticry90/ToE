# CV01 v1 Discriminative Design Gate

Purpose: define a non-tautological comparator condition before CV01 is upgraded
from `integrity_only` to a physics-discriminating lane.

Status: design-only; no status upgrade.

## Current v0 role

- CV01 v0 is explicitly `integrity_only`.
- It validates front-door typing, deterministic record generation, and metric
  self-consistency checks.

## v1 discriminative condition (planned)

At least one comparator condition must not be structurally guaranteed by the
BR-01 gauge mapping.

Candidate condition family:

- linear-vs-curved cross-artifact consistency residual:
  - derive a shared low-k speed estimate from both artifacts,
  - enforce a bounded residual under an explicit tolerance policy,
  - fail with a stable reason code when violated.

## Required negative control

- A perturbed synthetic artifact must fail deterministically with a declared
  CV01 reason code family.

## Promotion gate (v0 -> v1)

- CV01 v0 freeze tests remain green.
- Negative control lane remains green.
- At least one non-tautological v1 condition is implemented and proven to
  produce deterministic pass/fail behavior.
