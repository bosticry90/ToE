# CV01 v1 -> Pruning Bridge Design Gate

Purpose: define a controlled, explicit pathway for using CV01 v1 comparator outputs
in pruning decisions without implicit coupling.

Status: design-only; no status upgrade.

## Scope

- CV01 v1 remains a comparator lane under `OV-CV-01`.
- This document does not activate pruning logic.
- Any future coupling must be explicit and test-enforced.

## Non-implicit coupling rule

- BR pruning tables MUST NOT consume CV01 outputs by default.
- A dedicated bridge artifact must map CV01 reason codes to pruning reason atoms.
- The mapping must be versioned and lock-tested.

## Candidate mapping surface (design)

- `cv01_fail_linear_vs_curved_speed_inconsistent` -> `cv01_cross_artifact_inconsistent`
- `cv01_fail_cross_artifact_nonpositive_speed` -> `cv01_invalid_speed_sign`
- `cv01_fail_cross_artifact_missing_inputs` -> `cv01_missing_inputs_blocked`

## Activation gate

Promotion from design-only to active coupling requires all:

- v0 and v1 comparator freeze suites green;
- explicit policy record naming which CV01 reason atoms are eliminative;
- deterministic lock proving at least one elimination is attributable to a CV01 reason atom;
- survivor guard preserved (at least one non-eliminated candidate remains).

## Non-claims

- No external truth claim.
- No automatic upgrade of CV01 status.
- No implicit merge with existing BR-only eliminators.
