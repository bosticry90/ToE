# WS-10 TGC-93 Branch Decision Package (2026-04-11)

## Status
- ACTIVE
- Date: 2026-04-11
- Tranche: TGC-93
- Class: BRANCH_DECISION_PACKAGE_NONCLAIM

## Objective
Enforce hard branch behavior after TGC-92:
- authorize bounded seam reentry only with new blocker-reducing basis, or
- route directly to theorem-gap rework sequencing.

## Inputs audited
- `formal/docs/release/WS_10_TGC_92_CLOSURE_TO_BLOCKER_TRACEABILITY_DECISION_PACKAGE_20260410_v0.md`
- `formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md`

## Canonical branch tokens
- `TGC93_INPUT_TGC92_BLOCKER_REDUCING_CLOSURE_EVIDENCE_v0: FALSE`
- `TGC93_BRANCH_DECISION_v0: ROUTE_TO_THEOREM_GAP_REWORK`
- `TGC93_SEAM_REENTRY_AUTHORIZATION_v0: DENIED`
- `TGC93_REWORK_ROUTING_v0: TGC_77_TGC_78_TGC_81_TGC_83_TGC_85`

## Branch rule
- If `TGC92_BLOCKER_REDUCING_CLOSURE_EVIDENCE_v0` is `TRUE`, then:
  - `TGC93_BRANCH_DECISION_v0` must be `AUTHORIZE_SINGLE_SEAM_REENTRY`.
  - `TGC93_SEAM_REENTRY_AUTHORIZATION_v0` must be `AUTHORIZED`.
- If `TGC92_BLOCKER_REDUCING_CLOSURE_EVIDENCE_v0` is `FALSE`, then:
  - `TGC93_BRANCH_DECISION_v0` must be `ROUTE_TO_THEOREM_GAP_REWORK`.
  - `TGC93_SEAM_REENTRY_AUTHORIZATION_v0` must be `DENIED`.

## Linkage
- Program pointer: formal/docs/release/WS_10_GLOBAL_COMPLETION_EXECUTION_PROGRAM_20260408_v0.md
- Matrix pointer: formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md

## Non-claim boundary
This package records repository-local branch-routing control behavior and does not assert global physics adequacy claims.
