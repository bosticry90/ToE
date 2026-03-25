# ToE Closure Semantics Standard v0

Spec ID:
- `TOE_CLOSURE_SEMANTICS_STANDARD_v0`

Classification:
- `P-POLICY`

Purpose:
- Define disciplined closure language across roadmap, matrix, state, and completion-program surfaces.
- Separate bounded theorem-chain discharge from governance closeout and matrix closeout.
- Prevent repo-local completion tokens from being misread as external-truth or final-physics claims.

Non-claim boundary:
- semantics-only control surface.
- no theorem promotion by itself.
- no matrix-status promotion by itself.
- no external-truth claim.

Canonical anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `State_of_the_Theory.md`
- `formal/docs/release/TOE_COMPLETE_V1_PROGRAM_v0.md`
- `formal/python/tests/test_toe_closure_and_action_promotion_standards_gate.py`

Dual-layer closure semantics:
- `PHYSICS-CLOSED`:
  - core theorem-chain objective is discharged under explicit assumptions and pinned non-claim boundaries.
- `GOVERNANCE-CLOSED`:
  - required roadmap/package criteria are satisfied and required blocker rows are cleared under pinned policy.
- `MATRIX-CLOSED`:
  - pillar matrix `matrix_status` is `CLOSED` under canonical unlock and publishability policy.

Terminology discipline:
- conversational `closed` defaults to `PHYSICS-CLOSED` unless explicitly qualified.
- use `MATRIX-CLOSED` or `GOVERNANCE-CLOSED` for matrix/program closeout claims.
- `TOE_COMPLETE_v0` and `TOE_COMPLETE_v1` are repo-local bounded completion semantics and do not mean physics-complete ToE.

Status-language safety rule:
- in canonical status summaries (roadmap/state/program), unqualified `CLOSED` and unqualified `DISCHARGED` are prohibited as top-level interpretation markers.
- status summaries must carry explicit layer qualification (`PHYSICS-CLOSED`, `GOVERNANCE-CLOSED`, `MATRIX-CLOSED`) and bounded non-claim framing.
- `DISCHARGED_v0_*` tokens encode route/governance completion state under pinned assumptions and do not imply global physics completeness.

Control rules:
- pillar matrix `matrix_status` remains the canonical unlock-policy field.
- diagnostic physics/governance status lines do not override matrix status.
- proceed authorization is allowed only when the relevant pillar physics status is explicitly closed under pinned assumptions.
- matrix closure authorization is allowed only when the relevant pillar governance status is explicitly closed and all required closure rows are non-`B-*`.

Program interpretation rule:
- `TOE_COMPLETE_v0` means bounded matrix closure plus governance-green suite.
- `TOE_COMPLETE_v1` means strengthened bounded repo closure under the completion program.
- neither token means publication-grade all-regime derivation closure, seam-total physics closure, or external-truth confirmation.

Required tokens:
- `TOE_CLOSURE_SEMANTICS_STANDARD_STATUS_v0: CANONICAL_PINNED`
- `TOE_CLOSURE_SEMANTICS_DEFAULT_CLOSED_MEANING_v0: PHYSICS_CLOSED_UNLESS_QUALIFIED`
- `TOE_COMPLETE_V1_INTERPRETATION_v0: BOUNDED_REPO_COMPLETION_NOT_PHYSICS_COMPLETE`
- `TOE_CLOSURE_SEMANTICS_CLOSED_USAGE_RULE_v0: REQUIRE_LAYER_QUALIFIER_IN_STATUS_SURFACES`
- `TOE_DISCHARGED_SEMANTICS_RULE_v0: DISCHARGED_IS_ROUTE_OR_GOVERNANCE_NOT_GLOBAL_PHYSICS_COMPLETENESS`
- `TOE_DISCHARGED_VARIANT_REQUIREMENT_v0: USE_DISCHARGED_v0_BOUNDED_WHEN_CONTINUUM_OR_EQUIVALENCE_OPEN`
- `TOE_CLOSURE_SEMANTICS_AMBIGUITY_GUARD_GATE_v0: formal/python/tests/test_toe_closure_status_language_ambiguity_guard_gate.py`