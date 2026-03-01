# PILLAR-STAT Unlock Readiness Checklist v0

Spec ID:
- `PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0`

Classification:
- `P-POLICY`

Purpose:
- Provide a bounded, machine-checkable go/no-go checklist for moving `PILLAR-STAT` from `LOCKED` to `ACTIVE`.
- Preserve existing non-claim and no-adjudication-flip governance semantics.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- does not change adjudication truth by itself.
- does not authorize semantic broadening outside bounded scope.

Canonical policy anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `formal/docs/paper/DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md`
- `formal/docs/release/PILLAR_MATURITY_AUDIT_v0.md`
- `formal/docs/release/PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md`

## Go/No-Go Checklist (unlocking `PILLAR-STAT`)

### Gate A — prerequisite closure (must be true)
1. `TARGET-GR01-DERIV-CHECKLIST-PLAN` is `CLOSED` in canonical roadmap surfaces.
2. No contradictory prerequisite token appears in state/roadmap/matrix surfaces.

Pass evidence:
- Roadmap row for `PILLAR-STAT` shows prerequisite set as closed.
- Matrix and cross-surface consistency gates pass.

Fail conditions:
- Any prerequisite token unresolved or contradictory across canonical surfaces.

### Gate B — STAT target structure is explicitly pinned (must be true)
1. `TARGET-TH-ENTROPY-PLAN` remains the sole target ID for unlock.
2. `formal/docs/paper/DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md` retains all required structural objects:
   - entropy/entropy-production object,
   - flux/balance object,
   - regime assumptions object,
   - admissibility/causality constraints.
3. Closure definition remains explicit: typed theorem/derivation surface + explicit regime validity + synchronized pointers.
4. Exact STAT authority token names and placeholder values are pre-pinned (non-discharged, legacy-safe) before activation, with no cross-surface mirror definitions while `PILLAR-STAT` is `LOCKED`.

Pass evidence:
- Structural object list and closure definition lines remain present and unambiguous.
- `formal/python/tests/test_stat_authority_token_preset_lock_gate.py` passes.
- Phase-advancement handoff pins remain synchronized across:
  - `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`
  - `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
  - `State_of_the_Theory.md`
  - `formal/docs/release/PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md`
  - `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json`
- Current handoff evidence is certified by:
  - `formal/python/tests/test_stat_failure_trigger_discharge_object_surface_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_failure_trigger_discharge_coherence_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_discharge_completion_transition_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_adjudication_transition_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_inevitability_transition_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_boundary_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py`
  - `formal/python/tests/test_stat_unlock_prerequisite_integrity_gate.py`
  - `formal/python/tests/test_pillar_phase_advancement_gate.py`

Fail conditions:
- Missing required structural object definition.
- Scope drift into unbounded or claim-level semantics.
- Any drift between the pinned nonflip-execution-custody-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation status token and the post-saturation scaffold reopen token handoff.

### Gate C — unlock transition wiring (must be completed in one change set)
1. Update roadmap pillar table row: `PILLAR-STAT` status `LOCKED` -> `ACTIVE`.
2. Keep `PILLAR-COSMO` as `LOCKED` (frozen order: `QFT -> STAT -> COSMO`).
3. Register `PILLAR-STAT` in `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json` with an `ACTIVE` matrix row and synchronized placeholder authority tokens (non-discharged, non-legacy values).
4. Mirror the STAT authority tokens exactly once in `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`, `formal/docs/paper/PHYSICS_ROADMAP_v0.md`, and `State_of_the_Theory.md`.
5. Ensure at-most-one-active rule remains satisfied after edit.
6. Apply matching doc-gate updates required by freeze policy (no dangling references), using `formal/docs/release/PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md` as the patch boundary template.

Pass evidence:
- Roadmap and matrix/status gates remain green after status transition.

Fail conditions:
- Multiple `ACTIVE` pillars created.
- Unlock order violated.
- Doc-gate references left inconsistent.

### Gate D — governance-suite pass on pinned tests (must be green)
Required unlock validation split:
- Preflight while `PILLAR-STAT` is still `LOCKED`:
  - `formal/python/tests/test_stat_unlock_readiness_pack_gate.py`
- Post-activation patch validation (after `LOCKED -> ACTIVE`, excludes lock-scoped readiness pack gate):
  - `formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
  - `formal/python/tests/test_authority_token_single_definition_gate.py`
  - `formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py`
  - `formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py`
  - `formal/python/tests/test_pillar_status_matrix_consistency_gate.py`
  - `formal/python/tests/test_results_table_integrity.py`

Command (preflight, LOCKED posture):
- `python -m pytest formal/python/tests/test_stat_unlock_readiness_pack_gate.py`

Command (post-activation, ACTIVE posture):
- `python -m pytest formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_authority_token_single_definition_gate.py formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py formal/python/tests/test_pillar_status_matrix_consistency_gate.py formal/python/tests/test_results_table_integrity.py`

Policy note:
- Freeze policy language requires governance-suite pass on pinned tests. If release governance interprets this as full pinned list in roadmap enforcement hooks, run that full set before merge.

Fail conditions:
- Any red in minimum pack or required pinned governance suite.

### Gate E — bounded completeness posture before/at unlock
1. Preserve current truth: custody gate may be satisfied while adequacy gate remains unsatisfied.
2. Do not claim all-5 maturity unless both custody and adequacy 5x5 gates are satisfied.
3. Keep SR/EM/QM/GR/QFT adjudication tokens unchanged during STAT unlock transition.

Pass evidence:
- No adjudication-token flips in diff.
- Maturity framing remains bounded and non-claim.

Fail conditions:
- Any implicit or explicit adjudication promotion during unlock-only change.

## Execution order (minimal)
1. Validate Gate A + Gate B (read-only verification) and run Gate D preflight (`LOCKED` posture).
2. Prepare and review the atomic diff using `formal/docs/release/PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md`.
3. Apply Gate C transition edits in one atomic change set.
4. Run Gate D post-activation validation pack (`ACTIVE` posture) (and full pinned suite if required by release policy).
5. Record Gate E attestation in release notes/state checkpoint.

## Unlock decision template
- `PILLAR-STAT_UNLOCK_DECISION_v0: GO | NO_GO`
- `PILLAR-STAT_UNLOCK_PREREQ_CHECK_v0: PASS | FAIL`
- `PILLAR-STAT_UNLOCK_WIRING_CHECK_v0: PASS | FAIL`
- `PILLAR-STAT_UNLOCK_GOVERNANCE_SUITE_v0: PASS | FAIL`
- `PILLAR-STAT_UNLOCK_NONCLAIM_BOUNDARY_v0: PASS | FAIL`
- `PILLAR-STAT_UNLOCK_NOTES_v0: <short bounded rationale>`

Unlock authorization rule:
- Emit `GO` only when all four checks are `PASS` and no bounded-scope violations are present.

## Post-Activation Closure-Prep Handoff (ACTIVE posture only)

Purpose:
- Separate the current `ACTIVE` pre-discharge lane from the future `ACTIVE -> CLOSED` transition.
- Pin the exact closure-prep control surfaces without authorizing closure by itself.

Current closure-prep posture (must remain true until fully earned closure criteria are satisfied):
- `PILLAR-STAT_PHYSICS_STATUS: OPEN_v0_ACTIVE_PREEXECUTION`
- `PILLAR-STAT_GOVERNANCE_STATUS: OPEN_v0_REQUIRED_ROWS_BLOCKED_EXECUTION`
- `PROCEED_GATE_STAT: BLOCKED_v0_PHYSICS_NOT_CLOSED`
- `MATRIX_CLOSURE_GATE_STAT: BLOCKED_v0_GOVERNANCE_NOT_CLOSED`
- `REQUIRED_STAT_CLOSURE_ROWS: TOE-STAT-DER-01,TOE-STAT-DER-02`

Closure-prep control surfaces:
- `formal/docs/release/PILLAR_STAT_CLOSURE_PREP_CHECKLIST_v0.md`
- `formal/docs/release/PILLAR_STAT_CLOSURE_CHANGESET_TEMPLATE_v0.md`
- `formal/python/tests/test_stat_dual_closure_posture_gate.py`
- `formal/python/tests/test_stat_closure_changeset_template_structure_gate.py`

Boundary note:
- This handoff does not authorize `ACTIVE -> CLOSED`.
- Full closure still requires discharged adjudication tokens, non-placeholder required STAT closure rows, and matrix/roadmap synchronization in one bounded change set.

## Activation Execution Attestation (2026-02-26)

Status note:
- This attestation records the first structural activation patch for `PILLAR-STAT` (`LOCKED -> ACTIVE`) under pre-discharge placeholder authority tokens.
- This attestation is not a STAT derivation discharge claim and does not assert adequacy completion.

Executed checks:
- Preflight (`LOCKED` posture): `formal/python/tests/test_stat_unlock_readiness_pack_gate.py`
- Post-activation validation (`ACTIVE` posture):
  - `formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
  - `formal/python/tests/test_authority_token_single_definition_gate.py`
  - `formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py`
  - `formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py`
  - `formal/python/tests/test_pillar_status_matrix_consistency_gate.py`
  - `formal/python/tests/test_results_table_integrity.py`
- Pinned governance suite (`governance_suite.ps1`) passed in activation-patch validation lane.

Attestation tokens (executed):
- `PILLAR-STAT_UNLOCK_DECISION_v0: GO`
- `PILLAR-STAT_UNLOCK_PREREQ_CHECK_v0: PASS`
- `PILLAR-STAT_UNLOCK_WIRING_CHECK_v0: PASS`
- `PILLAR-STAT_UNLOCK_GOVERNANCE_SUITE_v0: PASS`
- `PILLAR-STAT_UNLOCK_NONCLAIM_BOUNDARY_v0: PASS`
- `PILLAR-STAT_UNLOCK_NOTES_v0: STRUCTURAL_ACTIVATION_ONLY_PRE_DISCHARGE_PLACEHOLDER_TOKENS_PINNED`
