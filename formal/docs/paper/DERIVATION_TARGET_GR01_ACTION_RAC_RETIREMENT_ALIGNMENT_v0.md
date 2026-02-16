# Derivation Target: GR01 Action/RAC Retirement Alignment v0

Spec ID:
- `DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0`

Target ID:
- `TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Freeze a bounded discharge path for the remaining GR01 action/RAC retirement alignment blocker.
- Keep `conditional-publish endpoint` explicit until retirement criteria are discharged.
- Prevent silent drift between "explicit non-retirement posture" and "retired assumptions" narratives.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- no comparator-lane authorization.
- no GR field-equation recovery claim.
- no external truth claim.

## Required Alignment Deliverables (all required)

1. Stance surface remains explicit:
- `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`
- `conditional-publish endpoint`
- explicit `hAction` / `hRAC` posture.

2. Retirement criteria remain explicit and synchronized:
- `BLK-01` and `BLK-02` remain state-visible until discharged.
- replacement-discharge requirements remain explicit:
  - action provenance replacement object,
  - RAC obligation replacement object.

3. Lock pointer set remains pinned:
- `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md`
- `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md`
- `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_bridge_discharge_object_v0.md`

4. Cross-surface synchronization:
- `DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
- `DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md`
- `PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`

## Mandatory Failure Triggers

- missing explicit `conditional-publish endpoint` stance token.
- missing `hAction` or `hRAC` explicit posture.
- missing any locked support pointer listed above.
- removal of `BLK-01`/`BLK-02` blocker mention without replacement discharge artifact.
- cross-surface mismatch about action/RAC retirement posture.

## Discharged Alignment Endpoint Definition (v0 conditional-publish posture)

- Alignment may be marked discharged without retiring `hAction`/`hRAC` only when
  all conditions below are true:
  1. `conditional-publish endpoint` remains explicit in the stance surface.
  2. `BLK-01` and `BLK-02` remain explicit as intentionally deferred retirement
     blockers with pinned replacement-object pointers.
  3. Required lock pointers remain pinned and synchronized across checklist,
     Newtonian target, roadmap, and state inventory.
  4. A single alignment adjudication token is set in this file.

- Alignment adjudication token (machine-checkable):
  - allowed values:
    - `NOT_YET_DISCHARGED`
    - `DISCHARGED_CONDITIONAL_PUBLISH_v0`
  - single token line required:
    - `ALIGNMENT_ADJUDICATION: <allowed value>`
  - transition rule:
    - `ALIGNMENT_ADJUDICATION: DISCHARGED_CONDITIONAL_PUBLISH_v0` requires all
      endpoint conditions above to be satisfied and cross-surface blocker-state
      synchronization.
    - `ALIGNMENT_ADJUDICATION: NOT_YET_DISCHARGED` keeps action/RAC retirement
      alignment blocker-facing.

## v0 Snapshot

- Current retirement posture:
  - explicit non-retirement (`conditional-publish endpoint`).
- Current blocker posture:
  - action/RAC retirement remains explicitly deferred under conditional-publish
    endpoint with pinned replacement-object pointers.
- Current alignment adjudication token (v0):
  - `ALIGNMENT_ADJUDICATION: DISCHARGED_CONDITIONAL_PUBLISH_v0`

## Dependencies

- `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`

## Enforcement Hooks

- `formal/python/tests/test_gr01_dual_closure_and_blockers.py`
- `formal/python/tests/test_pillar_dual_layer_gate_template.py`

## Freeze Policy

- This target does not alter theorem labels.
- This target does not authorize assumption retirement by itself.
- This target does not unlock SR/EM.
