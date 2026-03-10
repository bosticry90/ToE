# Foundational Derivation Chain Standard v0

Spec ID:
- `FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0`

Classification:
- `P-POLICY`

Purpose:
- Standardize one repo-wide derivation grammar for derivation-grade lanes.
- Make stage coverage auditable across pillars.
- Prevent hidden stage skipping between action surfaces and regime-limit outputs.

Non-claim boundary:
- planning/control artifact only.
- does not prove any theorem by itself.
- does not promote claim labels by itself.
- does not discharge pillar closure by itself.
- does not authorize comparator-lane expansion by itself.

Canonical anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`
- `formal/python/tests/test_foundational_derivation_chain_coverage_gate.py`

Canonical derivation chain (v0):
- `ACTION`
- `VARIATION`
- `BRIDGE`
- `OPERATOR`
- `TRANSPORT`
- `RESIDUAL_LAW`
- `REGIME_LIMIT`

Stage definitions (plain-language, binding vocabulary):
- `ACTION`: extremized object surface and explicit scope assumptions.
- `VARIATION`: formal stationarity/variation route that extracts dynamics obligations.
- `BRIDGE`: witness/constructor mapping that carries variation outputs into operator-valid form.
- `OPERATOR`: machine-checkable operator equation surface.
- `TRANSPORT`: theorem route transporting operator structure across allowed interfaces.
- `RESIDUAL_LAW`: physically recognizable law-form residual/equation surface.
- `REGIME_LIMIT`: bounded limit where the residual law is interpreted as GR/QM/EM/STAT/COSMO behavior.

## Standard rules

### 1) Applicability rule
This standard is mandatory for derivation-grade lanes and full-derivation discharge lanes.
- Recommended lane scope: one lane token per target/pillar route (for example `GR01`, `QM_EVOLUTION`, `EM_U1`).

### 2) Required stage token bundle rule
Each admitted lane must pin all seven stage-status tokens:
- `<LANE>_ACTION_STAGE_STATUS_v0`
- `<LANE>_VARIATION_STAGE_STATUS_v0`
- `<LANE>_BRIDGE_STAGE_STATUS_v0`
- `<LANE>_OPERATOR_STAGE_STATUS_v0`
- `<LANE>_TRANSPORT_STAGE_STATUS_v0`
- `<LANE>_RESIDUAL_LAW_STAGE_STATUS_v0`
- `<LANE>_REGIME_LIMIT_STAGE_STATUS_v0`

Allowed stage-status values:
- `NOT_STARTED_v0`
- `SCAFFOLD_PINNED_v0`
- `RUN_BOUNDED_v0_NONCLAIM`
- `COMPLETE_BOUNDED_v0`
- `DISCHARGED_v0_DERIVATION_GRADE`

### 3) Admissible progression rule
Progression must be forward and explicit.
- A downstream stage may not be marked `COMPLETE_BOUNDED_v0` or `DISCHARGED_v0_DERIVATION_GRADE` when its immediate predecessor is `NOT_STARTED_v0`.
- Non-monotone stage rollback requires an explicit reopen token in the lane target doc.

### 4) Anti-shortcut rule
Direct regime claims without operator/transport coverage are prohibited in derivation-grade status surfaces.
- `REGIME_LIMIT` status may be `SCAFFOLD_PINNED_v0`, but not `DISCHARGED_v0_DERIVATION_GRADE`, unless `OPERATOR`, `TRANSPORT`, and `RESIDUAL_LAW` are at least `COMPLETE_BOUNDED_v0`.

### 5) Cross-surface synchronization rule
For each lane, the same seven stage-status tokens must be synchronized in:
- lane target document.
- canonical state surface (`State_of_the_Theory.md`).
- enforcement output/gate artifacts where applicable.

### 6) Enforcement gate rule
Coverage and ordering checks are enforced by:
- `formal/python/tests/test_foundational_derivation_chain_coverage_gate.py`

## Initial rollout posture (v0)

- This v0 standard authorizes bounded scaffold-first rollout.
- Existing lanes may adopt token scaffolds before any discharge-status promotion.
- No existing adjudication token is changed by this file.
