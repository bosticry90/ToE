# PILLAR-STAT Activation Changeset Template v0

Spec ID:
- `PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0`

Classification:
- `P-POLICY`

Purpose:
- Constrain the first `PILLAR-STAT` `LOCKED -> ACTIVE` patch to an explicit, reviewable, bounded fileset.
- Pin exact validation commands before and after the activation edit so lock-scoped readiness gates are not misapplied post-flip.

Non-claim boundary:
- planning/execution-template artifact only.
- non-claim control surface.
- not an activation by itself.
- does not authorize adjudication discharge.
- does not authorize claim-label promotion in `RESULTS_TABLE_v0.md`.

Canonical anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`
- `State_of_the_Theory.md`
- `formal/docs/release/PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0.md`
- `formal/python/tests/test_stat_unlock_readiness_pack_gate.py`

## Preconditions (must be true before preparing activation patch)

1. `PILLAR-STAT` remains `LOCKED`.
2. STAT readiness pack is green under locked posture (`formal/python/tests/test_stat_unlock_readiness_pack_gate.py`).
3. Reserved STAT closure rows remain placeholders (`TOE-STAT-DER-01`, `TOE-STAT-DER-02`) and are not promoted.
4. STAT authority token preset lock is green (`formal/python/tests/test_stat_authority_token_preset_lock_gate.py`).
5. No adjudication token in non-STAT pillars is modified.

## Mandatory Files To Touch (single atomic activation change set)

1. `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
   - Change the canonical `PILLAR-STAT` row status from `LOCKED` to `ACTIVE`.
   - Add exactly one mirror definition for the two STAT authority tokens (same values as matrix/state/STAT target doc).
   - Preserve `PILLAR-COSMO` as `LOCKED`.

2. `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
   - Add/register `PILLAR-STAT` matrix row (required by `test_pillar_matrix_roadmap_coverage_gate.py` once roadmap status becomes `ACTIVE`).
   - Required keys must be present:
     - `discharge_doc`
     - `full_derivation_token`
     - `inevitability_token`
     - `consistency_gate`
     - `legacy_retirement_gate`
     - `full_derivation`
     - `inevitability`
     - `matrix_status`
   - `matrix_status` must be `ACTIVE`.
   - `full_derivation` / `inevitability` values must be synchronized placeholders and must not use the legacy forbidden prefix `NOT_YET_`.

3. `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`
   - Preserve the pre-pinned STAT authority token definitions (names + placeholder values) exactly as declared in locked readiness.
   - Values must match matrix + roadmap + state exactly if mirrored during activation.
   - Preserve non-claim boundary and no-discharge language.

4. `State_of_the_Theory.md`
   - Add exactly one mirror definition each for the two STAT authority tokens named in the matrix row.
   - Add a bounded activation checkpoint note (no discharge claim, no adequacy claim).

## Optional File To Touch (attestation only; do not expand scope)

1. `formal/docs/release/PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0.md`
   - Record unlock decision tokens/notes after validation.
   - Do not rewrite gate semantics during the activation patch.

## Forbidden Edits In This Activation Patch

- Do not modify `PILLAR-COSMO` status.
- Do not promote `TOE-STAT-DER-01` or `TOE-STAT-DER-02` out of `P-POLICY`.
- Do not add STAT theorem/evidence artifacts (`formal/output/stat_evidence_checkpoint_cycle01_v0.json`) in this patch.
- Do not alter adjudication tokens for `PILLAR-QFT`, `PILLAR-QM`, `PILLAR-GR`, `PILLAR-EM`, or `PILLAR-SR`.
- Do not broaden STAT scope into cosmology / QFT-statistical / black-hole / holographic claims.

## Pinned STAT Authority Tokens (no naming decisions remain)

Pinned token names:
- `PILLAR_STAT_FULL_DERIVATION_DISCHARGE_ADJUDICATION`
- `PILLAR_STAT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION`

Pinned placeholder value (non-discharged; legacy-safe):
- `ACTIVE_PREEXECUTION_v0_NONDISCHARGED`

Locked-stage preset source:
- `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`
- `formal/python/tests/test_stat_authority_token_preset_lock_gate.py`

Token sync requirement:
- Each token is defined exactly once in:
  - `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`
  - `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
  - `State_of_the_Theory.md`
- Matrix row values match the same token values exactly.

## Exact Validation Commands

### A. Preflight (LOCKED posture; run before editing)

This command is lock-scoped and is expected to fail after a successful activation flip:

```powershell
python -m pytest formal/python/tests/test_stat_unlock_readiness_pack_gate.py
```

### B. Post-activation validation (ACTIVE posture; run after editing)

This command intentionally excludes lock-scoped STAT readiness-pack gates and instead validates the activation patch wiring:

```powershell
python -m pytest formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_authority_token_single_definition_gate.py formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py formal/python/tests/test_pillar_status_matrix_consistency_gate.py formal/python/tests/test_results_table_integrity.py
```

### C. Optional combined validation (ACTIVE posture + retained STAT structural guards)

Use only after activation if lock-scoped tests are excluded:

```powershell
python -m pytest formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_authority_token_single_definition_gate.py formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py formal/python/tests/test_pillar_status_matrix_consistency_gate.py formal/python/tests/test_results_table_integrity.py formal/python/tests/test_stat_readiness_placeholder_structure_gate.py
```

## Patch Review Checklist (activation diff only)

- `PILLAR-STAT` changed to `ACTIVE` in roadmap and matrix only (status parity preserved).
- STAT authority tokens exist exactly once in roadmap/state/STAT target doc.
- STAT matrix row token names and values match all mirrored surfaces.
- No non-STAT adjudication token values changed.
- No STAT placeholder closure row promotions were introduced.

## Activation Attestation Template (to fill after post-activation validation)

- `PILLAR-STAT_ACTIVATION_CHANGESET_PRECHECK_v0: PASS | FAIL`
- `PILLAR-STAT_ACTIVATION_CHANGESET_WIRING_v0: PASS | FAIL`
- `PILLAR-STAT_ACTIVATION_CHANGESET_POSTGATES_v0: PASS | FAIL`
- `PILLAR-STAT_ACTIVATION_CHANGESET_SCOPE_BOUNDARY_v0: PASS | FAIL`
- `PILLAR-STAT_ACTIVATION_CHANGESET_NOTES_v0: <bounded rationale>`
