# Post-Slice-B Execution Packet v0

Spec ID:
- `POST_SLICE_B_EXECUTION_PACKET_v0`

Date:
- `2026-03-20`

Purpose:
- Convert post-Slice-B strategy into an explicit execution packet with strict phase labeling, stop conditions, and anti-regrowth controls.

Non-claim boundary:
- Execution governance artifact only.
- No theorem adjudication change by itself.

## Phase A - Boundary Lock

Authority baseline:
1. `formal/docs/release/SCIENTIFIC_CORE_EXTRACTION_MEMO_v0.md`
2. `formal/docs/release/SLICE_B_GR_QM_SEAM_IMPLEMENTATION_BRIEF_v0.md`

Decision lock:
- GR-QM remains frozen at Slice B.
- Default next science lane is GR01 theorem compression.
- GR-QM Slice C is not opened automatically.

Stop condition:
- Do not touch seam theorem surfaces unless post-slice decision review explicitly reauthorizes re-entry.

## Phase B - Bounded GR01 Brief

Required brief fields:
1. One local bottleneck theorem family.
2. One minimal file envelope.
3. One fixed focused validation ladder.
4. One anti-widening policy.
5. One measurable acceptance rule.

Primary surface:
- `formal/toe_formal/ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean`

Reference witness surface:
- `formal/toe_formal/ToeFormal/Variational/ActionToFirstVariationBridgeRep32.lean`

Mirror surface:
- `formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`

Abort widening if progress requires any of:
- fourth science file,
- roadmap or state edits,
- new gate family,
- broad variational refactor.

## Phase C - Execute GR01 Compression

Objective:
- Replace scaffold-conditional closure with stronger action-native constructive closure under bounded weak-field assumptions.

Success profile:
1. theorem-body substance exceeds packaging edits,
2. shortcut dependency burden is reduced,
3. unresolved debt becomes clearer and narrower.

Anti-regrowth rule for science slices:
- If governance/control growth exceeds science-core theorem content growth, rescope immediately.

## Phase D - Validate GR01 Fixed Ladder

Run only:
1. `./py.ps1 -m pytest -q formal/python/tests/test_gr01_full_derivation_discharge_gate.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_gr01_inevitability_gate.py`
3. `./py.ps1 -m pytest -q formal/python/tests/test_gr01_action_operator_discharge_gate.py`
4. `./py.ps1 -m pytest -q formal/python/tests/test_gr01_publication_grade_discharge_package_gate.py`

Rule:
- Do not run broader suites inside bounded slice execution unless the fixed ladder is already green.

## Phase E - Post-GR01 Decision Review

Allowed outcomes only:

Outcome 1 - one more GR01 slice:
- remaining blocker is local,
- theorem-bearing content remains dominant,
- no new control family required,
- proof route is becoming shorter or denser.

Outcome 2 - pivot to QM compression:
- next GR step widens assumptions too much,
- next GR step requires broad bridge/refactor scope,
- next GR step is mostly packaging.

Decision memo must record:
1. theorem bottleneck addressed,
2. exact files changed,
3. exact gates run,
4. remaining blocker,
5. reason for next lane.

## Phase F - QM Compression (if GR pauses)

Primary surfaces:
1. `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
2. `formal/toe_formal/ToeFormal/QM/QMFullDerivationScaffold.lean`

Mirror surface:
- `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md`

Objective:
- tighten constructive evolution semantics,
- minimize assumption burden,
- preserve bounded-envelope discipline.

## Phase G - QFT Scalar Re-entry

Re-entry condition:
- only after single-pillar theorem-depth strengthening is complete.

Do not reopen for readiness packaging.

Allowed QFT objective:
- theorem linkage and compatibility-strength improvement.

Primary surfaces:
1. `formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md`
2. `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0.md`
3. `formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md`
4. `formal/output/toe_qft_scalar_field_equations_v0.json`

## Phase H - GR-QM Re-entry Bar

Default:
- no automatic GR-QM re-entry.

Reopen only for semantics-rich content:
1. typed witness invariants,
2. stronger semantic predicates,
3. structurally meaningful bridge theorems.

Not sufficient:
- additional tag transport,
- package elaboration,
- seam packaging-only growth.

Primary future surfaces:
1. `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`
2. `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean`

## Phase I - Infrastructure Simplification Program

Execution boundary:
- Never share a patch set with active theorem work.

Recommended order:
1. manifest extraction in `governance_suite.ps1`,
2. token/adjudication registries from `ARCHITECTURE_SCHEMA_v1.json`,
3. checkpoint authority registry so `State_of_the_Theory.md` is a consumer,
4. helper consolidation,
5. archive separation of legacy micro families,
6. scientific/operational doc split.

Hard anti-regrowth rule:
- No simplification phase may increase the number of manually authoritative surfaces.

## Phase J - End-of-Slice Memo Discipline

Every science slice must close with a compact memo containing:
1. bottleneck addressed,
2. exact files changed,
3. exact validations run,
4. unresolved blocker,
5. reason for next lane.

Operational non-negotiable:
- Do not allow mixed theorem-plus-infrastructure patch sets.
