# Master Action Maturity Pillar Integration Action Plan v0

Spec ID:
- `MASTER_ACTION_MATURITY_PILLAR_INTEGRATION_ACTION_PLAN_v0`

Classification:
- `P-POLICY`

Purpose:
- Integrate the master-action convergence thesis into the existing pillar deep-maturity workflow.
- Treat action-level unification, derivation grammar closure, seam constraints, and empirical discrimination as one governed execution stack.
- Preserve bounded non-claim posture while increasing falsifiability pressure.

Non-claim boundary:
- planning/control artifact only.
- does not promote theorem labels by itself.
- does not claim external physical truth by itself.
- does not alter matrix closure by itself.
- does not authorize empirical adjudication promotion by itself.

Canonical anchors:
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md`
- `formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md`
- `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
- `formal/docs/paper/FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json`
- `formal/python/tests/test_foundational_derivation_chain_coverage_gate.py`
- `formal/python/tests/test_toe_master_action_seam_registry_gate.py`
- `formal/python/tests/test_packet02_m4_seam_coupling_gate.py`

## Strategic framing

Working hypothesis to operationalize:

1. One candidate master action drives cross-domain derivations.
2. One canonical derivation grammar is reused across pillars.
3. Known law surfaces are regime-limit residuals.
4. Seam constraints carry the unification burden across pillars.

Execution principle:
- The program advances only by artifact+gate parity and discriminator outcomes, never by narrative convergence alone.

## Standardized derivation grammar contract

Canonical chain:
- `action -> variation -> bridge -> operator -> transport -> residual_law -> regime_limit`

Integration requirements:
1. Each active deep-maturity target must pin all seven chain-stage status tokens.
2. Missing stage tokens are treated as integration debt, not optional metadata.
3. Stage-token parity must hold across target doc, roadmap surface, state surface, and matrix row.

Primary enforcement surface:
- `formal/python/tests/test_foundational_derivation_chain_coverage_gate.py`

## Maturity-pillar integration map (M1-M5)

### M1 (theorem closed)

Objective:
- keep theorem closure explicit and bounded under assumption discipline.

Action package:
1. For each pillar, ensure M1 target rows reference derivation-chain stages through theorem endpoints.
2. Ensure any action-level dependency is assumption-classified and non-promotional.

### M2 (derivation complete)

Objective:
- force per-pillar derivation completeness to trace back to the master-action chain.

Action package:
1. Require all M2 completion rows to include explicit mapping from pillar derivation to chain stages.
2. Require an assumption-minimization delta note for each M2 promotion tranche.

### M3 (empirically discriminative)

Objective:
- shift from "comparison exists" to "alternative structures are pressure-tested and pruned/retained".

Action package:
1. Ensure each pillar has packet-02 (or later) discriminator semantics with explicit decision eligibility.
2. Require non-inconclusive outcomes to include decision records and pointer parity.
3. Keep decision-balance guard active to prevent one-sided collapse artifacts.

### M4 (cross-pillar inevitable)

Objective:
- treat seam constraints as first-class closure obligations.

Action package:
1. Seam classes are explicitly mapped to pillar interfaces (`GR<->QM`, `QM<->STAT`, `EM<->QFT`, `SR<->COSMO`, plus any newly admitted seam).
2. Every M4 row must pin stage-complete seam bundles (`action/variation/bridge/operator/transport/residual/regime`).
3. Seam failure is classified as maturity-blocking, equivalent to theorem-chain failure for M4 posture.

### M5 (theory-parity linked)

Objective:
- maintain hash-pinned parity across state/roadmap/target/registry while preserving bounded non-claim posture.

Action package:
1. Keep active M5 parity artifact synchronization policy unchanged.
2. Ensure any master-action integration token entering M5 surfaces is mirrored on all canonical parity surfaces in one change set.

## Anti-steering and anti-hallucination controls

1. Adversarial lane requirement:
- Every major master-action refinement must include at least one explicit counterfactual or failure-mode lane.

2. Structural-bias declaration:
- Each tranche must state whether conclusions are action-principle-dependent or action-principle-robust.

3. Reproduction-vs-novelty split:
- Artifacts must separate known-physics reproduction claims from novel discriminator claims.

4. Selection-bias controls:
- Rejected derivation paths remain recorded as retained negatives (not silently dropped).

## Four immediate execution moves

1. Canonical master-action expression discipline:
- Keep one bounded candidate expression as canonical working object.
- Treat modifications as tranche-based revisions with explicit assumption deltas.

2. Grammar standard hardening:
- Enforce seven-stage chain tokens across all active pillar maturity targets.

3. Seam-first governance:
- Promote seam constraints to maturity-critical status in M4 and packet-02 coupling checks.

4. Discriminator pressure acceleration:
- Prioritize empirical packets that distinguish between candidate master-action variants, not only versus null baselines.

## Milestones and completion signals

Milestone A (integration wiring complete):
- plan is cross-pinned in state and deep-maturity program surfaces.

Milestone B (grammar parity complete):
- all active maturity rows pin the seven-stage chain without drift findings.

Milestone C (seam-first closure complete):
- seam constraints are enforced as M4 blocking conditions with passing gates.

Milestone D (discriminator pressure live):
- packet artifacts include variant-discrimination outcomes with bounded retain/prune semantics.

## Dedicated gate checklist (copy-paste tranche template)

Use this checklist before running focused gates.

### A) Foundational derivation chain coverage gate

Gate path:
- `formal/python/tests/test_foundational_derivation_chain_coverage_gate.py`

Required global anchors:
- `FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0`
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md`
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`

Required stage token names (per lane):
- `<LANE>_ACTION_STAGE_STATUS_v0`
- `<LANE>_VARIATION_STAGE_STATUS_v0`
- `<LANE>_BRIDGE_STAGE_STATUS_v0`
- `<LANE>_OPERATOR_STAGE_STATUS_v0`
- `<LANE>_TRANSPORT_STAGE_STATUS_v0`
- `<LANE>_RESIDUAL_LAW_STAGE_STATUS_v0`
- `<LANE>_REGIME_LIMIT_STAGE_STATUS_v0`

Allowed stage values:
- `NOT_STARTED_v0`
- `SCAFFOLD_PINNED_v0`
- `RUN_BOUNDED_v0_NONCLAIM`
- `COMPLETE_BOUNDED_v0`
- `DISCHARGED_v0_DERIVATION_GRADE`

Phase-row synchronization requirement (for each pillar and each phase `m2`, `m3`, `m4` in `FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json`):
- `status_token` value in phase `source_doc` equals `expected_status`
- same `status_token` value is mirrored in `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- same `status_token` value is mirrored in `State_of_the_Theory.md`

### B) Master-action seam registry gate

Gate path:
- `formal/python/tests/test_toe_master_action_seam_registry_gate.py`

Required seam-registry tokens in `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`:
- `TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0`
- `TOE_MASTER_ACTION_SEAM_REGISTRY_STATUS_v0: SCAFFOLD_PINNED_NONCLAIM`
- `TOE_CK_CLASS_COMPATIBILITY_v0`
- `TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0`
- `TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0`
- `TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0`
- `formal/python/tests/test_toe_master_action_seam_registry_gate.py`

Cross-surface pointer parity requirement:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md` contains `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- `State_of_the_Theory.md` contains `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`

### C) Packet-02 M4 seam coupling gate

Gate path:
- `formal/python/tests/test_packet02_m4_seam_coupling_gate.py`

Required matrix surfaces:
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json`
- `formal/docs/paper/FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json`

Required packet artifact payload fields (for non-`INCONCLUSIVE_v0` decisions):
- `decision`
- `m4_seam_closure_pointer`

Coupling requirement for every non-inconclusive lane:
- artifact `payload.m4_seam_closure_pointer` exactly equals phase-row `m4.source_doc`
- pointed seam document exists on disk

## Validation commands

- Full governance suite:
  - `./governance_suite.ps1`

- Focused foundational and seam gates:
  - `./py.ps1 -m pytest -q formal/python/tests -k "foundational_derivation_chain or toe_master_action_seam_registry or packet02_m4_seam_coupling or foundational_empirical_packet02"`

## Completion definition for this plan

This plan is complete when:
- canonical surfaces point to this plan.
- grammar-stage parity is present on active maturity tranches.
- seam constraints are treated as maturity-blocking in M4 enforcement.
- empirical packet lanes show variant discrimination pressure under bounded non-claim semantics.
