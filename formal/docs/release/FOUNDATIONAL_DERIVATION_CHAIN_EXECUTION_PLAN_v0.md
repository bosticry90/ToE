# Foundational Derivation Chain Execution Plan v0

Spec ID:
- `FOUNDATIONAL_DERIVATION_CHAIN_EXECUTION_PLAN_v0`

Classification:
- `P-POLICY`

Purpose:
- Convert the newly standardized derivation chain and candidate master action into executable next steps.
- Separate completed bootstrap work from remaining rollout work.
- Define a hybrid concurrent/sequential execution schedule aligned to M2/M3/M4 posture.

Non-claim boundary:
- planning/control artifact only.
- does not promote theorem labels by itself.
- does not certify empirical adequacy by itself.
- does not authorize comparator-lane expansion by itself.

Canonical anchors:
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md`
- `formal/docs/release/MASTER_ACTION_MATURITY_PILLAR_INTEGRATION_ACTION_PLAN_v0.md`
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`
- `formal/python/tests/test_foundational_derivation_chain_coverage_gate.py`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`

## Current completion status (already done)

1. Repo-wide chain standard is created and pinned:
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md`

2. Candidate master action is created and explicitly non-canonical:
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`

3. Coverage gate exists and is wired:
- `formal/python/tests/test_foundational_derivation_chain_coverage_gate.py`
- `governance_suite.ps1`

4. M3 lane token backfill is complete for 7 pillars:
- `DERIVATION_TARGET_QM_M3_COMPLETION_PROMOTION_v0.md`
- `DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md`
- `DERIVATION_TARGET_STAT_M3_COMPLETION_PROMOTION_v0.md`
- `DERIVATION_TARGET_COSMO_M3_COMPLETION_PROMOTION_v0.md`
- `DERIVATION_TARGET_EM_M3_COMPLETION_PROMOTION_v0.md`
- `DERIVATION_TARGET_QFT_M3_COMPLETION_PROMOTION_v0.md`
- `DERIVATION_TARGET_SR_M3_COMPLETION_PROMOTION_v0.md`

## Remaining execution scope

### Track A (concurrent now): Mathematical consolidation

Target outcome:
- Candidate master action becomes seam-explicit and lane-auditable without canonical promotion.

Action items:
1. Create seam-constraint registry draft:
- add `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- enumerate `C_k` classes: compatibility, bridge admissibility, transport consistency, regime-interface bounds.

2. Add per-pillar mapping section:
- for each pillar, map `C_k` classes to current theorem/target surfaces.

3. Add assumption-minimization delta log:
- declare which terms remain policy-level versus theorem-linked.

Acceptance gate additions:
- `formal/python/tests/test_toe_master_action_seam_registry_gate.py`
- `formal/python/tests/test_toe_master_action_assumption_classification_gate.py`

### Track B (concurrent now): Computational testing in bounded shadow lanes

Target outcome:
- Non-authoritative numerical pressure tests exist for operator/residual stability and regime scans.

Action items:
1. Create bounded shadow-lane target:
- add `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_v0.md`
- enforce `RUN_BOUNDED_v0_NONCLAIM` posture and no promotion semantics.
- bind Track B to:
	- `formal/docs/release/GROUNDED_SPECULATION_POSTURE_STANDARD_v0.md`
	- `formal/docs/release/COMPUTATIONAL_ANALYSIS_BOUNDED_AUTHORIZATION_CLASS_20260416_v0.json`
	- `formal/docs/release/COMPUTATIONAL_ANALYSIS_LANE_EXECUTION_POLICY_20260416_v0.md`
	- `formal/python/tests/test_computational_analysis_lane_policy_gate.py`
- treat Track B outputs as auxiliary computational-analysis artifacts, not lane reopen or packet authorization.

2. Pin first concrete computational-analysis packet:
- add `formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md`
- add `formal/output/qm_stat_rl10_computational_analysis_packet_01_v0.json`
- bind the packet to declared RL10 bridge surfaces only:
	- `formal/docs/release/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_PACKET_20260412_v0.json`
	- `formal/docs/release/QM_STAT_RL10_INTERFACE_TRANSFORMATION_PACKET_20260411_v0.json`
- constrain Packet-01 to `INCONCLUSIVE_v0` only with retain/prune notes treated as subordinate classificatory annotations.
- add `formal/python/tests/test_qm_stat_rl10_computational_analysis_packet_01_gate.py`

3. Add first-run artifact contract:
- add `formal/output/toe_master_action_shadow_numerics_cycle01_v0.json` schema contract doc.

4. Add numerical gate scaffold:
- add `formal/python/tests/test_toe_master_action_shadow_numerics_cycle01_gate.py`

Acceptance criteria:
- artifact includes operator stability summary, residual stability summary, regime-limit scan summary.
- first concrete packet is tied to one existing declared seam/model need and remains deterministic/local.
- Packet-01 remains `INCONCLUSIVE_v0` with no probe-readiness, comparator-binding confirmation, or restart drift.
- no promotion/adjudication token drift.
- no restart, blocker-movement, or live packet authorization drift.

### Track C (concurrent with stabilization): Prediction scaffolding aligned to M3

Target outcome:
- At least one bounded discriminator template per pillar linked to residual-law outputs.

Action items:
1. Create prediction scaffold target:
- add `formal/docs/release/FOUNDATIONAL_PREDICTION_SCAFFOLD_PLAN_v0.md`

2. Define discriminator template fields:
- residual observable definition
- alternative-theory comparator field
- elimination criterion
- uncertainty and bounded validity window

3. Cross-pin into existing M3 targets:
- each M3 target gets a `*_PREDICTION_SCAFFOLD_STATUS_v0` token.

Acceptance gate additions:
- `formal/python/tests/test_foundational_prediction_scaffold_coverage_gate.py`

### Track D (sequential after initial stabilization, overlaps M3): Empirical comparison

Target outcome:
- Bounded empirical comparison packets that can prune alternatives without over-claim.

Action items:
1. Create empirical comparison protocol:
- add `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`

2. Define first comparison packet target:
- add `formal/docs/paper/DERIVATION_TARGET_TOE_EMPIRICAL_COMPARISON_PACKET_01_v0.md`

3. Add packet gate:
- `formal/python/tests/test_toe_empirical_comparison_packet_01_gate.py`

Acceptance criteria:
- packet links artifact -> bridge -> prediction -> discriminator outcome.
- outcome restricted to bounded `retain/prune/inconclusive` semantics.

## Enforcement expansion backlog (highest leverage)

1. Extend chain-stage gate coverage from M3 docs to:
- M2 completion promotion docs.
- M4 seam-closure promotion docs.
- full-derivation discharge docs where applicable.

2. Add chain-status matrix surface:
- add `formal/docs/paper/FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json`
- one row per lane with seven stage columns.

3. Add matrix consistency gate:
- `formal/python/tests/test_foundational_derivation_chain_matrix_consistency_gate.py`

## Execution order

Phase 1 (immediate, concurrent):
1. Track A items 1-3.
2. Track B items 1-3.
3. Track C items 1-2.

Phase 2 (after first stabilization checkpoint):
1. Track C item 3 and prediction coverage gate.
2. Track D protocol and packet-01 target.

Phase 3 (hardening):
1. Enforcement expansion backlog items 1-3.
2. Full governance suite inclusion for all new gates.

## Completion definition for this plan

This plan is complete when:
- seam registry + shadow numerics + prediction scaffold + empirical protocol docs exist and are pinned.
- corresponding gates exist and pass.
- chain-stage matrix exists and is synchronized with canonical state/roadmap surfaces.
- no non-claim boundary violations are introduced.
