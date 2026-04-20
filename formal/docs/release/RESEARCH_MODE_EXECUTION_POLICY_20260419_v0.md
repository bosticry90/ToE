# Research Mode Execution Policy 2026-04-19 v0

Spec ID:
- `RESEARCH_MODE_EXECUTION_POLICY_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Restore a short, equation-first discovery loop inside the repo.
- Permit bounded local derivations, reductions, simulations, counterexamples, and design-only probes without forcing full governance overhead on each intermediate result.
- Keep research outputs non-canonical until they explicitly pass through the existing sandbox and promotion governance lanes.

Required policy tokens:
- `RESEARCH_MODE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `RESEARCH_MODE_MODEL_v0: RESEARCH_FIRST_WITH_SANDBOX_AND_PROMOTION_BOUNDARY`
- `RESEARCH_MODE_ALLOWED_OUTPUTS_v0: LOCAL_DERIVATION_REDUCTION_SIMULATION_COUNTEREXAMPLE_RETAIN_PRUNE_INCONCLUSIVE_AND_DESIGN_ONLY`
- `RESEARCH_MODE_FORBIDDEN_OUTPUTS_v0: NO_CANONICAL_ROW_MUTATION_NO_RELEASE_GATE_TRUTH_CHANGE_NO_SEAM_CLASS_FLIP_NO_MASTER_ACTION_RECLASSIFICATION_NO_EXTERNAL_TRUTH_CLAIM`
- `RESEARCH_MODE_LOOP_DISCIPLINE_v0: ONE_OBJECT_ONE_QUESTION_ONE_TEST_ONE_OUTPUT`
- `RESEARCH_MODE_MINIMUM_METADATA_SCHEMA_v0: formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `RESEARCH_MODE_RETENTION_POLICY_v0: formal/docs/release/RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md`
- `RESEARCH_MODE_AUTHORITY_MATRIX_v0: formal/docs/release/RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md`
- `RESEARCH_MODE_NAMESPACE_v0: formal/python/research`
- `RESEARCH_MODE_RUNNER_v0: research_mode_execution.ps1`
- `RESEARCH_MODE_GATE_v0: formal/python/tests/test_research_mode_lane_policy_gate.py`
- `RESEARCH_MODE_PROMOTION_BINDING_v0: RESEARCH_OUTPUTS_MUST_PASS_THROUGH_SANDBOX_AND_PROMOTION_GOVERNANCE_BEFORE_CANONICAL_MUTATION`

Allowed actions:
- Run bounded derivation attempts, asymptotic reductions, simulation probes, notation repairs, and smallest-counterexample searches.
- Bind research artifacts to a pillar, seam, or master-action target as advisory-only context.
- Emit repository-local `retain`, `prune`, `inconclusive`, `counterexample`, and design-only outcomes.

Disallowed actions:
- Mutate canonical pillar, seam, target-map, or release-gate truth directly from research output.
- Treat research notes or research JSON outputs as canonical authority surfaces.
- Reclassify seam status, master-action class, or roadmap truth from research output alone.
- Claim scientific adequacy or external truth.

Integration rules:
- Research mode is the default discovery lane for local mathematical work.
- Sandbox remains the first promotable staging lane.
- Promotion governance remains the only path that may authorize canonical mutation.
- Research outputs may carry a scientific delta class, but delta class alone does not promote them.

Canonical bindings:
- `formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md`
- `formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md`
- `formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `formal/docs/release/RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md`
- `formal/docs/release/RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md`
- `formal/python/tests/test_research_mode_lane_policy_gate.py`
- `research_mode_execution.ps1`

Non-claim boundary:
- This policy authorizes bounded research-mode exploration only.
- This policy does not authorize canonical promotion, release-gate truth changes, or external scientific claims.