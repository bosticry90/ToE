# SR M5 Cycle28 Execution Checklist v0

Spec ID:
- `SR_M5_CYCLE28_EXECUTION_CHECKLIST_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the next bounded progression step after cycle27 for SR M5 theory-parity-link execution.
- Ensure cycle28 is a distinct audit tranche, not a mechanical rollover.

Non-claim boundary:
- planning-only control artifact.
- no external truth claim.
- no automatic adjudication promotion.

Cycle28 objective token:
- `SR_M5_CYCLE28_OBJECTIVE_v0: LEGACY_LEAKAGE_ZERO_AND_SINGLE_ACTIVE_POINTER_v0`

Objective definition:
- Require the active SR M5 artifact/gate pointer to appear exactly once on each canonical parity surface.
- Require zero active references to prior cycle artifact/gate pointers on the same parity surfaces.

Canonical parity surfaces in scope:
- `formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`
- `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json`

Execution steps:
1. Clone cycle27 artifact and gate to cycle28 paths.
2. Add cycle28 objective token to the cycle28 artifact payload.
3. Archive cycle27 gate with `pytest.skip` and canonical-cycle28 reason.
4. Retarget canonical pointers (state, roadmap, target, authority, registry, governance suite, and deep-maturity program gate assertions) to cycle28.
5. Recompute and propagate `SR_M5_THEORY_PARITY_SHA256_v0` for cycle28.
6. Enforce uniqueness and no-legacy-leakage checks in `test_sr_m5_theory_parity_link_cycle28_gate.py`.
7. Run focused maturity gates.
8. Run full governance suite.
9. Commit and push only with green focused and full-suite evidence.

Focused validation command:
- `./py.ps1 -m pytest formal/python/tests/test_sr_m5_theory_parity_link_cycle28_gate.py formal/python/tests/test_pillar_deep_maturity_program_gate.py formal/python/tests/test_pillar_phase_advancement_gate.py -q`

Full validation command:
- `./governance_suite.ps1`

Exit criteria:
- Cycle28 artifact hash and pointers are synchronized across canonical parity surfaces.
- Active cycle references are unique and legacy leakage checks pass.
- Focused maturity gates pass.
- Full governance suite passes.
- Working tree is clean after validation.
