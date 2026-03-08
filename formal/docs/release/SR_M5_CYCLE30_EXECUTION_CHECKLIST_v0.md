# SR M5 Cycle30 Execution Checklist v0

Spec ID:
- `SR_M5_CYCLE30_EXECUTION_CHECKLIST_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the next bounded progression step after cycle29 for SR M5 theory-parity-link execution.
- Ensure cycle30 is a distinct audit tranche, not a mechanical rollover.

Non-claim boundary:
- planning-only control artifact.
- no external truth claim.
- no automatic adjudication promotion.

Cycle30 objective token:
- `SR_M5_CYCLE30_OBJECTIVE_v0: LEGACY_LEAKAGE_ZERO_SINGLE_ACTIVE_POINTER_AND_TOKEN_ORDER_STABLE_v0`

Objective definition:
- Require the active SR M5 artifact/gate pointer to appear exactly once on each canonical parity surface.
- Require zero active references to prior cycle artifact/gate pointers on the same parity surfaces.
- Require stable ordering of SR M5 token rows on canonical parity surfaces:
  1. `SR_M5_STATUS_v0`
  2. `SR_M5_THEORY_PARITY_ARTIFACT_v0`
  3. `SR_M5_THEORY_PARITY_SHA256_v0`
  4. `SR_M5_THEORY_PARITY_GATE_v0`
  5. `SR_M5_READINESS_v0`

Canonical parity surfaces in scope:
- `formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`
- `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json`

Execution steps:
1. Clone cycle29 artifact and gate to cycle30 paths.
2. Add cycle30 objective token to the cycle30 artifact payload.
3. Archive cycle29 gate with `pytest.skip` and canonical-cycle30 reason.
4. Retarget canonical pointers (state, roadmap, target, authority, registry, governance suite, and deep-maturity program gate assertions) to cycle30.
5. Recompute and propagate `SR_M5_THEORY_PARITY_SHA256_v0` for cycle30.
6. Enforce uniqueness, no-legacy-leakage, and token-order checks in `test_sr_m5_theory_parity_link_cycle30_gate.py`.
7. Run focused maturity gates.
8. Run full governance suite.
9. Commit and push only with green focused and full-suite evidence.

Focused validation command:
- `./py.ps1 -m pytest formal/python/tests/test_sr_m5_theory_parity_link_cycle30_gate.py formal/python/tests/test_pillar_deep_maturity_program_gate.py formal/python/tests/test_pillar_phase_advancement_gate.py -q`

Full validation command:
- `./governance_suite.ps1`

Exit criteria:
- Cycle30 artifact hash and pointers are synchronized across canonical parity surfaces.
- Active cycle references are unique and legacy leakage checks pass.
- SR M5 token ordering remains stable across canonical parity surfaces.
- Focused maturity gates pass.
- Full governance suite passes.
- Working tree is clean after validation.
