# PILLAR-STAT Phase Advancement Contract v0

Spec ID:
- `PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0`

Classification:
- `P-POLICY`

Purpose:
- Enforce forward movement once the current STAT scaffold phase is saturated.
- Prevent silent extension of the completed scaffold phase without an explicit reopen.
- Keep post-activation STAT work pointed at the next unfinished bounded milestone.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- does not assert discharge, adequacy completion, or external truth.

Canonical policy anchors:
- `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_STANDARD_v0.md`
- `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json`
- `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`
- `formal/python/tests/test_stat_row_scaffold_cycle01_aggregation_gate.py`

Advancement contract tokens:
- `STAT_SCAFFOLD_PHASE_COMPLETION_v0: CYCLE01_ROW_AND_TRANSITION_SCAFFOLDS_SATURATED`
- `STAT_NEXT_EXECUTION_PHASE_v0: EVIDENCE_ADEQUACY_AND_DISCHARGE_READINESS`
- `STAT_NEXT_EXECUTION_OBJECTIVE_v0: COMPLETE_5X5_ADEQUACY_INPUTS_BEFORE_FURTHER_SCAFFOLD_EXPANSION`
- `STAT_NEXT_EXECUTION_TOKEN_v0: EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_v0`
- `STAT_NEXT_EXECUTION_TOKEN_STATE_v0: NOT_PRESENT_v0`
- `EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_v0: NOT_PRESENT_v0`
- `STAT_SCAFFOLD_PHASE_COMPONENT_GATE_FREEZE_v0: 43`
- `STAT_SCAFFOLD_PHASE_REOPEN_RULE_v0: EXPLICIT_REOPEN_REQUIRED_BEFORE_COMPONENT_GATE_EXPANSION`
- `STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0: NOT_PRESENT_v0`
- `STAT_PHASE_ADVANCEMENT_GATE_v0: CROSS_SURFACE_PARITY_AND_COMPONENT_FREEZE_REQUIRED`
- advancement contract pointer: `formal/docs/release/PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md`
- global standard pointer: `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_STANDARD_v0.md`
- registry pointer: `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json`
- advancement gate path: `formal/python/tests/test_pillar_phase_advancement_gate.py`

Enforcement semantics:
1. Once `STAT_SCAFFOLD_PHASE_COMPLETION_v0` is pinned, `STAT_NEXT_EXECUTION_PHASE_v0` must point to evidence-adequacy/discharge-readiness work rather than another scaffold-saturation or custody-fanout loop.
2. `STAT_NEXT_EXECUTION_TOKEN_v0` remains the next unfinished milestone until `EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_v0` stops being `NOT_PRESENT_v0`.
3. If `STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0` is `NOT_PRESENT_v0`, the admitted STAT scaffold component gate set is frozen at `STAT_SCAFFOLD_PHASE_COMPONENT_GATE_FREEZE_v0`.
4. Any expansion of the scaffold component gate set requires flipping `STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0` in the same change set.

Current bounded next move:
- Complete the evidence-adequacy/discharge-readiness inputs already scaffolded for STAT before admitting further scaffold-phase expansion.
