# Pillar Phase Advancement Standard v0

Spec ID:
- `PILLAR_PHASE_ADVANCEMENT_STANDARD_v0`

Classification:
- `P-POLICY`

Purpose:
- Standardize how pillar progression is declared and enforced.
- Ensure that once a pillar, phase, or bounded milestone is complete, the next required thing is explicitly pinned.
- Prevent silent re-extension of a completed phase without an explicit reopen rule.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- does not assert discharge, adequacy completion, or external truth.

Canonical artifacts:
- standard pointer: `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_STANDARD_v0.md`
- registry pointer: `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json`
- enforcement gate path: `formal/python/tests/test_pillar_phase_advancement_gate.py`

Standard advancement modes:
1. `CLOSED_HANDOFF`
- A closed pillar must pin an explicit next-pillar handoff in canonical state and must not remain progression-ambiguous.
- Optional proceed-gate tokens may be required when the roadmap already defines them.

2. `CLOSED_HANDOFF_ARTIFACT`
- A closed pillar must pin an explicit handoff artifact/gate bundle in addition to the global next-pillar handoff.
- The authority/state surfaces pin the exact handoff token value; the roadmap must at minimum pin the same artifact pointer and gate pointer so handoff intent remains machine-checkable without forcing duplicate token narration.

3. `PHASE_ORDERED`
- If a phase completion token is pinned, the next phase entry token must also be pinned in the authority/state surfaces.
- Phase completion may not coexist with an omitted successor-entry declaration.

4. `ACTIVE_EXECUTION`
- An active pillar must pin the next unfinished execution token and next execution objective.
- If the active phase is marked saturated, the admitted component set is frozen until an explicit reopen token is flipped.

5. `LOCKED_QUEUE`
- A locked pillar must remain wait-only until its pinned prerequisite set closes.
- Locked queue posture must remain explicit in canonical roadmap surfaces.

Registry rule:
- Every pillar subject to this standard must have one registry entry in `PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json`.
- Mode-specific fields are defined by the registry entry and enforced by the generic gate.
