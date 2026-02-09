# BRIDGE_TICKET_TOYHG_0001 — C6 Toy-H/Toy-G pair-compatibility extension [DESIGN-ONLY]

Status: Design-only preimplementation (falsifiable plan; bounded)

Opened: 2026-02-05

## Bridge family taxonomy (governance; docs-only)

- Bridge class: joint_pair_compatibility_bridge
- Evidence strength: bounded_design_preimplementation
- Degrees of freedom: pinned joint pass/fail signatures, pinned pair-consistency rule, pinned probe set
- Falsification mode: design pre-gate cannot target `mismatch_toyh_pair_vs_toyg_bridge` under pinned artifacts
- Non-implication clause: this ticket records design intent only; no runtime bridge implementation or physics claim

## Why this ticket exists (mismatch-driven design)

Source artifacts:
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json`

Selected target mismatch region:
- `mismatch_toyh_pair_vs_toyg_bridge`

Pinned target probe:
- `stress_c6_amplitude_scale`

Rationale:
- Remaining mismatch is cross-channel: Toy-H pair fails while Toy-G bridge passes.
- A dedicated joint functional is required to encode pair-level compatibility explicitly instead of patching one channel ad hoc.

## Proposed observable (design only)

- Observable ID (planned): `TOYHG_C6_pair_compatibility_v1`
- Definition sketch: joint compatibility predicate over `(toyh_phase_bridge, toyh_current_bridge, toyg_bridge)` pass/fail tuple on shared pinned probes.
- Scope limits:
  - design_only
  - no_new_canonical_surface
  - no_physics_claim

## Planned negative controls (implementation target)

1. `P-F-P` signature must fail with current-channel localization.
2. `P-P-F` signature must fail with Toy-G localization.
3. `F-F-P` signature must fail with pair-vs-bridge localization.

## Planned program impact rule

Success criterion after implementation:
- pair-channel admissibility is deterministic under pinned signatures, and
- `mismatch_toyh_pair_vs_toyg_bridge` is eliminated from the mismatch frontier,
- while preserving raw-channel nonredundancy audit surfaces.

## Pre-gate feasibility artifact

- `formal/quarantine/feasibility/BRIDGE_TOYHG_C6_pair_compatibility_feasibility.json`

## Evidence (design pre-gate)

- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_feasibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_feasibility_is_deterministic`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_feasibility_pointers_exist.py::test_bridge_toyhg_c6_pair_compatibility_feasibility_artifact_pointers_exist`

## Exit condition for this design ticket

- Pre-gate feasibility is `found=true`.
- Then open implementation ticket (separate bounded ticket) for executable tests + boundary report + manifest updates.

## Failure posture

- If pre-gate feasibility is false, do not implement ToyHG_0001; first close the listed prerequisites.

