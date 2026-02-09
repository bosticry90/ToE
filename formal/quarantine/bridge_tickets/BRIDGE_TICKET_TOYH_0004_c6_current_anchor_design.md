# BRIDGE_TICKET_TOYH_0004 — C6 current-anchor bridge extension (Toy-H) [DESIGN-ONLY]

Status: Design-only preimplementation (falsifiable plan; bounded)

Opened: 2026-02-05

## Bridge family taxonomy (governance; docs-only)

- Bridge class: gauge_current_anchor_compatibility
- Evidence strength: bounded_design_preimplementation
- Degrees of freedom: pinned tiny-shear probe, pinned current-anchor operator, pinned tolerance bundle
- Falsification mode: design pre-gate cannot target `mismatch_toyh_current_only` under pinned artifacts
- Non-implication clause: this ticket records design intent only; no runtime bridge implementation or physics claim

## Why this ticket exists (mismatch-driven design)

Source artifacts:
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json`

Selected target mismatch region:
- `mismatch_toyh_current_only`

Pinned target probe:
- `stress_toyh_current_control`

Rationale:
- The remaining Toy-H-only mismatch is localized to current-channel control sensitivity, not phase invariance.
- A dedicated current-anchor proxy can resolve tiny-shear control failures without changing legacy channel semantics.

## Proposed observable (design only)

- Observable ID (planned): `TOYH_C6_current_anchor_proxy_v1`
- Definition sketch: normalized x-current response under pinned local-phase-shear, with explicit anchor-error and response-min guards.
- Scope limits:
  - design_only
  - no_new_canonical_surface
  - no_physics_claim

## Planned negative controls (implementation target)

1. Zero-shear control must fail anchor-response minimum.
2. Wrong operator sign must fail anchor-match tolerance.
3. Amplitude scaling must fail invariance tolerance.

## Planned program impact rule

Success criterion after implementation:
- program-level `nonredundant` remains `true` on raw channels, and
- `mismatch_toyh_current_only` is eliminated on pinned probes,
- without introducing new fail-fail inflation in unrelated probe classes.

## Pre-gate feasibility artifact

- `formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_anchor_feasibility.json`

## Evidence (design pre-gate)

- `formal/python/tests/test_bridge_toyh_c6_current_anchor_feasibility_determinism.py::test_bridge_toyh_c6_current_anchor_feasibility_is_deterministic`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_feasibility_pointers_exist.py::test_bridge_toyh_c6_current_anchor_feasibility_artifact_pointers_exist`

## Exit condition for this design ticket

- Pre-gate feasibility is `found=true`.
- Then open implementation ticket (separate bounded ticket) for executable tests + boundary report + manifest updates.

## Failure posture

- If pre-gate feasibility is false, do not implement Toy-H_0004; first close the listed prerequisites.

