# BRIDGE_TICKET_TOYG_0003 — C6 unwrap-stability bridge extension (Toy-G) [DESIGN-ONLY]

Status: Design-only preimplementation (falsifiable plan; bounded)

Opened: 2026-02-04

## Bridge family taxonomy (governance; docs-only)

- Bridge class: topological_unwrap_stability_compatibility
- Evidence strength: bounded_design_preimplementation
- Degrees of freedom: pinned periodic loop; pinned grid set; pinned unwrap-stability thresholds
- Falsification mode: design pre-gate cannot target the selected mismatch region under pinned artifacts
- Non-implication clause: this ticket records design intent only; no runtime bridge implementation or physics claim

## Why this ticket exists (mismatch-driven design)

Source artifacts:
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json`

Selected target mismatch region:
- `mismatch_toyg_bridge_only`

Current localized Toy-G failure reasons in that region:
- winding channel: `fail_unwrap_discontinuity_guard`
- mode channel: `fail_peak_fraction_low`

Rationale:
- This is the dominant remaining Toy-G-only mismatch class after Toy-G_0002.
- Resolving this region is the highest-leverage next eliminative move without adding new canonical surfaces.

## Proposed observable (design only)

- Observable ID (planned): `TOYG_C6_unwrap_stability_proxy_v1`
- Definition sketch: branch-cut-stable phase increment consistency on the pinned loop, coupled to a minimal spectral-coherence guard.
- Scope limits:
  - design_only
  - no_new_canonical_surface
  - no_physics_claim

## Planned negative controls (implementation target)

1. Coarse-grid/high-winding specimen should fail unwrap-stability guard.
2. Deliberately wrong unwrapping operator should violate pinned expectations.

## Planned orthogonality impact rule

Success criterion after implementation:
- program-level `nonredundant` remains `true`, and
- `mismatch_toyg_bridge_only` count decreases under pinned probes,
- without inflating unrelated fail-fail cells.

## Pre-gate posture

- No new front door is required; C6 typed loop inputs already exist.
- Planned pre-gate artifact: `formal/quarantine/feasibility/BRIDGE_TOYG_C6_unwrap_stability_feasibility.json`
- Implementation is deferred pending explicit pre-gate artifact and bounded test plan.

## Exit condition for this design ticket

- A dedicated pre-gate artifact confirms targetability of `mismatch_toyg_bridge_only`.
- Then open a separate implementation ticket for executable tests + boundary report + manifest/ledger updates.

## Failure posture

- If pre-gate targetability cannot be shown deterministically, do not implement Toy-G_0003.
