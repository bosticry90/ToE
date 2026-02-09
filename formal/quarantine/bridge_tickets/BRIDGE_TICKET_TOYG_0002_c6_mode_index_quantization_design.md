# BRIDGE_TICKET_TOYG_0002 — C6 mode-index quantization proxy (Toy-G) [DESIGN-ONLY]

Status: Design-only preimplementation (falsifiable plan; bounded)

Opened: 2026-02-04

## Bridge family taxonomy (governance; docs-only)

- Bridge class: topological_mode_index_quantization
- Evidence strength: bounded_design_preimplementation
- Degrees of freedom: pinned periodic loop; pinned FFT mode extraction rule; pinned resolution set
- Falsification mode: pre-gate feasibility fails OR planned orthogonality impact cannot be measured under pinned probes
- Non-implication clause: this ticket records design intent only; no bridge implementation or physics claim

## Why this ticket exists (mismatch-driven design)

Source mismatch artifact: `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`

Dominant remaining mismatch class includes Toy-G winding-only failures. The first targeted region for elimination is:

- `fail_not_integer_close` (selected target reason-code)

Rationale:
- It is a primary quantization-boundary ambiguity, not an unwrap-guard artifact.
- It is selection-light and can be tested with deterministic pinned probes.

## Proposed observable (design only)

- Observable ID (planned): `TOYG_C6_mode_index_quantization_v1`
- Definition: dominant FFT mode index on a pinned periodic loop extracted from C6 complex field specimen.
- Integer-attractor rule (planned): peak mode index must match nearest pinned integer target under bounded tolerance/alias policy.

This observable is structurally distinct from winding quantization and is intended to reduce `fail_not_integer_close` ambiguity volume.

## Planned negative controls (implementation target)

1. Off-grid mode target (fractional mode) must fail integer closeness.
2. Wrong operator (e.g., mirrored or sign-flipped index extraction) must violate pinned expectation.

## Planned orthogonality impact rule

Success criterion after implementation:

- program-level `nonredundant` remains `true`, and
- mismatch mass in the targeted `fail_not_integer_close` region decreases on pinned probes,
- without inflating unrelated fail-fail cells.

## Pre-gate feasibility artifact

- `formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json`

## Evidence (design pre-gate)

- `formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_determinism.py::test_bridge_toyg_c6_mode_index_feasibility_is_deterministic`
- `formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist.py::test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist`

## Exit condition for this design ticket

- Pre-gate feasibility is `found=true`.
- Then open implementation ticket (separate bounded ticket) for executable tests + boundary report + manifest updates.

## Failure posture

- If pre-gate feasibility is false, do not implement Toy-G_0002; first close the listed prerequisites.
