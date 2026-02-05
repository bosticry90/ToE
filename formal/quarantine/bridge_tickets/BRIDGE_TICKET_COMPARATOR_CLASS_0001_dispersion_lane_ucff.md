# BRIDGE_TICKET_COMPARATOR_CLASS_0001 -- Dispersion comparator lane for UCFF diversification [DESIGN-ONLY]

Status: Design-only (no implementation)

Opened: 2026-02-05

Branch: `design/canonical-surface-scan`

## Purpose (bounded)

Define a non-grid comparator class for canonical dispersion surfaces, starting with UCFF, so diversification does not depend on phase/current/pair grid mapping.

This ticket is the selected blocker-cycle exit family:
- `R5`: classify UCFF as non-grid canonical and route to a new comparator class.

No implementation ticket is minted in this cycle.

## Triggering evidence (path-pinned)

- `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_BLOCKER_0002_phase_action_grid_surface.md`
  - selected resolution family: `R5`
- `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_DIVERSIFY_0002_grid_shaped_target_discovery.md`
  - D2/D3 outcome: non-C6 feasible candidates = 0 under Form A/B requirement
- `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json`
  - `sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`
- `formal/python/toe/ucff/core_front_door.py`
- `formal/docs/ucff_core_front_door_contract.md`

## Scope

Allowed:
- Define comparator contract for 1D dispersion surfaces with typed inputs/outputs.
- Define deterministic normalization and failure-reason taxonomy.
- Define negative controls and acceptance criteria for a future implementation ticket.

Not allowed:
- No runtime logic changes in `formal/python/tools/**`.
- No schema changes to existing bridge-program orthogonality artifacts.
- No probe-set expansion in this ticket.

## Comparator class contract (design-only)

Target surface type:
- Typed deterministic front door with:
  - input: `k: List[float]` (+ pinned params/config)
  - output: `omega2: List[float]`

Canonical normalization rules:
1. `k` and `omega2` are same length and index-aligned.
2. `k` ordering must be deterministic; default strict mode requires nondecreasing `k`.
3. Comparison uses pinned shared `k` grid; if interpolation is allowed later, interpolation policy must be deterministic and pinned.
4. Units/tags are treated as pinned metadata and must not be inferred implicitly.

Comparator metrics (initial design set):
- Relative L2 mismatch on `omega2(k)`.
- Max relative error across shared `k` support.
- Structural checks:
  - positivity/non-negativity policy (where required),
  - monotonicity window checks (if declared by lane config).

## Failure reason codes (design taxonomy)

- `FAIL_DISPERSION_SHAPE_MISMATCH`
- `FAIL_DISPERSION_SIGN`
- `FAIL_DISPERSION_MONOTONICITY`
- `FAIL_K_GRID_ORDER`
- `FAIL_K_GRID_ALIGNMENT`
- `FAIL_DISPERSION_NONDETERMINISTIC`

## Negative controls (design-only)

Pinned future negatives to preserve non-vacuity:
1. `k` permutation control -> expect `FAIL_K_GRID_ORDER` or `FAIL_K_GRID_ALIGNMENT`.
2. Parameter sign-flip control (where physically admissibility-constrained) -> expect `FAIL_DISPERSION_SIGN`.
3. Shape perturbation control (scale/curvature perturbation) -> expect `FAIL_DISPERSION_SHAPE_MISMATCH`.

## Explicit C7/MT-01a deferral

C7/MT-01a remains blocked for phase/current/pair bridge mapping in this lane and is intentionally deferred.

Any C7 follow-up must run under a separate derived-observable design lane and must not be coupled to this UCFF-first comparator ticket.

## Deliverables

1. This design comparator contract (UCFF-first, non-grid).
2. Deterministic reason-code taxonomy and negative-control plan.
3. One next-ticket rule for implementation handoff.

## Deterministic next-ticket rule

After this design ticket is accepted, mint exactly one implementation ticket:

- `BRIDGE_TICKET_COMPARATOR_CLASS_IMPL_0001_dispersion_lane_ucff`

Implementation scope (future ticket only):
- Add deterministic comparator generator + artifact surface for UCFF dispersion lane.
- Add bounded tests for determinism, alignment, negative controls, and reason-code stability.

No other implementation tickets are opened from this design ticket.

## Acceptance criteria

- Contract is path-pinned to UCFF front-door evidence.
- Comparator definition does not require Form A/B grid semantics.
- C7 is explicitly deferred (no hidden cross-lane coupling).
- No runtime/tool code changes are made in this ticket.
