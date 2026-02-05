# BRIDGE_TICKET_CANONICAL_SURFACE_DIVERSIFY_0002 -- Alternative grid-shaped canonical target discovery [DESIGN-ONLY]

Status: Design-only (no implementation)

Opened: 2026-02-05

## Purpose (bounded)

Identify one non-C6 canonical family that is already grid-shaped (non-archive, deterministic, typed front door) and therefore a valid next diversification target after C7/MT-01a and UCFF failed D2 adapter discovery.

No runtime bridge logic changes are permitted in this ticket.

## Triggering evidence (pinned)

- `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_BLOCKER_0001_spatial_grid_surface_mapping.md`
  - D2 outcomes: C7/MT-01a `adapter_possible=false`, UCFF `adapter_possible=false`
  - blocker reason: `NO_GRID_SURFACE_EXISTS` (scanner-native `BLOCKED_NO_SPATIAL_GRID_SURFACE`)
- `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json`
  - `sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`

## Selection criteria for alternative target

Candidate must satisfy all:
1. Non-archive canonical surface with typed input/output front door.
2. Deterministic behavior for identical pinned inputs.
3. Grid-shaped output or operator surface mappable to:
   - Form A (`phi: ndarray[complex]`) or
   - Form B (`rhs(phi): ndarray[complex]` or equivalent operator surface).
4. Supports existing bridge probe semantics without schema changes, or fails with explicit deterministic blocker.

## Design-only procedure

1. Enumerate candidate canonical families currently present in non-archive Python surfaces.
2. Run or draft deterministic feasibility checks per candidate (documentation/scanner artifacts only).
3. Produce a pinned comparison table (`found=true/false`, blocker reason, artifact path, sha256).
4. Recommend exactly one next implementation ticket if any candidate is feasible.

## Deliverables

1. Pinned candidate inventory for non-C6 canonical families.
2. Deterministic feasibility artifact(s) for each candidate scanned.
3. One recommendation:
   - implementation ticket for a feasible target, or
   - further design blocker ticket if none are feasible.

## Acceptance criteria

- Evidence is deterministic and path-pinned.
- No runtime bridge/tool code changes.
- Recommendation is single-target and implementation-scoped (if feasible).
