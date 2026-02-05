# BRIDGE_TICKET_CANONICAL_SURFACE_SCAN_0001

Status: Design-only (no implementation)

Opened: 2026-02-05

## Purpose (bounded)

Plan a canonical-surface diversification feasibility scan that extends bridge comparison beyond C6 while preserving pinned probes, deterministic reporting, and current admissibility semantics.

This ticket does not permit runtime bridge implementation changes.

## Branch guardrails

This ticket is governed by:
- `formal/quarantine/bridge_tickets/DESIGN_ONLY_WORKFLOW_GUARDRAILS.md`

## Candidate surfaces (evaluation order)

1. C7 / MT-01a (primary target)
2. UCFF surface candidates (secondary target; only if deterministic and typed inputs are available)

## Feasibility criteria (must all hold for `found=true`)

1. Deterministic generation for identical pinned inputs.
2. Admits pinned probe IDs used by bridge-program orthogonality surfaces (current frontier size: 17 probes).
3. Produces observables comparable to existing channel outputs (phase/current/pair compatibility mapping remains defined).
4. Generates auditable artifacts with evidence pointers.
5. Does not require schema changes or tolerance-profile rewrites.

If any criterion fails, mark `found=false` and pin a deterministic block reason.

## Scan procedure (design-only)

1. Reuse existing feasibility scanners where available.
2. If a scanner does not exist for a candidate surface, produce a design-only feasibility specification (no runtime evaluator edits).
3. Record each result in the pinned results table below.
4. Recommend one next implementation ticket only when at least one non-C6 candidate is `found=true`.

## Scan execution evidence (2026-02-05)

- Scanner used: `.\py.ps1 -m formal.python.tools.bridge_toyg_canonical_feasibility_scan`
- Output artifact:
  - `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json`
- Determinism check:
  - scanner rerun wrote identical bytes (`sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`)

## Pinned results table

| candidate_surface | found | blocked_reason | evidence_artifact_path | artifact_sha256 | status |
| --- | --- | --- | --- | --- | --- |
| C6 (anchor/control) | true | none | formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json | 36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0 | complete |
| C7 / MT-01a | false | NO_OBSERVABLE_MAPPING_PHASE_CURRENT_PAIR | formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json | 36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0 | blocked |
| UCFF candidate set | false | NO_OBSERVABLE_MAPPING_PHASE_CURRENT_PAIR | formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json | 36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0 | blocked |

Scanner-native reason-code mapping (same artifact):
- C7 / MT-01a -> `reason_code=BLOCKED_NO_SPATIAL_GRID_SURFACE`, `found=false`
- UCFF -> `reason_code=BLOCKED_NO_SPATIAL_GRID_SURFACE`, `found=false`

## Deliverables

1. Design-only feasibility artifacts or specifications per candidate surface.
2. Updated pinned results table (found/blocked + reason).
3. Recommendation:
   - If `found=true` for a non-C6 candidate: mint one implementation ticket scoped to that surface only.
   - If all `found=false`: mint one design ticket for the dominant block reason.

## Acceptance criteria

1. Candidate list evaluated in order (C7/MT-01a, then UCFF).
2. Each candidate has deterministic `found` state and pinned reason.
3. No runtime bridge computation files are changed.
4. Next-ticket recommendation is explicit and evidence-bound.

## Recommendation (post-scan)

No non-C6 candidate is feasible yet (`found=true` only for C6). Do not mint an implementation ticket.

Next design-only target:
- Draft a follow-on ticket for dominant block reason `NO_OBSERVABLE_MAPPING_PHASE_CURRENT_PAIR`, scoped to mapping requirements for C7/UCFF without runtime bridge changes.
