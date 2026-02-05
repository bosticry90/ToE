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

## Pinned results table (to fill with artifacts)

| candidate_surface | found | blocked_reason | evidence_artifact_path | artifact_sha256 | status |
| --- | --- | --- | --- | --- | --- |
| C6 (anchor/control) | true | none | formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json | pinned-existing | complete |
| C7 / MT-01a | pending | pending | pending | pending | design-scan-open |
| UCFF candidate set | pending | pending | pending | pending | design-scan-open |

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
