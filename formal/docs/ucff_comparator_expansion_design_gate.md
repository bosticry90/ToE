# UCFF Comparator Expansion Gate (Design-Only)

Purpose: define the minimum comparator design contract now, while implementation
remains blocked until foundational phases are closed.

Status: design-gate baseline retained; comparator-expansion block lifted for the COMP-03 UCFF lane on 2026-02-08 after COMP-01 + COMP-02 closure. Broader comparator expansion remains policy-gated.

## Block Rule

No new comparator implementation is admissible unless all are true:

- Phase 1 dynamics-match closure is evidenced in Lean (declared action -> EL -> declared dynamics).
- Phase 3 Noether linkage is evidenced against the same declared action/evolution surface.
- Phase 4 observability audits required by policy are pinned and green.

## Minimal Comparator Contract (once unblocked)

- Front-door API only; typed input object required.
- Input must be a fingerprinted empirical artifact (no raw array fallback).
- Output must be a deterministic metric vector with reason-code-ready fields.
- Candidate-family completeness check required before lock generation.

## Required Guardrails

- Candidate internals cannot be imported by downstream consumers.
- Comparator lock must include at least one family-elimination condition under
  explicitly stated regime assumptions.
- Any override lane must be declared and auditable, never implicit.

## First Implementation Target (post-unblock)

- UCFF low-k slope comparator lane with:
  - deterministic lock generation,
  - explicit comparability declarations,
  - pruning-table compatibility checks.

## Lift Record

- Lift event: 2026-02-08
- Authorized implementation scope: COMP-03 UCFF dispersion comparator lane only
- Preconditions satisfied: COMP-01 + COMP-02 exit criteria
