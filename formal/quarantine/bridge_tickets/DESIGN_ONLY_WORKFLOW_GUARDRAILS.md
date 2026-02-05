# DESIGN_ONLY_WORKFLOW_GUARDRAILS

Status: Canonical policy for design-only branches (no implementation)

## Definition

This branch is design-only:
- Allowed: documentation, planning, feasibility scans, inventory updates, tickets, reproduction capsules, manifest drafts.
- Not allowed: runtime logic changes, algorithm changes, tolerance changes, schema changes, adding new probes, modifying existing evaluation code.

## Allowed file patterns

- `State_of_the_Theory.md` (documentation-only evidence blocks)
- `formal/quarantine/bridge_tickets/**` (tickets, capsules, plans, classifiers)
- New design-only tools are allowed ONLY if they:
  - produce documentation artifacts,
  - do not affect runtime evaluation paths,
  - are gated to design-only outputs (no replacement of canonical artifacts).

## Prohibited changes

Any diffs under:
- `formal/python/tools/**` (except purely additive design-only report generators that do not affect existing pipelines)
- `formal/python/tests/**` (except tests for design-only generators)
- Anything that changes existing bridge computations, comparisons, tolerances, or admissibility semantics.

## Verification requirements

Before any merge from this branch:
- `git diff --name-only main...HEAD` must show only allowed file patterns.
- If any prohibited file is changed, the branch must be reclassified as implementation and moved to an `impl/` branch namespace.

## Merge discipline

- Merge only via squash (single commit) or a short linear series.
- Commit messages must start with `design:` or `docs:`.

## Scope

Canonical-surface diversification feasibility scan:
- identify candidate surface families (e.g., C7 / MT-01a / UCFF surface candidates)
- determine “bridge feasibility” (found=true/false) via existing scanners or documentation-only scans
- produce a design ticket for the first diversification target
