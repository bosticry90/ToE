# CRFT Validation Queue Protocol (Docs-Only)

Date: 2026-02-01

## Purpose

This note defines the protocol for converting legacy CRFT claim sources into bounded, executable validation work **without importing archive code** and **without upgrading epistemic status by fiat**.

The validation queue is an operational tracker: it records what was claimed, what canonical surface it maps to, and what tests constitute admissible evidence that the mapping is consistent with the current canonical implementation.

## Core artifacts

### Claims extraction (bookkeeping)

- Input: a legacy CRFT spec document (may be under the archive directory)
- Output: a deterministic claims list with stable claim IDs and a deterministic validation shortlist

Primary artifact:
- formal/quarantine/claims/CRFT_claims_extract_extended_crft_test_family_v1.json

### Validation queue (operational tickets)

- Input: a claims-extraction JSON that includes `validation_shortlist`
- Output: a bounded JSON “queue” of validation items with explicit evidence pointers

Primary artifact:
- formal/quarantine/validation/CRFT_validation_queue_extended_crft_test_family_v1.json

## Queue schema v3 (meaning)

`schema_version: 3` indicates each queue item contains deterministic evidence pointers and deterministic grouping metadata:

- `evidence.pytest_nodes`: a list of pytest node IDs as **static strings**, produced deterministically (not discovered at runtime)
- `evidence.canonical_surface_refs`: stable canonical identifiers (e.g., `CP-NLSE-2D`, `MT-01a`) that refer to the already-admissible “front doors”
- `claim_family`: a deterministic grouping key (e.g., `C6_CP_NLSE_2D`, `C7_MT_01A`)
- `evidence_strength`: a deterministic tag (e.g., `bounded_single`, `bounded_multi`) describing the intended evidence posture per ticket

This makes each item operational and auditable: a reviewer can run the referenced pytest nodes and verify that they exist.

## Evidence discipline

Passing the tests referenced by `evidence.pytest_nodes` means:

- The claim-to-surface mapping is **consistent** with the current canonical implementation and the chosen bounded validation criterion.

Passing does **not** mean:

- The claim is physically true in a broader sense.
- The surface is complete for all regimes.
- The legacy document is authoritative.

The queue is designed to produce **admissible, executable evidence** for specific mappings under explicit scope.

## Validation types (current practice)

A queue item should be validated using at least one bounded approach:

- Invariant: a structural or inequality constraint that should always hold under specified conditions.
- Regression lock: a pinned numerical output compared against a canonical lock artifact.
- Symbolic equivalence: a deterministic algebraic/simplification check (if a canonical symbolic surface exists).
- Numerical sanity: a small-scope check that is deterministic and diagnostic, not an exploration.

## Governance constraints

- Quarantine boundary: archive code is not importable; any archive interaction is read-only and limited to allowlisted tooling.
- Front-door-only: validations must attach to existing canonical surfaces; do not introduce new public modules as part of validation.
- Determinism: artifacts are stable (sorted keys, stable ordering), and evidence pointers are static strings.
- No status upgrades: queue artifacts and passing tests are evidence; any inventory/status changes must follow the repo’s epistemic governance rules.

## Operational workflow

1. Extract claims from a selected legacy CRFT spec into a deterministic claims JSON.
2. Generate a bounded validation queue (max N items per batch).
3. Implement minimal bounded tests against existing canonical surfaces.
4. Ensure evidence-pointer integrity: referenced pytest nodes exist and remain stable.
5. Run pytest; record that the operational checks are green.

## Scope notes

This protocol is intentionally narrow. It is optimized for:

- auditability
- determinism
- minimal coupling
- explicit scope

It is not optimized for narrative exposition.
