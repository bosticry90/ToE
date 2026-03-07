# TOE Architecture Stack v0

Status: ACTIVE_v0
Owner: ToE governance
Last updated: 2026-03-06

## Purpose

Define the executable software architecture roles for ToE tooling.
This document is a build contract, not a physics claim.

## Layering Contract

- Layer 1: Source surfaces (canonical markdown/json and pinned artifacts)
- Layer 2: Data-quality checks (shape, duplication, pointer, and hash hygiene)
- Layer 3: Trust core (strict validators; Rust-target lane)
- Layer 4: Async orchestration (Python asyncio coordination of checks)
- Layer 5: Local analysis lane (bounded model-assisted analysis)
- Layer 6: Human adjudication (final authority over semantic promotion)

## Immediate Build Boundaries (v0)

- Python async orchestration is allowed for I/O and subprocess coordination only.
- Orchestration output must be explicit JSON and must include manual-review fields.
- Trust-core is promoted to blocking CI status for tranche-3 scoped checks.
- No tool may auto-promote canonical status/adjudication tokens.

## Required Report Fields

Every orchestration run must emit a report with these top-level fields:

- `checks_run`
- `failures`
- `uncertainties`
- `speculative_flags`
- `manual_review_required`

Schema source:
- `formal/docs/release/TOE_ADJUDICATION_REPORT_SCHEMA_v0.json`

## Non-Autopilot Rule

- Machine-generated output is advisory.
- Human review is required for any governance-affecting update.
- A successful run means structural checks passed, not semantic truth.
