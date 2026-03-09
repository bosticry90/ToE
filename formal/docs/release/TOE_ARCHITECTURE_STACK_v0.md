# TOE Architecture Stack v0

Status: ACTIVE_v0
Owner: ToE governance
Last updated: 2026-03-08

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

## Governance Posture Milestone (2026-03-08)

Governance execution posture now requires runtime-local evidence, not only static surface checks.
The pinned local path (`governance_suite.ps1`) now verifies stack execution for:

- preflight (`formal.python.tools.dev_stack_preflight`)
- orchestration manifest execution (`formal.python.orchestration.runner`)
- SQL integrity snapshot execution (`formal.python.tools.sql_integrity_snapshot`)
- Rust trust-core local run (`cargo run --manifest-path formal/rust/toe_trust_core/Cargo.toml`) when cargo is available

Regression guard pointer:
- `formal/python/tests/test_local_execution_posture_gate.py`

## Local Execution Posture Tiers

Canonical tier names for local governance operation:

- `STATIC_GOVERNANCE_v0`:
	- file/pointer/schema/test-surface governance checks only
	- no required local orchestration or SQL snapshot run
- `RUNTIME_GOVERNANCE_v0`:
	- includes static governance plus required local preflight, orchestration run, and SQL integrity snapshot run
- `STRICT_RUNTIME_GOVERNANCE_v0`:
	- includes runtime governance plus required local Rust trust-core execution
	- strict requirement toggle: `TOE_REQUIRE_RUST_LOCAL=1`

## Failure Taxonomy (Local Governance)

Expected failure classes and canonical meaning:

- `PRECHECK_DEV_STACK_FAILED_v0`:
	- `formal.python.tools.dev_stack_preflight` failed
	- indicates local execution environment is not ready
- `ORCHESTRATION_RUNTIME_FAILED_v0`:
	- orchestration manifest runner failed
	- indicates runnable orchestration drift or execution regression
- `SQL_INTEGRITY_RUNTIME_FAILED_v0`:
	- SQL integrity snapshot failed or reported issues
	- indicates integrity contract failure in generated runtime state
- `STRICT_RUST_MISSING_CARGO_v0`:
	- `TOE_REQUIRE_RUST_LOCAL=1` and cargo missing
	- indicates strict runtime posture cannot be satisfied on this machine
- `RUST_TRUST_CORE_RUNTIME_FAILED_v0`:
	- cargo present but trust-core runtime failed
	- indicates trust-core execution regression

## Overhead Guardrail

Runtime governance hardening remains valid only while trust gain exceeds local friction.
When adding new runtime checks, preserve these constraints:

- keep runtime checks directly coupled to trust-critical failure modes
- avoid redundant checks that duplicate existing static gates
- require explicit governance rationale for any added local runtime cost

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
