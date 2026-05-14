# Domain-Neutral Architecture Blueprint v0

Status: standalone reusable blueprint
Date: 2026-05-11
Origin: derived from the ToE repository architecture, stripped of subject-specific content
Authority boundary: this document is not a project claim surface, not a release gate, and not a domain result.

## Purpose

This blueprint describes a portable repository architecture for projects that need durable state, machine-checkable contracts, reproducible artifacts, and conservative promotion of results.

It is intended for use in separate repositories. The reusable object is the architecture pattern, not the original project's subject matter.

Use this blueprint when a project has any of these traits:

- long-running work with many intermediate decisions,
- high cost of overstating conclusions,
- multiple active work lanes or research branches,
- generated reports, benchmarks, simulations, proofs, or external evidence,
- a need to preserve blockers and uncertainty,
- a need for CI gates that enforce state, structure, and language contracts.

## Design Intent

The repository should act as a governed operating system for the project:

- Human-readable state explains what is currently true.
- Machine-readable schemas define what is allowed.
- Tests enforce the contract between state, code, docs, and artifacts.
- Generated outputs are evidence candidates, not authority by default.
- Promotion requires explicit gates.
- Historical material remains available but cannot silently re-enter the live surface.

The main architectural rule is simple: separate creation from promotion.

## Non-Claim Boundary

Adopting this architecture does not make a project correct, complete, validated, safe, publishable, or production-ready.

The architecture only provides a controlled path for:

- defining scope,
- recording status,
- producing evidence,
- testing evidence integrity,
- preserving blockers,
- deciding whether a result can be promoted.

No generated file, benchmark, report, proof object, model output, dataset summary, or dashboard should become authoritative merely because it exists in the repository.

## Repository Scaffold

Recommended full scaffold:

```text
project_name/
  README.md
  PROJECT_STATE.md
  ARCHITECTURE_SCHEMA_v1.json
  GOVERNANCE_VERSION_v1.lock
  requirements.lock
  pytest.ini
  scripts/
    run_tests.ps1
    run_governance.ps1
    run_orchestration.ps1
    validate_tooling.ps1
  docs/
    blueprints/
    charter/
      PROJECT_CHARTER_v0.md
      DOMAIN_SCOPE_v0.md
      NON_CLAIM_BOUNDARY_v0.md
    architecture/
      ARCHITECTURE_STACK_v0.md
      AUTHORITY_SURFACES_v0.md
      CONTRACT_REGISTRY_v0.md
      PROMOTION_RULES_v0.md
      ARTIFACT_LIFECYCLE_POLICY_v0.md
    lanes/
      LANE_REGISTRY_v0.md
      ACTIVE_LANE_STATUS_v0.md
    release/
      CURRENT_AUTHORITATIVE_SURFACES_v0.md
      GOVERNANCE_TEST_MANIFEST_v1.json
      ORCHESTRATION_MANIFEST_v0.json
      RELEASE_STATUS_v0.md
    templates/
      CONTRACT_TEMPLATE_v0.md
      DECISION_RECORD_TEMPLATE_v0.md
      ARTIFACT_REPORT_TEMPLATE_v0.json
      BLOCKER_RECORD_TEMPLATE_v0.md
  src/
    project_name/
      __init__.py
      meta/
      core/
      contracts/
      tools/
      orchestration/
  tests/
    conftest.py
    governance/
    contracts/
    artifacts/
    orchestration/
    integration/
  output/
    reports/
    snapshots/
    figures/
    logs/
  external/
    README.md
  quarantine/
    README.md
  archive/
    README.md
  scratch/
    README.md
```

Recommended minimal scaffold:

```text
project_name/
  README.md
  PROJECT_STATE.md
  ARCHITECTURE_SCHEMA_v1.json
  docs/
    architecture/
      AUTHORITY_SURFACES_v0.md
      CONTRACT_REGISTRY_v0.md
      PROMOTION_RULES_v0.md
    release/
      GOVERNANCE_TEST_MANIFEST_v1.json
  src/
    project_name/
  tests/
    governance/
  output/
    reports/
  quarantine/
```

Start small. Add formal proofs, orchestration, artifact retention, and multi-lane governance only after the project has enough complexity to justify them.

## Architectural Layers

### Layer 0: Control Plane

The control plane defines what the repository currently believes about itself.

Core files:

- `PROJECT_STATE.md`: current human-readable status.
- `ARCHITECTURE_SCHEMA_v1.json`: machine-readable architecture contract.
- `GOVERNANCE_VERSION_v1.lock`: pinned baseline for growth limits and contract versions.
- `docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md`: index of current authority sources.

Responsibilities:

- name the live target or active work lane,
- define allowed status tokens,
- define allowed claim or result classes,
- define required lifecycle phases,
- identify canonical source files,
- identify generated files that are not authoritative,
- preserve non-claim boundaries.

### Layer 1: Contract Surfaces

Contract surfaces define stable expectations for work products.

Examples:

- project charter,
- domain scope,
- non-claim boundary,
- architecture stack,
- lane registry,
- promotion rules,
- artifact lifecycle policy,
- external evidence registry,
- benchmark or evaluation contracts,
- schema files for JSON reports.

Contracts should be short, explicit, and testable. A contract that cannot be checked by a human or machine should be treated as guidance, not governance.

### Layer 2: Domain Kernel

The domain kernel contains the project's primary reusable concepts.

Depending on the project, this may include:

- source code models,
- data models,
- equations or proofs,
- simulation primitives,
- evaluation definitions,
- benchmark adapters,
- policy logic,
- formal methods modules.

The domain kernel should avoid importing from reports, notebooks, scratch space, archive, or quarantine. Direction of dependency should flow from stable definitions to generated evidence, not backward.

### Layer 3: Tooling And Generators

Tooling transforms controlled inputs into reports, ledgers, snapshots, comparisons, or derived artifacts.

Recommended rules:

- tools live under `src/project_name/tools/` or `scripts/`,
- tools emit structured outputs under `output/`,
- tools do not directly edit authority files unless explicitly designed and gated,
- report schemas are versioned,
- report generation is deterministic when possible,
- each generator has a corresponding contract test.

Use wrappers for common commands so local and CI behavior stay aligned.

### Layer 4: Verification Gates

Verification gates enforce the architecture.

Recommended gate families:

- schema shape gates,
- authority surface consistency gates,
- contract coverage gates,
- report schema gates,
- evidence pointer existence gates,
- generated artifact determinism gates,
- archive and quarantine boundary gates,
- dependency and environment gates,
- status-language or claim-language gates,
- orchestration manifest gates.

A gate should fail loudly when a new work product bypasses required phases, uses an unknown status token, points to a missing artifact, or promotes a result without authorization.

### Layer 5: Evidence And Artifact Plane

The artifact plane stores generated or imported evidence.

Recommended locations:

- `output/reports/`: structured generated reports.
- `output/snapshots/`: reproducibility snapshots.
- `output/figures/`: generated figures.
- `output/logs/`: command or run logs.
- `external/`: external data, references, or third-party material.
- `quarantine/`: material under review, legacy material, or blocked candidates.
- `archive/`: historical material explicitly outside the live authority surface.

Artifacts should carry enough metadata to be auditable:

- schema ID,
- generated timestamp,
- generator name and version,
- source inputs,
- command or test node,
- status,
- uncertainties,
- blockers,
- promotion state.

### Layer 6: CI And Release Plane

CI should encode the same rules humans use locally.

Recommended jobs:

- governance gates,
- dependency/security scan,
- full test suite,
- cross-platform parity gates,
- orchestration smoke,
- artifact schema smoke,
- optional formal build,
- optional integration or release readiness job.

The release plane should never be just "tests passed." It should also answer:

- What is authoritative now?
- What changed?
- Which artifacts were generated?
- Which blockers remain?
- Which claims are explicitly not authorized?
- Which historical surfaces are superseded?

## Authority Surface Pattern

Every project should identify its authority surfaces.

Recommended classes:

```text
CANONICAL_CONTROL_SOURCES
PUBLIC_SUMMARY_SURFACES
ACTIVE_TARGET_SURFACES
CONTRACT_SURFACES
GENERATED_OUTPUT_SURFACES
HISTORICAL_SUPERSEDED_SURFACES
QUARANTINED_SURFACES
```

Suggested rule:

- `PROJECT_STATE.md` summarizes status for humans.
- `docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md` indexes the current authority chain.
- `ARCHITECTURE_SCHEMA_v1.json` defines tokens, phases, and required structure.
- `output/` is never authoritative unless a promotion gate explicitly binds an artifact into an authority surface.

## Lifecycle Model

Use a small state machine for work products:

```text
DRAFT
REGISTERED
AUTHORIZED_FOR_EXECUTION
EXECUTED
REVIEWED
PROMOTED
RETAINED_WITH_BLOCKERS
SUPERSEDED
QUARANTINED
ARCHIVED
RETIRED
```

Default rule: new work starts as `DRAFT` or `REGISTERED`.

Promotion should require:

- a declared scope,
- a contract or schema,
- evidence pointers,
- a review result,
- remaining blocker inventory,
- an explicit non-claim check where applicable.

## Phase Coverage Pattern

For high-impact claims or deliverables, require phase coverage.

Generic phase sequence:

```text
TARGET_DEFINITION
ASSUMPTION_FREEZE
CANONICAL_ROUTE
ANTI_SHORTCUT
COUNTERFACTUAL
INDEPENDENT_NECESSITY
HARDENING
BOUNDED_SCOPE
DRIFT_GATES
ADJUDICATION_SYNC
```

Projects may rename phases, but should preserve the underlying obligations:

- define the target,
- freeze assumptions,
- describe the intended route,
- block shortcut promotion,
- test alternatives or failure cases,
- require independent necessity or justification,
- harden against regressions,
- bound scope,
- monitor drift,
- synchronize result status with allowed tokens.

## Token Discipline

Define a limited set of allowed status tokens.

Example result tokens:

```text
DRAFT_ONLY
DESIGN_READY
EXECUTION_READY
EXECUTED_UNREVIEWED
REVIEWED_NONPROMOTED
PROMOTED_WITH_SCOPE
BLOCKED
SUPERSEDED
RETIRED
```

Example evidence classes:

```text
STRUCTURAL
REGIME
APPROXIMATION
DERIVATION
EMPIRICAL
SIMULATION
BENCHMARK
REVIEW
```

Tests should reject new high-impact token classes unless the architecture schema is intentionally updated.

## Testing Architecture

Recommended test layout:

```text
tests/
  conftest.py
  governance/
    test_architecture_schema.py
    test_authority_surfaces.py
    test_status_language.py
    test_growth_policy.py
  contracts/
    test_contract_registry.py
    test_phase_coverage.py
    test_promotion_rules.py
  artifacts/
    test_report_schemas.py
    test_evidence_pointers.py
    test_artifact_determinism.py
  orchestration/
    test_orchestration_manifest.py
    test_runner_smoke.py
  integration/
```

`conftest.py` should enforce import boundaries:

- repo root must be importable,
- archive and quarantine should not appear in normal import paths,
- deprecated test families may be skipped only by explicit policy,
- tests should resolve paths from the repo root, not from the caller's shell location.

## Orchestration Pattern

Use a manifest-driven runner for grouped checks.

Example manifest:

```json
{
  "schema_id": "ORCHESTRATION_MANIFEST_v0",
  "runner_version": "v0",
  "checks": [
    {
      "check_id": "architecture_schema",
      "command": ["{python}", "-m", "pytest", "tests/governance/test_architecture_schema.py", "-q"],
      "timeout_seconds": 240
    },
    {
      "check_id": "authority_surfaces",
      "command": ["{python}", "-m", "pytest", "tests/governance/test_authority_surfaces.py", "-q"],
      "timeout_seconds": 240
    }
  ]
}
```

The runner should emit a structured report with:

- schema ID,
- generated timestamp,
- checks run,
- failures,
- stdout and stderr tails,
- uncertainties,
- manual review requirements.

## Artifact Lifecycle

High-growth artifact families need retention rules.

Each governed artifact family should define:

- family ID,
- path glob,
- retention threshold,
- archive destination,
- exemption rules,
- review cadence,
- gate that validates the policy.

Canonical release packets and baseline locks may be exempt from timed archive, but the exemption should be explicit.

## Quarantine And Archive Boundaries

Quarantine is for material that is not yet trusted, no longer trusted, or not yet routed.

Archive is for historical material that should remain readable but not active.

Required controls:

- live code must not import from archive,
- tests must not silently collect quarantined tests,
- authority surfaces must label historical material as historical,
- archived material should not satisfy current evidence pointers unless explicitly grandfathered,
- quarantine exits require review and a destination.

## CI Blueprint

Recommended CI job order:

```text
governance
dependency-security
tests
cross-platform-parity
orchestration-smoke
artifact-schema-smoke
optional-formal-build
optional-release-readiness
```

The governance job should run first because it validates the rules used by later jobs.

The dependency-security job should run before full tests when dependency integrity is part of the release posture.

Cross-platform parity is recommended when the project uses shell wrappers, path-sensitive tooling, compiled extensions, or generated artifacts.

## Command Wrappers

Provide stable wrappers for common commands.

Example:

```text
scripts/run_tests.ps1
scripts/run_governance.ps1
scripts/run_orchestration.ps1
```

Wrappers should:

- resolve repo root from their own location,
- use the project virtual environment or an explicit interpreter,
- apply timeouts for long-running validation,
- support dry-run mode where useful,
- pass through additional arguments,
- return accurate exit codes.

## Naming Conventions

Use names that encode lifecycle and version.

Recommended pattern:

```text
OBJECT_NAME_YYYYMMDD_v0.json
OBJECT_NAME_v0.md
OBJECT_REGISTRY_v1.json
GOVERNANCE_VERSION_v1.lock
```

Keep names stable enough for tests to reference them. Avoid using filenames as prose; use explicit fields inside the document or JSON payload for meaning.

## Schema Conventions

`ARCHITECTURE_SCHEMA_v1.json` should include:

```json
{
  "schema_id": "ARCHITECTURE_SCHEMA_v1",
  "schema_version": 1,
  "required_phases": [],
  "allowed_status_tokens": [],
  "allowed_evidence_classes": [],
  "authority_surface_inventory": {},
  "growth_policy": {},
  "phase_exempt_name_patterns": [],
  "status_exempt_name_patterns": []
}
```

Keep the schema compact. The schema should define architectural rules, not become a duplicate of every document in the repository.

## Growth Policy

Long-running governed repositories accumulate surfaces quickly.

Use growth limits for:

- authority documents,
- status token classes,
- claim classes,
- release packet families,
- generated artifact families,
- test manifest groups.

Growth policies should make expansion intentional without blocking ordinary implementation work.

## Implementation Sequence

1. Create the minimal scaffold.
2. Write `PROJECT_STATE.md`.
3. Write `ARCHITECTURE_SCHEMA_v1.json`.
4. Define authority surfaces.
5. Define promotion rules and non-claim boundary.
6. Add import-boundary and schema tests.
7. Add one generated report and its schema test.
8. Add command wrappers.
9. Add CI governance and test jobs.
10. Add artifact lifecycle policy once output growth begins.
11. Add orchestration only after multiple gates need coordinated execution.
12. Add archive and quarantine policy before importing legacy material.

## Migration Checklist

Use this checklist when moving the pattern into a new repository.

```text
[ ] Replace project_name placeholders.
[ ] Define live status in PROJECT_STATE.md.
[ ] Declare non-claim boundary.
[ ] Create ARCHITECTURE_SCHEMA_v1.json.
[ ] Create CURRENT_AUTHORITATIVE_SURFACES_v0.md.
[ ] Define allowed status tokens.
[ ] Define allowed evidence classes.
[ ] Define required phases for high-impact work.
[ ] Add governance tests for schema and authority surfaces.
[ ] Add evidence pointer tests.
[ ] Add artifact report schema tests.
[ ] Add command wrappers.
[ ] Add CI governance job.
[ ] Add quarantine and archive READMEs.
[ ] Add artifact lifecycle policy when outputs become numerous.
[ ] Review whether a full governance blueprint is needed.
```

## Relationship To Governance Blueprint

This architecture blueprint defines the repository structure and system boundaries.

The companion governance blueprint should define claim discipline, blocker handling, evidence admissibility, and promotion policy in more detail.

Use this document first when building the repository skeleton. Use the governance blueprint when deciding how work products become trusted.

## Anti-Patterns

Avoid these patterns:

- letting generated reports rewrite authority without review,
- treating passing tests as automatic promotion,
- importing from archive or quarantine in live modules,
- storing important status only in CI logs,
- using notebooks as the only source of truth,
- adding new status tokens without schema updates,
- preserving legacy material without a boundary label,
- hiding blockers in prose instead of naming them,
- mixing external project artifacts into the original repository,
- adding heavy orchestration before simple tests exist.

## Success Criteria

A project has adopted this architecture when:

- a new contributor can identify the current authority surfaces,
- status tokens are finite and tested,
- generated artifacts have schemas,
- evidence pointers are checked,
- blockers remain visible,
- archive and quarantine cannot silently influence live work,
- CI runs the same governance gates available locally,
- promotion is explicit and reversible,
- the project can say what is not yet authorized as clearly as what is.

