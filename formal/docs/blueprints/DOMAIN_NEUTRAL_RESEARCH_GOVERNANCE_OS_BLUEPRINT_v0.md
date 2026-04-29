# Domain-Neutral Research Governance Operating System Blueprint v0

Status: standalone reusable blueprint
Date: 2026-04-29
Origin: derived from the ToE research operating architecture, stripped of ToE-specific physics content
Authority boundary: this document is not a ToE claim surface, not a ToE lane artifact, and not a ToE release gate.

## Purpose

This blueprint defines a domain-neutral research governance operating system for projects that need disciplined computational testing, simulation, evidence tracking, and claim control.

It is meant to help create separate project repositories without mixing those projects into the ToE repository. The reusable object is the operating architecture, not the ToE theory content.

Use this blueprint when a project has all or most of these traits:

- Ambitious claims that can easily be overstated.
- Simulation, computation, or statistical tests that need careful interpretation.
- Multiple evidence streams with different reliability levels.
- Open blockers that must be preserved rather than narrated away.
- A need for reproducible status, auditability, and controlled claim promotion.
- Human review requirements before a result becomes authoritative.

## Non-Claim Boundary

This blueprint does not assert that any project using it is correct, complete, validated, or policy-ready.

It only defines a way to:

- separate hypotheses from claims,
- separate simulation outputs from validated conclusions,
- record blockers instead of hiding them,
- preserve lineage from evidence to conclusion,
- make project state machine-readable,
- keep promotion rules explicit.

No result becomes authoritative because it appears in a report, chart, notebook, model run, simulation trace, benchmark comparison, or summary document. Results become authoritative only when the project's promotion rules say they do.

## Recommended Workspace Layout

Keep non-ToE projects outside the ToE repository.

Recommended sibling layout:

```text
Documents/
  ToE/
    formal/docs/blueprints/DOMAIN_NEUTRAL_RESEARCH_GOVERNANCE_OS_BLUEPRINT_v0.md
  ResearchGovernanceProjects/
    climate_resilience_governance/
    ai_safety_eval_governance/
    pandemic_response_simulation_governance/
    energy_grid_resilience_governance/
```

If a project begins inside ToE for drafting convenience, move it out before it accumulates claims, tests, reports, or data. Do not import external project artifacts into ToE authority, release, lane, or paper surfaces unless there is a deliberate ToE-specific reason.

## Repository Scaffold

Each governed research project should start with this folder structure:

```text
project_name/
  README.md
  PROJECT_STATE.md
  GOVERNANCE_VERSION.lock
  docs/
    charter/
      PROJECT_CHARTER_v0.md
      DOMAIN_SCOPE_v0.md
      NON_CLAIM_BOUNDARY_v0.md
    architecture/
      ARCHITECTURE_STACK_v0.md
      CLAIM_LIFECYCLE_v0.md
      PROMOTION_RULES_v0.md
      BLOCKER_TAXONOMY_v0.md
    lanes/
      LANE_REGISTRY_v0.md
    benchmarks/
      EXTERNAL_BENCHMARK_REGISTRY_v0.md
    release/
      GOVERNANCE_TEST_MANIFEST_v0.json
      RELEASE_STATUS_v0.md
    templates/
      CLAIM_RECORD_TEMPLATE_v0.md
      BLOCKER_RECORD_TEMPLATE_v0.md
      SIMULATION_RUN_TEMPLATE_v0.md
      BENCHMARK_RECORD_TEMPLATE_v0.md
      DECISION_RECORD_TEMPLATE_v0.md
  data/
    raw/
    processed/
    external/
    README.md
  models/
    README.md
  simulations/
    README.md
  output/
    reports/
    figures/
    traces/
    snapshots/
  src/
    project_name/
  tests/
    governance/
    simulations/
    claims/
    benchmarks/
  scripts/
    run_governance.ps1
    run_simulations.ps1
    recompute_reports.ps1
  notebooks/
    sandbox/
  scratch/
    README.md
```

The scaffold has one controlling idea: research can be creative, but promotion must be conservative.

## Minimal Adoption

For a small project, the minimum viable governance system is:

```text
project_name/
  README.md
  PROJECT_STATE.md
  docs/
    charter/
      PROJECT_CHARTER_v0.md
      NON_CLAIM_BOUNDARY_v0.md
    architecture/
      CLAIM_LIFECYCLE_v0.md
      PROMOTION_RULES_v0.md
      BLOCKER_TAXONOMY_v0.md
    benchmarks/
      EXTERNAL_BENCHMARK_REGISTRY_v0.md
  output/
    reports/
  tests/
    governance/
```

Do not start with heavy automation unless the project needs it. Start with clean claim discipline, then add tests.

## Core Objects

### Claim

A claim is any statement the project may want to rely on.

Every claim should have:

- stable ID,
- plain-language statement,
- domain,
- scope,
- claim level,
- evidence links,
- blockers,
- promotion state,
- owner or reviewer,
- last updated date.

Recommended claim levels:

```text
HYPOTHESIS
DESIGN_INTENT
SIMULATION_OBSERVATION
STATISTICAL_RESULT
BENCHMARK_SUPPORTED
REPRODUCED_RESULT
GOVERNED_CLAIM
RETIRED_OR_REFUTED
```

Default rule: new claims begin as `HYPOTHESIS` or `DESIGN_INTENT`.

### Evidence

Evidence is any artifact that supports, weakens, or contextualizes a claim.

Evidence can include:

- dataset snapshot,
- model definition,
- simulation output,
- statistical test,
- proof or formal argument,
- external benchmark,
- expert review,
- failure case,
- replication run.

Evidence does not promote itself. Evidence only becomes promotion-relevant when a gate says it is admissible.

### Blocker

A blocker is a named reason a claim cannot be promoted.

Common blocker classes:

```text
DATA_BLOCKER
MODEL_BLOCKER
SIMULATION_BLOCKER
STATISTICAL_BLOCKER
CAUSAL_BLOCKER
BENCHMARK_BLOCKER
REPRODUCIBILITY_BLOCKER
SECURITY_BLOCKER
INTERPRETATION_BLOCKER
GOVERNANCE_BLOCKER
ETHICS_OR_SAFETY_BLOCKER
EXTERNAL_VALIDATION_BLOCKER
```

Default rule: unresolved blockers must be carried forward into status documents and reports. They should not disappear because a later result is encouraging.

### Gate

A gate is a machine-checkable or review-checkable rule that controls promotion.

Examples:

- Required files exist.
- Every promoted claim has evidence.
- Every simulation result has a seed, config, and environment record.
- Every benchmark claim points to an external benchmark record.
- Every governed claim has no unresolved hard blockers.
- Every policy-relevant claim has sensitivity analysis.
- Every release has a current project state document.

### Registry

A registry is a structured list of governed objects.

Recommended registries:

```text
claims_registry.json
blocker_registry.json
evidence_registry.json
simulation_registry.json
external_benchmark_registry.json
decision_registry.json
promotion_registry.json
```

Registries can start as Markdown tables. Move to JSON when tests need to enforce invariants.

### Authority Surface

An authority surface is a document or structured file that defines current project truth.

Recommended authority surfaces:

- `README.md`
- `PROJECT_STATE.md`
- `docs/charter/PROJECT_CHARTER_v0.md`
- `docs/charter/NON_CLAIM_BOUNDARY_v0.md`
- `docs/architecture/PROMOTION_RULES_v0.md`
- `docs/release/GOVERNANCE_TEST_MANIFEST_v0.json`

Notebooks, scratch files, ad hoc charts, exploratory simulations, and raw reports are not authority surfaces by default.

### Lineage

Lineage records how a conclusion changed.

Every promoted claim should answer:

- What evidence supports it?
- What evidence weakens it?
- What assumptions does it require?
- What blockers remain?
- What tests were run?
- What changed since the prior state?
- What would downgrade or refute it?

## Architecture Stack

### Layer 0: Charter

Defines what the project is and is not allowed to claim.

Core files:

- `docs/charter/PROJECT_CHARTER_v0.md`
- `docs/charter/DOMAIN_SCOPE_v0.md`
- `docs/charter/NON_CLAIM_BOUNDARY_v0.md`

Questions:

- What problem is being studied?
- What outputs are allowed?
- What outputs are explicitly not allowed?
- Who is the audience?
- What would count as misuse?

### Layer 1: Claim Governance

Defines claim levels, blockers, and promotion rules.

Core files:

- `docs/architecture/CLAIM_LIFECYCLE_v0.md`
- `docs/architecture/PROMOTION_RULES_v0.md`
- `docs/architecture/BLOCKER_TAXONOMY_v0.md`

Questions:

- What is the difference between an observation and a claim?
- What evidence is admissible?
- What blocks promotion?
- Who can adjudicate ambiguous cases?

### Layer 2: Domain Model

Defines the model of the world used by the project.

Core locations:

- `models/`
- `src/project_name/`
- `docs/architecture/ARCHITECTURE_STACK_v0.md`

Questions:

- What variables are included?
- What variables are excluded?
- What causal assumptions are being made?
- What approximations are allowed?
- What regimes are outside scope?

### Layer 3: Data and Evidence

Defines data sources, evidence standards, and external references.

Core locations:

- `data/raw/`
- `data/processed/`
- `data/external/`
- `docs/benchmarks/EXTERNAL_BENCHMARK_REGISTRY_v0.md`

Questions:

- Where did the data come from?
- Can the data be redistributed?
- What preprocessing happened?
- What uncertainty or bias is known?
- Which external references are trusted and why?

### Layer 4: Computation and Simulation

Defines computational experiments, simulation runs, and reproducibility requirements.

Core locations:

- `simulations/`
- `output/reports/`
- `output/traces/`
- `tests/simulations/`

Questions:

- What config produced the run?
- What seed was used?
- What environment was used?
- What sensitivity checks were run?
- Which outputs are stable under rerun?
- Which outputs are exploratory only?

### Layer 5: Test and Gate System

Defines automated checks.

Core locations:

- `tests/governance/`
- `tests/claims/`
- `tests/benchmarks/`
- `docs/release/GOVERNANCE_TEST_MANIFEST_v0.json`

Questions:

- Which checks are release-blocking?
- Which checks are advisory?
- Which checks are focused local validation only?
- What does failure mean?

### Layer 6: Human Adjudication

Defines review authority.

Core files:

- `docs/release/RELEASE_STATUS_v0.md`
- `docs/templates/DECISION_RECORD_TEMPLATE_v0.md`

Questions:

- Who can promote a claim?
- Who can waive a blocker?
- What requires explicit review?
- What cannot be automated?

## Claim Lifecycle

Recommended promotion path:

```text
HYPOTHESIS
  -> DESIGN_INTENT
  -> SIMULATION_OBSERVATION
  -> STATISTICAL_RESULT
  -> BENCHMARK_SUPPORTED
  -> REPRODUCED_RESULT
  -> GOVERNED_CLAIM
```

Allowed backward transitions:

```text
GOVERNED_CLAIM -> BENCHMARK_SUPPORTED
GOVERNED_CLAIM -> REPRODUCED_RESULT
GOVERNED_CLAIM -> RETIRED_OR_REFUTED
ANY_LEVEL -> BLOCKED
ANY_LEVEL -> RETIRED_OR_REFUTED
```

Promotion should be harder than demotion.

## Promotion Rules

Baseline rules:

1. No claim promotes by narrative summary alone.
2. No simulation output promotes directly to governed claim.
3. No benchmark comparison promotes unless benchmark admissibility is recorded.
4. No policy recommendation promotes without sensitivity and failure-mode review.
5. No high-impact claim promotes with unresolved hard blockers.
6. No result is considered reproduced unless the reproduction run is independent enough to matter.
7. No authority surface updates without changing the project state date.
8. No release unless governance tests pass or failures are explicitly classified.

Hard blockers should require explicit human adjudication to waive.

## Computational Testing Model

Tests should enforce structure before they enforce truth.

Good early tests:

- Required files exist.
- Project state references current registries.
- Claims have stable IDs.
- Promoted claims have evidence.
- Evidence paths exist.
- Blocker IDs are valid.
- No governed claim has unresolved hard blockers.
- Simulation reports include config, seed, and timestamp.
- Benchmark claims reference benchmark records.
- Release manifest contains all release-blocking tests.

Good later tests:

- Rerun stability checks.
- Sensitivity analysis thresholds.
- Model comparison checks.
- Drift detection.
- Backtest performance.
- Out-of-distribution stress tests.
- Cross-dataset validation.
- Adversarial or worst-case scenario tests.

## Simulation Governance

A simulation result should record:

- purpose,
- model version,
- input data version,
- config,
- random seed,
- environment,
- output path,
- summary metric,
- uncertainty estimate,
- known limitations,
- linked claims,
- promotion status.

Recommended statuses:

```text
SANDBOX_RUN
REPRODUCIBLE_RUN
SENSITIVITY_CHECKED_RUN
BENCHMARKED_RUN
GOVERNANCE_ADMISSIBLE_RUN
RETIRED_RUN
```

Default rule: a simulation is a stress surface, not a truth machine.

## External Benchmark Registry

Every project should define external pressure sources.

Benchmark record fields:

```text
benchmark_id:
name:
source:
domain:
why_relevant:
what_it_can_test:
what_it_cannot_test:
data_rights:
update_frequency:
known_biases:
linked_claims:
admissibility_status:
last_reviewed:
```

Recommended admissibility statuses:

```text
CONTEXT_ONLY
ADMISSIBLE_FOR_SANITY_CHECK
ADMISSIBLE_FOR_BACKTEST
ADMISSIBLE_FOR_BENCHMARK_SUPPORT
NOT_ADMISSIBLE
RETIRED
```

Default rule: external benchmarks create pressure; they do not automatically validate the project.

## Governance Test Manifest

The governance manifest should distinguish release-blocking tests from focused validation tests.

Example:

```json
{
  "manifest_id": "GOVERNANCE_TEST_MANIFEST_v0",
  "release_blocking": [
    {
      "id": "required_authority_surfaces",
      "command": "python -m pytest tests/governance/test_required_authority_surfaces.py",
      "purpose": "Ensure core project authority files exist."
    }
  ],
  "focused_validation": [
    {
      "id": "simulation_report_schema",
      "command": "python -m pytest tests/simulations/test_simulation_report_schema.py",
      "purpose": "Validate current simulation report structure."
    }
  ],
  "non_claim_boundary": "Passing tests does not by itself promote any domain claim."
}
```

## Template: Project Charter

```text
# Project Charter v0

Project:
Domain:
Primary question:
Intended users:
Forbidden uses:
Current status:

## Allowed Outputs

- Exploratory analysis:
- Simulation reports:
- Benchmark comparisons:
- Governed claims:
- Policy or operational recommendations:

## Non-Claim Boundary

This project does not claim:

- ...

## Success Criteria

- ...

## Hard Stop Conditions

- ...
```

## Template: Claim Record

```text
# Claim Record

claim_id:
statement:
domain:
scope:
claim_level:
authority_status:
linked_evidence:
linked_simulations:
linked_benchmarks:
linked_blockers:
assumptions:
known_limits:
promotion_requirements:
demotion_triggers:
owner:
last_updated:
```

## Template: Blocker Record

```text
# Blocker Record

blocker_id:
class:
severity:
blocks_claims:
description:
resolution_requirement:
acceptable_evidence:
current_status:
owner:
opened_date:
last_reviewed:
```

Recommended severities:

```text
INFO
SOFT_BLOCKER
HARD_BLOCKER
RELEASE_BLOCKER
SAFETY_BLOCKER
```

## Template: Simulation Run Record

```text
# Simulation Run Record

run_id:
purpose:
model_version:
code_ref:
data_ref:
config_ref:
seed:
environment:
output_ref:
summary:
uncertainty:
known_limits:
linked_claims:
linked_blockers:
status:
created_at:
```

## Template: Decision Record

```text
# Decision Record

decision_id:
date:
decision:
context:
options_considered:
evidence_reviewed:
blockers_reviewed:
promotion_or_demotion_effect:
non_claim_boundary:
reviewer:
follow_up:
```

## Global Problem Project Patterns

### Climate Resilience

Possible questions:

- Which adaptation investments remain robust across climate scenarios?
- Which regions are most exposed to compound hazards?
- Which policies reduce displacement under uncertainty?

Likely blockers:

- uncertain climate projections,
- incomplete local infrastructure data,
- socioeconomic confounding,
- poor transfer from model region to target region.

Useful tests:

- scenario sweep,
- sensitivity analysis,
- historical backtest,
- external disaster benchmark comparison.

### Pandemic Preparedness

Possible questions:

- Which intervention portfolios are robust before full information is available?
- Which surveillance signals give useful early warning?
- Which supply-chain policies reduce medical shortage risk?

Likely blockers:

- reporting lag,
- behavioral adaptation,
- privacy limits,
- uncertain pathogen parameters,
- intervention compliance uncertainty.

Useful tests:

- agent-based simulation,
- retrospective outbreak replay,
- uncertainty sweep,
- policy stress test.

### AI Safety and Evaluation

Possible questions:

- Which evaluation failures predict deployment risk?
- Which mitigations remain effective under distribution shift?
- Which systems need stricter release controls?

Likely blockers:

- benchmark saturation,
- weak external validity,
- hidden capability elicitation gaps,
- unclear harm model,
- poor adversarial coverage.

Useful tests:

- adversarial evals,
- red-team trace registry,
- benchmark drift checks,
- capability-risk claim gates.

### Energy Grid Resilience

Possible questions:

- Which grid designs survive demand spikes and extreme weather?
- Which storage strategies reduce cascading failure risk?
- Which regions are most vulnerable to correlated outage conditions?

Likely blockers:

- proprietary grid data,
- uncertain demand growth,
- correlated weather risk,
- model simplification of cascading dynamics.

Useful tests:

- outage simulation,
- load-flow stress tests,
- extreme weather scenario sweep,
- historical event replay.

### Food and Water Security

Possible questions:

- Which supply chains are most fragile under drought or conflict?
- Which water allocation policies remain stable under climate stress?
- Which interventions reduce famine risk fastest?

Likely blockers:

- incomplete local data,
- political instability,
- market feedback loops,
- nonlinear crop response,
- intervention access constraints.

Useful tests:

- multi-scenario simulation,
- supply-chain graph stress,
- drought backtest,
- intervention sensitivity analysis.

## Project Creation Checklist

Use this checklist when starting a new repository.

```text
[ ] Create sibling repo outside ToE.
[ ] Copy this blueprint into docs/architecture/ or docs/blueprints/.
[ ] Write PROJECT_CHARTER_v0.md.
[ ] Write NON_CLAIM_BOUNDARY_v0.md.
[ ] Write CLAIM_LIFECYCLE_v0.md.
[ ] Write PROMOTION_RULES_v0.md.
[ ] Write BLOCKER_TAXONOMY_v0.md.
[ ] Create PROJECT_STATE.md.
[ ] Create EXTERNAL_BENCHMARK_REGISTRY_v0.md.
[ ] Create minimal governance tests.
[ ] Create output/reports/ for generated reports.
[ ] Keep scratch and notebooks non-authoritative by default.
[ ] Define release-blocking versus focused-validation tests.
[ ] Run governance before promoting any claim.
```

## ToE Repository Protection Rules

To preserve ToE integrity:

1. Do not build non-ToE projects inside `formal/docs/lanes/`.
2. Do not add non-ToE project tests to the ToE governance manifest.
3. Do not import non-ToE project code into `formal/toe_formal/`.
4. Do not update `State_of_the_Theory.md` for external project progress.
5. Do not cite external project results as ToE support unless a separate ToE admissibility review exists.
6. Do not let a reusable governance pattern become a ToE physics claim.
7. Keep generated data, simulations, and notebooks for other projects in sibling repositories.

Allowed inside ToE:

- this blueprint,
- brief references to the methodology,
- explicit ToE-specific governance improvements,
- separately reviewed ToE-relevant artifacts.

Not allowed inside ToE by default:

- external project state files,
- external project simulation outputs,
- external project claim registries,
- external project benchmark reports,
- external project release manifests.

## First Pilot Recommendation

The first pilot should be narrow enough to finish but serious enough to test the architecture.

Recommended pilot:

```text
Project: Climate Resilience Governance Pilot
Question: Which adaptation strategy remains most robust across a fixed set of flood-risk scenarios?
Initial claims: 3 to 5
Initial blockers: 5 to 10
Initial simulations: 1 reproducible scenario sweep
Initial benchmarks: 2 external data sources
Initial gates: required files, claim IDs, evidence links, blocker carry-forward, simulation metadata
```

A good first pilot should prove that the operating architecture can prevent overclaiming while still producing useful computational insight.

## Success Criteria For The Operating System

The operating system is working if:

- project state is always knowable,
- claims do not outrun evidence,
- blockers remain visible,
- simulations are reproducible enough to audit,
- benchmark comparisons state what they can and cannot show,
- promotion is explicit,
- demotion is allowed,
- release status is testable,
- human judgment is recorded where automation is insufficient.

The operating system is failing if:

- status lives only in conversation,
- reports silently become claims,
- blockers disappear without decision records,
- notebooks become hidden authority,
- simulations cannot be rerun,
- benchmark failures are ignored,
- promotion rules are rewritten after results arrive,
- project conclusions cannot be traced to evidence.

## Operating Principle

The architecture should make honest uncertainty productive.

The goal is not to slow research down. The goal is to keep research moving without letting confidence detach from evidence.
