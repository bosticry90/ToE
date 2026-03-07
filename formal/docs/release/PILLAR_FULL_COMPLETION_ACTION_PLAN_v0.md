# Pillar Full Completion Action Plan v0

Document ID: PILLAR_FULL_COMPLETION_ACTION_PLAN_v0
Owner: Governance
Status: Active Planning
Last-Updated: 2026-03-06

## Purpose

Define the work required to move all pillars from current mixed closure posture
(matrix/roadmap CLOSED but several derivation rows still conditional or blocked)
into a terminal full-completion posture with no unresolved pillar-critical rows.

## Current Reality Snapshot

- Matrix status is CLOSED for all pillars.
- Phase registry modes are mixed:
  - PILLAR-STAT: CLOSED_HANDOFF
  - PILLAR-COSMO: CLOSED_HANDOFF
  - PILLAR-SR: CLOSED_HANDOFF
  - PILLAR-GR, PILLAR-QM, PILLAR-EM: CLOSED_HANDOFF
  - PILLAR-QFT: CLOSED_HANDOFF_ARTIFACT
- Results table still includes unresolved rows impacting full-completion claims:
  - GR blocked rows: TOE-GR-01, TOE-GR-THM-01
  - Multiple pillar derivation rows remain T-CONDITIONAL (GR/EM/STAT/COSMO).

## Full-Completion Definition

A pillar is considered fully complete only when all of the following are true:

1. Phase registry mode is terminal (no ACTIVE_EXECUTION, LOCKED_QUEUE, or PHASE_ORDERED).
2. Matrix status, roadmap status, state status, and proceed/matrix-closure gates are synchronized.
3. Pillar-critical rows in RESULTS_TABLE are not B-BLOCKED.
4. Pillar-critical derivation rows are not governance-only placeholders.
5. Full governance suite passes.

## Program Phases

### Phase 1: Normalize Completion Contract

1. Add explicit per-pillar completion checklist tokens in authority docs.
2. Add a cross-pillar full-completion gate asserting definition items above.
3. Add a policy note that CLOSED matrix status is necessary but not sufficient for full completion.

Exit criteria:
- New completion gate exists and is wired into governance_suite.ps1.
- Gate fails on any pillar that violates the definition.

### Phase 2: Resolve Non-Terminal Modes

1. PILLAR-STAT: execute reopen sequence to closure and transition mode from ACTIVE_EXECUTION to terminal mode.
2. PILLAR-COSMO: complete LOCKED_QUEUE transition packet lifecycle and move mode to terminal mode.
3. PILLAR-SR: retire PHASE_ORDERED mode by marking all phase pairs complete and promoting to terminal mode.

Exit criteria:
- No pillar in phase registry has mode ACTIVE_EXECUTION, LOCKED_QUEUE, or PHASE_ORDERED.

### Phase 3: Clear Blocked and Conditional Derivation Debt

1. GR:
   - Resolve TOE-GR-01 and TOE-GR-THM-01 blocked rows.
   - Promote GR derivation rows from conditional to fully discharged theorem posture where intended.
2. EM:
   - Convert discharge-lane conditional posture to final theorem-grade closure posture where intended.
3. STAT:
   - Convert derivation rows from scaffold-conditional posture to final closure posture after phase completion.
4. COSMO:
   - Convert conditional closure package posture to terminal closure posture once queue transitions are complete.

Exit criteria:
- No pillar-critical rows remain B-BLOCKED.
- Targeted rows no longer depend on temporary transition semantics.

### Phase 4: Cross-Pillar Unification and Residual-Risk Closure

1. Add a unification target that composes pillar-level closure contracts under shared assumptions.
2. Add counterfactual and necessity checks at cross-pillar level.
3. Add final release gate verifying no legacy contradiction between matrix closure and results semantics.

Exit criteria:
- Unification target is pinned with passing gates.
- No residual cross-surface contradiction warnings.

## Pillar-Specific Work Packages

### PILLAR-GR

- Primary debt: blocked theorem/derivation rows in results table.
- Work package:
  - Close weak-field theorem-surface debt.
  - Discharge analytic bridge obligations required to remove B-BLOCKED rows.

### PILLAR-QM

- Primary debt: plan-heavy posture around measurement/symmetry targets.
- Work package:
  - Elevate remaining plan-only targets to derivation artifacts where intended.
  - Add explicit completion evidence tying theorem chains to results rows.

### PILLAR-EM

- Primary debt: conditional closure semantics despite closed matrix posture.
- Work package:
  - Convert governance-conditional row language to final closure language after theorem-grade checks.

### PILLAR-SR

- Primary debt: PHASE_ORDERED operational mode.
- Work package:
  - Complete and retire phase-pair transitions.
  - Promote to terminal mode and freeze residual phase gates.

### PILLAR-QFT

- Primary debt: CLOSED_HANDOFF_ARTIFACT still signals handoff-phase semantics.
- Work package:
  - Retire handoff artifact mode by replacing with terminal completed mode after artifact finalization checks.

### PILLAR-STAT

- Primary debt: derivation rows remain scaffold-conditional despite terminal mode closure.
- Work package:
  - Execute reopen-completion cycle.
  - Promote derivation rows from scaffold-conditional to final closure posture.

### PILLAR-COSMO

- Primary debt: conditional closure-package posture remains after mode normalization.
- Work package:
  - Preserve closed-handoff governance parity while retiring compatibility-only semantics.
  - Promote conditional closure-package posture to terminal closure posture.

## Recommended Execution Order

1. Phase 1 contract normalization.
2. Phase 2 mode normalization (STAT, COSMO, SR).
3. Phase 3 derivation debt closure (GR first, then STAT/COSMO/EM, then QM plan-to-derivation upgrades).
4. Phase 4 unification and final risk retirement.

## Validation Commands

- Full governance:
  - ./governance_suite.ps1
- Focused pillar sweep:
  - ./py.ps1 -m pytest -q formal/python/tests -k "cosmo_ or stat_ or gr_ or sr_ or em_ or qm_ or qft_ or phase_adherence or pillar_phase_advancement"

## Success Signal

All pillars are terminal-mode complete, no pillar-critical blocked rows remain,
conditional-only transition semantics are retired, and governance suite is green.
