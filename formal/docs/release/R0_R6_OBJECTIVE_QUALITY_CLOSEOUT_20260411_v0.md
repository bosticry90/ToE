# R0-R6 Objective-Quality Closeout Policy (v0)

Status: ACTIVE_NONLIVE_NONCLAIM
Schema ID: R0_R6_OBJECTIVE_QUALITY_CLOSEOUT_20260411_v0

## Purpose

Declare machine-checkable closeout criteria for the R0-R6 governance/control stack while preserving a strict separation between control-stack completeness and scientific completion.

## Required Inputs

- `formal/output/reports/science_global_completion_baseline_20260411_v0.json`
- `formal/output/reports/theorem_gap_reduction_wave_20260411_v0.json`
- `formal/output/reports/theorem_gap_execution_linkage_20260411_v0.json`
- `formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json`
- `formal/output/reports/theorem_gap_single_row_execution_20260411_v0.json`
- `formal/output/reports/theorem_gap_qm_rework_tranche_20260411_v0.json`
- `formal/output/reports/theorem_gap_qm_subtarget_tranche_20260411_v0.json`

## Objective Criteria

1. All R0-R6 report files exist and are parseable JSON.
2. Each report materializes an `objective_quality` surface.
3. Each report advertises `summary.phase_status == COMPLETE` for contract execution.
4. R2 no-change fail-closed route semantics remain present.
5. R3 row-level stagnation visibility remains materialized.
6. R4 and R5 no-change fail-closed route fields remain materialized.
7. R6 failure diagnosis remains materialized.

## Completion Semantics

- `control_stack_objective_complete = true` means objective-quality control instrumentation for R0-R6 is complete.
- `scientific_objective_complete = true` is a separate condition and depends on real blocker movement.
- `global_objective_complete = control_stack_objective_complete && scientific_objective_complete`.

## Non-Claim Boundary

This artifact does not claim scientific adequacy or completion. It certifies control-stack coverage and preserves fail-closed routing semantics.