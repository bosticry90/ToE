# CONVERGENCE_PROMOTION_SIGNIFICANCE_DECLARATION_20260409_v0

status: ACTIVE_NONLIVE_NONCLAIM
scope: CONVERGENCE_FIRST_HARDENING_PHASE1_DECLARATION
last_updated: 2026-04-09

## Purpose

Declare the minimum machine-check fields required before any phase-level convergence
promotion claim may be treated as admissible under current authority surfaces.

## Required Fields (machine-checked)

1. discriminator_threshold
2. discriminator_score
3. blocker_reduction_claim
4. proof_debt_movement
5. baseline_pack_pointer

Missing any required field is a hard fail for this gate.

## Promotion-Significance Rule

A promotion-significance checkpoint must declare:

- a discriminator threshold (explicit numeric boundary),
- a measured discriminator score for the candidate slice,
- blocker movement relative to baseline, and
- proof-debt movement relative to baseline.

This declaration is a governance contract only and does not authorize live/theory status
promotion by itself.

## Pinned Pointers

- baseline_pack_pointer: formal/output/reports/convergence_baseline_pack_20260409_v0.json
- checkpoint_pointer: formal/output/reports/convergence_promotion_significance_checkpoint_20260409_v0.json
- gate_pointer: formal/python/tests/test_convergence_promotion_significance_gate.py
