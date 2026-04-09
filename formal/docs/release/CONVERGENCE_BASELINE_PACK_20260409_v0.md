# CONVERGENCE_BASELINE_PACK_20260409_v0

## Status
- ACTIVE
- Date: 2026-04-09
- Class: CONVERGENCE_QUALITY_AND_REDUNDANCY_BASELINE_NONCLAIM

## Objective
Publish a frozen baseline pack with exactly five required metrics so downstream convergence-quality claims are machine-checkable against a stable reference.

## Required metrics (exactly five)
1. blocker count by class
2. theorem-depth baseline score
3. redundant-registry count
4. checkpoint count
5. active canonical owners list

## Baseline pack pointer
- formal/output/reports/convergence_baseline_pack_20260409_v0.json

## Metric sources
- Blocker-burn source: formal/output/ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json
- Theorem-depth source: formal/output/reports/physics_math_throughput_phase3_t08_theorem_depth_execution_packet_20260407_v0.json
- Completion baseline source: formal/output/ws10_global_completion_baseline_snapshot_20260408_v0.json

## Freeze contract
- No phase-level improvement claim is valid unless it cites delta versus formal/output/reports/convergence_baseline_pack_20260409_v0.json.
- Any replacement baseline pack must preserve this five-metric schema and publish an explicit supersession note.

## Next implementation hook
- Gate path: formal/python/tests/test_convergence_baseline_pack_gate.py
- Checklist linkage: Canonical Verification Checklist baseline and promotion-significance fields.

## Non-claim boundary
This artifact is a repository-local governance and convergence control surface only.
