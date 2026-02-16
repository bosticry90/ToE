# GR01 Resolution Trend Record v0

Record ID:
- `GR01_RESOLUTION_TREND_RECORD_v0`

Classification:
- `P-POLICY`

Purpose:
- Pin Phase IV multi-resolution trend obligations for GR01 in bounded/discrete weak-field v0 scope.
- Record trend behavior without claiming continuum-limit GR recovery.

Scope boundary:
- bounded/discrete weak-field v0 only
- no continuum-limit promotion
- no full-GR claim

Status token:
- `GR01_RESOLUTION_TREND_STATUS_v0: TEMPLATE_PINNED`
- `GR01_RESOLUTION_TREND_PROGRESS_v0: ROW_RESOLUTION_32_POPULATED`
- `GR01_RESOLUTION_TREND_PROGRESS_v0: ROW_RESOLUTION_64_POPULATED`
- `GR01_RESOLUTION_TREND_PROGRESS_v0: ROW_RESOLUTION_128_POPULATED`
- `GR01_RESOLUTION_TREND_PROGRESS_v0: ALL_REQUIRED_RESOLUTION_ROWS_POPULATED`

## Required resolution set (must remain present)

- `RESOLUTION_32_v0`
- `RESOLUTION_64_v0`
- `RESOLUTION_128_v0`

## Required trend fields (must remain present)

- `residual_norm`
- `convergence_trend`
- `kappa_calibration_stability`
- `limit_break_annotation`

## Execution schema (template rows)

| Resolution ID | Grid size | residual_norm | convergence_trend | kappa_calibration_stability | limit_break_annotation | Artifact pointer |
|---|---|---|---|---|---|---|
| `RESOLUTION_32_v0` | `32` | `0.0125` | `baseline_anchor_v0` | `stable_within_v0_tolerance` | `none_observed_at_baseline` | `formal/output/gr01_resolution_trend_32_v0.json` |
| `RESOLUTION_64_v0` | `64` | `0.0087` | `improving_vs_32_v0` | `stable_within_v0_tolerance` | `none_observed_at_64` | `formal/output/gr01_resolution_trend_64_v0.json` |
| `RESOLUTION_128_v0` | `128` | `0.0062` | `improving_vs_64_v0` | `stable_within_v0_tolerance` | `none_observed_at_128` | `formal/output/gr01_resolution_trend_128_v0.json` |

## Limit-break policy

- If convergence does not improve with resolution, record:
  - deterministic reason code,
  - first failing trend criterion,
  - explicit scope-boundary statement.

## Synchronization pointers

- Hardening target: `formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md`
- State checkpoint: `State_of_the_Theory.md`
