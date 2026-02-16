# QM Evolution Resolution Trend Record v0

Record ID:
- `QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0`

Classification:
- `P-POLICY`

Status token:
- `QM_EVOLUTION_RESOLUTION_TREND_STATUS_v0: TEMPLATE_PINNED`
- `QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ROW_QM_RESOLUTION_32_POPULATED`
- `QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ROW_QM_RESOLUTION_64_POPULATED`
- `QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ROW_QM_RESOLUTION_128_POPULATED`
- `QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ALL_REQUIRED_RESOLUTION_ROWS_POPULATED`

Required trend fields:
- `residual_norm`
- `convergence_trend`
- `limit_break_annotation`

Required resolution IDs:
- `QM_RESOLUTION_32_v0`
- `QM_RESOLUTION_64_v0`
- `QM_RESOLUTION_128_v0`

Execution schema:

| Resolution ID | Grid size | residual_norm | convergence_trend | limit_break_annotation | Artifact pointer |
|---|---|---|---|---|---|
| `QM_RESOLUTION_32_v0` | `32` | `0.0111` | `baseline_anchor_v0` | `none_observed_at_baseline` | `formal/output/qm_evolution_resolution_trend_32_v0.json` |
| `QM_RESOLUTION_64_v0` | `64` | `0.0079` | `improving_vs_32_v0` | `none_observed_at_64` | `formal/output/qm_evolution_resolution_trend_64_v0.json` |
| `QM_RESOLUTION_128_v0` | `128` | `0.0055` | `improving_vs_64_v0` | `none_observed_at_128` | `formal/output/qm_evolution_resolution_trend_128_v0.json` |

Synchronization pointers:
- `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0.md`
- `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
