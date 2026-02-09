# Review: BRAGG Override Hardening (non-Git)

This repo is not a Git checkout, so change review is done via the snapshot/diff tooling in `formal/tooling_snapshots/`.

## Snapshot diffs produced

## Baselines promoted (2026-01-29)

To keep future diffs tight without hiding meaningful drift, this repo now maintains two snapshot baselines:

- **Pipeline baseline** (code/tests/locks/tools; excludes evidence payload dirs)
  - Snapshot: `formal/tooling_snapshots/repo_snapshot_20260129_172514_BASELINE_pipeline_bragg_override_hardened.jsonl`
  - Pointer: `formal/tooling_snapshots/LATEST_BASELINE_PIPELINE.txt`
  - Legacy pointer (for convenience): `formal/tooling_snapshots/LATEST_BASELINE.txt`
  - Human label: `formal/tooling_snapshots/BASELINE_pipeline_bragg_override_hardened_CURRENT.txt`

- **Evidence baseline** (external payloads only)
  - Snapshot: `formal/tooling_snapshots/repo_snapshot_20260129_172514_BASELINE_evidence_external_evidence.jsonl`
  - Pointer: `formal/tooling_snapshots/LATEST_BASELINE_EVIDENCE.txt`
  - Human label: `formal/tooling_snapshots/BASELINE_evidence_external_evidence_CURRENT.txt`

Sanity check: diffing pipeline baseline → working snapshot at the time of creation was tight:

- `formal/tooling_snapshots/diff_BASELINE_pipeline_to_WORKING_20260129_172514.txt` reports `COUNTS new=0 modified=0 missing=0`.

### Hardened baseline → current

- Baseline snapshot: `formal/tooling_snapshots/repo_snapshot_BASELINE_hardened_20260118_103004.jsonl`
- Current snapshot: `formal/tooling_snapshots/repo_snapshot_current_20260129.jsonl`
- Diff report: `formal/tooling_snapshots/diff_baseline_hardened_vs_current_20260129.txt`

Relevant entries for this work (as reported in the diff file):

- NEW `formal/python/toe/observables/ovbr04a_bragg_lowk_slope_conditionA_record.py`
- NEW `formal/python/toe/observables/ovfnwt00_fn01_weight_policy_declarations_record.py`
- NEW `formal/python/toe/observables/ovfnwt01_fn01_weight_policy_pruning_table_record.py`

- NEW `formal/python/tests/test_ov_br04a_results_primary_contract.py`
- NEW `formal/python/tests/test_ov_fn_wt00_wildcard_semantics.py`
- NEW `formal/python/tests/test_regen_canonical_locks_bragg_only_override_smoke.py`

- NEW `formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md`
- NEW `formal/markdown/locks/observables/OV-BR-04b_bragg_lowk_slope_conditionB_OVERRIDE.md`
- NEW `formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md`
- NEW `formal/markdown/locks/observables/OV-FN-WT-00_fn01_weight_policy_declarations_OVERRIDE.md`
- NEW `formal/markdown/locks/observables/OV-FN-WT-01_fn01_weight_policy_pruning_table_OVERRIDE.md`

Note: the diff report is intentionally broad; this section just extracts the subset relevant to the BRAGG override hardening work.

### Pre-regen → post-regen (BRAGG-only override)

This checks whether the BRAGG-only override regeneration command introduces churn.

- Pre snapshot: `formal/tooling_snapshots/repo_snapshot_pre_regen_bragg_override_20260129.jsonl`
- Post snapshot: `formal/tooling_snapshots/repo_snapshot_post_regen_bragg_override_20260129.jsonl`
- Diff report: `formal/tooling_snapshots/diff_pre_vs_post_regen_bragg_override_20260129.txt`

Result: **no file changes** (new=0, modified=0, missing=0). This indicates the regen lane is currently at a fixed point.

Practical note: the smoke test asserts idempotence across two consecutive regen runs. The first run is allowed to normalize legacy lock state; the second run must be a fixed point.

## Commands used (PowerShell)

The exact command lines are captured in terminal history; these are the key ones:

Manual invocation rule (durability): always route through the repo venv via `.\py.ps1`.

- Do: `.\py.ps1 -m formal.python.tools.repo_hygiene_snapshot ...`
- Don’t: `python -m formal.python.tools.repo_hygiene_snapshot ...` (can hit system Python)

- Create a snapshot:
  - `.\py.ps1 -m formal.python.tools.repo_hygiene_snapshot snapshot --out <path>.jsonl`
- Diff snapshots:
  - `.\py.ps1 -m formal.python.tools.repo_hygiene_snapshot diff <baseline>.jsonl <current>.jsonl --profile clean --ignore-quarantine --out <report>.txt`
