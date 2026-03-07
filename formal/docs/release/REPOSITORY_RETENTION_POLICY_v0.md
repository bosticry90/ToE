# Repository Retention Policy v0

Document ID: REPOSITORY_RETENTION_POLICY_v0
Owner: Governance
Status: Active
Last-Updated: 2026-03-06

## Scope Tokens

RETENTION_SCOPE_SCRATCH_v0: SHORT_LIVED_WORK_ARTIFACTS
RETENTION_SCOPE_TOOLING_SNAPSHOTS_v0: TRANSITIONAL_PIPELINE_EVIDENCE
RETENTION_SCOPE_BACKUP_v0: DATED_CANONICAL_BACKUPS
RETENTION_SCOPE_ARCHIVE_v0: FROZEN_LEGACY_REFERENCE
RETENTION_POLICY_GOVERNANCE_GATE_v0: formal/python/tests/test_repository_retention_policy_contract_gate.py

## Policy

- `scratch/` is transient and should be pruned after merge/reconciliation.
- `formal/tooling_snapshots/` is transitional and should be reduced when superseded.
- `backup/` is dated and should be retained only with explicit date labeling.
- `archive/` is frozen reference material and should not be used for active imports.
- New large generated artifacts should prefer quarantined output paths over root-level sprawl.

## Operational Cadence

- 30-day cadence: prune obsolete files from `scratch/`.
- 60-day cadence: consolidate superseded files under `formal/tooling_snapshots/`.
- 90-day cadence: review `backup/` and archive or remove outdated snapshots.
