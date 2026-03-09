# SR M5 Archive Retention Policy v0

Spec ID:
- `SR_M5_ARCHIVE_RETENTION_POLICY_v0`

Classification:
- `P-POLICY`

Canonical pointer:
- `formal/docs/release/SR_M5_ARCHIVE_RETENTION_POLICY_v0.md`

Purpose:
- Preserve cycle-level SR M5 governance traceability without losing active-cycle operational clarity.
- Define deterministic retention and compaction boundaries for historical SR M5 artifacts and gates.

Non-claim boundary:
- planning-only policy artifact.
- non-claim governance control.
- no scientific or external truth claim.

Canonical scope:
- historical files matching:
  - `formal/output/sr_m5_theory_parity_link_cycle*_v0.json`
  - `formal/python/tests/test_sr_m5_theory_parity_link_cycle*_gate.py`

Retention rules:
1. Exactly one active SR M5 gate is permitted and must be non-skipped.
2. All prior SR M5 cycle gates remain archived and skip-marked for traceability.
3. Historical SR M5 artifacts remain immutable once superseded.
4. Compaction is allowed only via explicit policy revision that preserves:
   - cycle index traceability,
   - active-cycle reproducibility,
   - cross-surface pointer/hash auditability.

Operational guardrails:
- Active-cycle rollovers must run through:
  - `formal/python/tools/sr_m5_cycle_rollover.py`
- Periodic checkpoint reports are generated through:
  - `formal/python/tools/sr_m5_quality_checkpoint_report.py`
- Archive discipline is machine-enforced by:
  - `formal/python/tests/test_sr_m5_cycle_archive_discipline_gate.py`
- Retention policy bounds are machine-enforced by:
  - `formal/python/tests/test_sr_m5_archive_retention_policy_gate.py`
- Periodic checkpoint freshness is machine-enforced by:
  - `formal/python/tests/test_sr_m5_periodic_quality_checkpoint_gate.py`
- Next-target terminal semantics are machine-enforced by:
  - `formal/python/tests/test_pillar_deep_maturity_next_target_semantics_gate.py`

Status token:
- `SR_M5_ARCHIVE_RETENTION_POLICY_STATUS_v0: ACTIVE_v0`
- `SR_M5_ARCHIVE_RETENTION_MAX_HISTORY_v0: 200`
- `SR_M5_QUALITY_CHECKPOINT_CADENCE_v0: 10`
