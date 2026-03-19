# Quarantine Register v0

Spec ID:
- `QUARANTINE_REGISTER_v0`

Classification:
- `P-POLICY`

Purpose:
- Track intentionally quarantined files and families with explicit re-entry conditions.
- Prevent silent archive drift and undocumented long-term exclusions.

Non-claim boundary:
- control artifact only.
- no theorem promotion.
- no status promotion.

## Row schema

- `item_id`
- `file_or_family`
- `reason_quarantined`
- `date_quarantined`
- `owner`
- `reentry_condition`
- `status` (`ACTIVE` or `RETIRED`)
- `notes`

## Active rows

| item_id | file_or_family | reason_quarantined | date_quarantined | owner | reentry_condition | status | notes |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `QR-0001` | `formal/python/tests/**/test_cosmo_bg_micro*_dryrun_*` | Extremely repetitive custody/dryrun gate family; high maintenance cost and low incremental discriminative value per file. | `2026-03-17` | `ToE governance` | Consolidated registry-driven replacement exists and parity subset passes for representative packets/micros. | `ACTIVE` | Family is retained on disk for traceability until replacement suite is validated. |
| `QR-0002` | `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_*_DRYRUN_*` | Large procedural packet family dominates review surface and obscures science-facing deltas. | `2026-03-17` | `ToE governance` | Canonical summary route and bounded representative packet set are pinned; residual files archived or explicitly retained by policy. | `ACTIVE` | Does not alter current status tokens; registration only. |

## Maintenance rules

1. Any new quarantine row must include a measurable re-entry condition.
2. Quarantine status must be reviewed before each major release note cycle.
3. Quarantine does not imply deletion; it implies bounded non-default review status.
