# CT-09 Independent External Anchor Plan v0

Status: Historical planning artifact retained post-implementation (superseded by CT-09 v0 lane)

Objective
- Introduce one truly independent external dataset for the next external-anchor CT entry.
- Keep the implementation pattern identical to CT-06/07/08 (pinned definition, front door, comparator, controls, lock).

Independence requirement
- Dataset provenance must be independent from `Steinhauer2001_Fig3a_Digitized_v1`.
- The new lane must not be a slice, transform, or repackaging of CT-06 source rows.
- Source citation and dataset metadata must include a clear independence statement.

Required implementation pattern
- Pinned dataset intake contract with fingerprint and citation.
- Deterministic front-door report generation.
- Comparator with expectation-aware pass/fail semantics.
- Positive control and negative control (explicit break detection).
- Lock markdown that matches comparator record.

Planned artifacts
- Domain folder: `formal/external_evidence/ct09_independent_external_anchor_tbd/`
- Program doc entry with bounded claim type (`external_anchor_only`).
- Comparator manifest entry with `within_rep_only` unless additional policy upgrades are proven.

Scope limits (must remain explicit)
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- external_anchor_only
- no external truth claim

Execution status
- Historical status at creation: Planned (not implemented).
- This planning object is retained for provenance and does not assert any CT-09 result.
- Active implementation superseding this plan: `formal/docs/programs/CT09_independent_external_anchor_sound_speed_v0.md`.
