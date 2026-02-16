# CT-10 Independent External Anchor Selection Filter v0

Status: Active governance selection filter (pre-activation admission gate)

Purpose
- Define deterministic admission criteria for the next independent external anchor family.
- Enforce anchor multiplicity pressure without activating a CT-10 comparator claim yet.
- Keep scope bounded to governance and intake discipline only.

Selection criteria (all required)
- Candidate is a truly independent source family relative to CT-06/CT-07/CT-08 and CT-09.
- Candidate uses a different observable surface than existing dispersion and distance-time anchors.
- Candidate is not BEC-derived.
- Candidate has source lineage independence (citation/provenance tree does not reuse existing family roots).
- Candidate has preprocessing lineage independence (new extraction + preprocessing path; no shared preprocessing lineage).
- Candidate has public source citation, pinned dataset metadata, and reproducible fingerprints.
- Candidate introduces distinct model sensitivities for adversarial break studies.

Disqualifiers (any one is a hard reject)
- Slice, transform, or repackaging of CT-06/CT-07/CT-08 source rows.
- Reuse of CT-09 source rows or front-door report artifacts.
- Dataset or preprocessing copied from an existing anchor family with only parameter/window changes.
- Cross-anchor averaging or blended-comparator framing.

Required artifacts before CT-10 lane activation
- Intake folder at `formal/external_evidence/ct10_independent_external_anchor_tbd/`.
- Source citation with explicit lineage statement.
- Dataset metadata with frozen fingerprint fields.
- Deterministic selection-verdict record documenting pass/fail reasons.
- Doc-gate tests proving non-claim posture and required vocabulary.

Scope limits
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- external_anchor_only
- blocked-on-missing
- no external truth claim

Activation rule
- CT-10 comparator lane remains blocked until this selection filter passes and all lane artifacts are implemented.
- No comparator claims are permitted until a CT-10 lane module, front door, lock, and tests exist.

Governance vocabulary
- CT-10
- selection filter
- admission gate
- independent external anchor
- different observable surface
- source lineage independence
- preprocessing lineage independence
- not BEC-derived
- external_anchor_only
- blocked-on-missing
- no external truth claim
