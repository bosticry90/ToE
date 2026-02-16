# Conditional Theorems Program v0

Scope and intent
- This document defines the Conditional Theorems (CT) program as a post-RL governance track.
- It constrains assumptions, claim surfaces, controls, and evidence handling.
- It is normative and programmatic only; no external truth claim is made.

Program posture
- expectation-aware controls are required for each CT evidence object.
- pinned artifacts, a lock file, and a front door are required for each CT entry.
- Each entry uses a comparator to encode pass/fail semantics.
- Suite status: governance suite green on 2026-02-12 (383 passed).
- Suite status policy: this line tracks the latest full governance-suite run and must stay synchronized with `State_of_the_Theory.md` via doc gates.

CT-01
- schema=CT-01
- assumptions: RL05 and RL11 pinned artifacts are admissible inputs.
- claim: bounded internal propagation does not exceed the pinned signal-cone bound.
- controls: positive control and negative control are expectation-aware.

CT-02
- schema=CT-02
- assumptions: RL07 and RL11 pinned artifacts are admissible inputs.
- claim: bounded internal energy drift and CFL admissibility under pinned update bounds.
- controls: positive control and negative control are expectation-aware.

CT-03
- schema=CT-03
- assumptions: RL07 and RL11 pinned artifacts are admissible inputs.
- claim: CT-02 bounds hold under an alternate energy representation.
- controls: positive control and negative control are expectation-aware.

CT-04
- schema=CT-04
- assumptions: CT-02 pinned update bounds are the baseline comparator surface.
- claim: removing the CFL bound triggers a minimality no-go under the pinned surface.
- controls: positive control and negative control are expectation-aware.

CT-05
- schema=CT-05
- assumptions: CT-02 and CT-03 pinned artifacts plus RL11 admissibility are admissible inputs.
- claim: admissibility and bound status agree across the pinned representation map within eps.
- controls: positive control and negative control are expectation-aware.

CT-06
- schema=CT-06
- assumptions: pinned public dispersion dataset + pinned preprocessing assumptions are admissible inputs.
- claim: candidate dispersion curve reproduces the pinned observable within tolerance or fails under explicit pass/fail semantics.
- controls: positive control and negative control are expectation-aware.

CT-07
- schema=CT-07
- assumptions: CT-06 origin dataset plus pinned low-k slice preprocessing are admissible inputs.
- claim: low-k slice reproducibility holds within CT-07 tolerances under explicit non-independence from CT-06.
- controls: positive control and negative control are expectation-aware.

CT-08
- schema=CT-08
- assumptions: CT-06 origin dataset plus pinned high-k slice preprocessing are admissible inputs.
- claim: high-k slice reproducibility holds within CT-08 tolerances under explicit non-independence from CT-06.
- controls: positive control and negative control are expectation-aware.

CT-09
- schema=CT-09
- assumptions: pinned independent distance-time dataset plus pinned preprocessing assumptions are admissible inputs.
- claim: independent external-anchor sound-speed fit reproducibility holds within CT-09 tolerances under explicit pass/fail semantics.
- controls: positive control and negative control are expectation-aware.

CT-10 (pre-activation selection filter)
- schema=CT-10
- assumptions: candidate anchor must satisfy the deterministic selection filter in `formal/docs/programs/CT10_independent_external_anchor_selection_filter_v0.md`.
- claim: none; this is an admission gate only and does not assert comparator outcomes.
- controls: deterministic filter verdict record is required; lane activation is blocked-on-missing until a full CT-10 comparator entry exists.

External-anchor cluster lock (CT-06/CT-07/CT-08)
- Treat CT-06/CT-07/CT-08 as one evidence family with two regime probes (low-k, high-k).
- CT-07 and CT-08 are explicitly non-independent (`non_independent_of_CT06`) and must not be framed as independent confirmations.
- Cluster policy and limits are pinned in `formal/docs/programs/CT_external_anchor_cluster_v0.md`.

Required governance vocabulary
- assumptions
- claim
- controls
- positive control
- negative control
- expectation-aware
- no external truth claim
- pinned artifacts
- lock file
- front door
- comparator
- RL05
- RL11
- external anchor
- dispersion
- dataset_id
- low-k slice
- high-k slice
- non_independent_of_CT06
- independent external anchor
- distance_um_vs_time_ms
- CT-10
- selection filter
- admission gate
- different observable surface
- source lineage independence
- preprocessing lineage independence
- not BEC-derived
- blocked-on-missing

Revision policy
- Updates require explicit version bump, doc-gate update, and governance-suite approval.






