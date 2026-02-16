# CT External-Anchor Cluster v0 (CT-06/CT-07/CT-08)

Status: Pinned governance cluster

Purpose
- Lock CT-06, CT-07, and CT-08 as one external-anchor evidence family.
- Keep low-k and high-k entries as regime probes, not independent confirmations.
- Preserve explicit scope limits and non-independence labels.

Cluster definition
- Anchor family root: CT-06 (`Steinhauer2001_Fig3a_Digitized_v1`).
- Probe A: CT-07 low-k slice (`non_independent_of_CT06`).
- Probe B: CT-08 high-k slice (`non_independent_of_CT06`).

Interpretation policy
- CT-07 and CT-08 are not independent external confirmations.
- CT-07 and CT-08 are deterministic conditional probes of the CT-06 family.
- Claims remain dataset-conditional and front-door bounded.

Required governance posture
- Deterministic front door artifacts for each lane.
- Comparator pass/fail semantics with expectation-aware controls.
- Negative control must be explicit break detection.
- Lock markdown must match deterministic comparator record.
- Scope label must include no external truth claim.

Cluster-level limits
- Evidence family count: one (CT-06 root family).
- Regime probes: two (low-k, high-k).
- External-evidence independence count: one until a new independent dataset lane is added.
- CT-10 selection filter governs admission of the next independent family; independence count does not increase until a CT-10 lane is implemented and locked.
