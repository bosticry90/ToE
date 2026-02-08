# Second Empirical Comparator Domain (Pinned)

Domain ID: `DRBR-DOMAIN-02`

Selected domain: BEC Bragg secondary-source low-k fit anchor (Ernst 2009 family; B1 lane).

Status: selected and pinned for second comparator entry; no status upgrade.

## Why this domain

- Typed DR-01 linear/curved artifacts already exist with deterministic fingerprints.
- This source provides a cross-source stress lane relative to `DRBR-DOMAIN-01`.
- The lane is suitable for deterministic comparator negative-control behavior and controlled pruning pressure.

## Canonical input artifacts

- `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr01_fit_artifact.json`
- `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr01_fit_artifact_curved.json`

Required artifact properties:

- typed schema-compatible payload
- `data_fingerprint` present and reproducible from `sample_kw`
- provenance fields present (`source_kind`, `source_ref`, `fit_method_tag`)

## Comparator entry condition

The first comparator implementation under this domain is admissible only when:

- front-door comparator module is lock-tested with deterministic record output;
- blocked-on-missing-input behavior is tested;
- at least one deterministic negative control is present.

## Non-claims

- This selection does not assert external truth.
- This selection does not authorize unconstrained comparator expansion.
- This selection does not bypass disabled-by-default gate policy.
