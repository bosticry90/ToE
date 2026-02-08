# First Empirical Comparator Domain (Pinned)

Domain ID: `DRBR-DOMAIN-01`

Selected domain: BEC Bragg low-k dispersion anchor (Steinhauer 2001 family).

Status: selected and pinned for first cross-domain comparator entry; no status upgrade.

## Why this domain

- Existing typed artifacts already exist and are fingerprinted.
- Existing BR-01 and OV-DR-BR-01 surfaces already consume this artifact family.
- Failure in this domain can eliminate candidate families under explicit reason codes.

## Canonical input artifacts

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json`

Required artifact properties:

- typed schema-compatible payload
- `data_fingerprint` present and reproducible from `sample_kw`
- provenance fields present (`source_kind`, `source_ref`, `fit_method_tag`)

## Comparator entry condition

The first comparator implementation under this domain is admissible only when:

- Phase 1/3 structural closure remains green in Lean linkage tests;
- DR-01 -> BR-01 front-door tests are green;
- candidate pruning table shows at least one eliminator with deterministic reason code.

## Non-claims

- This selection does not assert external truth.
- This selection does not authorize unconstrained comparator expansion.
- This selection does not bypass disabled-by-default gate policy.
