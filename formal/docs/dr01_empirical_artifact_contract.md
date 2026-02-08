# DR-01 Empirical Artifact Contract (bounded)

Last updated: 2026-02-08

## Purpose

Define a small, deterministic contract for DR-01 empirical fit artifacts used by BR-01 bridges.
This is a data-contract and provenance surface only; it does not assert external truth by itself.

## Canonical artifact types

- Linear fit artifact (DR-01 low-k linearization)
  - Required keys:
    - `u`, `c_s`
    - `tag`, `source_kind`, `source_ref`, `fit_method_tag`
    - `sample_kw`, `data_fingerprint`
- Curved fit artifact (DR-01 curved proxy in y=omega/k space)
  - Required keys:
    - `u`, `c0`, `beta`
    - `tag`, `source_kind`, `source_ref`, `fit_method_tag`
    - `sample_kw`, `data_fingerprint`

## Fingerprint rule

- `data_fingerprint` must be `sha256` of a canonical encoding of `sample_kw`:
  - sort pairs by `(k, omega)`
  - format each pair as `"{k:.17g},{omega:.17g}"`
  - join with newline and trailing newline
  - hash UTF-8 bytes

## Intended bridge usage

- BR-01 front doors should consume `DR01Fit1D` / `DR01FitCurved1D` artifacts and emit deterministic metric vectors.
- Candidate pruning locks should reference these fingerprinted artifacts, not ad-hoc tuples.

## Test evidence

- Provenance + fingerprint stamping:
  - `formal/python/tests/test_dr01_fit_artifact_provenance.py`
- Contract-key and fingerprint checks on canonical external artifacts:
  - `formal/python/tests/test_dr01_empirical_artifact_contract.py`
- BR-01 front-door metric vector surface:
  - `formal/python/tests/test_br01_metric_vector_front_door.py`
