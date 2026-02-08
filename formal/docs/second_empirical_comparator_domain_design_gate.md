# Second Empirical Comparator Domain Design Gate

Domain ID (design): `DRBR-DOMAIN-02`

Purpose: pin selection criteria for a second comparator domain without activating
implementation.

Status: design-only; no status upgrade.

## Selection criteria

- typed artifact schema with deterministic fingerprints;
- reproducible extraction/provenance trail;
- at least one comparator condition with deterministic fail mode;
- no dependency on override lanes;
- explicit non-claims and scope limits.

## Candidate shortlist (design only)

- BEC sound-propagation lane (Andrews family) with low-k speed proxies;
- shallow-water low-k analog lane;
- second Bragg-source cross-anchor lane with overlap-only comparability.

## Activation gate

Domain promotion requires all:

- a pinned domain doc with canonical artifact paths;
- artifact-existence + fingerprint tests;
- front-door comparator module with schema freeze tests;
- blocked-on-missing-input behavior;
- deterministic negative control.

## Non-claims

- This does not select or activate `DRBR-DOMAIN-02`.
- This does not alter `DRBR-DOMAIN-01` governance.
- This does not authorize comparator expansion by narrative-only edits.
