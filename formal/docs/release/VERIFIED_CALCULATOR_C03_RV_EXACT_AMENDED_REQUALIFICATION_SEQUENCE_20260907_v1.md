# C03/RV Exact Computation — Amended Requalification Sequence v1

Status: `DEFINED_NOT_EXECUTED`

This sequence governs the next exact-evidence lineage after non-author review defects D-01/D-02 and Linux qualification failure D-07. It is a repair and qualification contract, not implementation evidence, scientific promotion, product release, or production activation.

## Preserved baseline

The following records are immutable inputs to the amendment comparison:

- frozen v1 bundle: `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`;
- non-author review: `SUPPORTED_WITH_REQUIRED_AMENDMENTS`, hash `d415ae3d690b4bcf87d6222f8618371af2d1a28b0c624843f95b8649cb816b15`;
- Linux v5 qualification: `FAIL`, result-record hash `e4a7a5e961b9c60a9e29d4beabb3b5e4984a0456f835ae17dad7a8d265e7a48f`;
- repair-test contract: `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_REPAIR_ACCEPTANCE_TESTS_20260907_v1.json`, definition hash `009590b4923f73956139916b2d43b4b1171b5a32f8125705d4666b90cc5542e9`.

The frozen v1 bundle, review result, and Linux failure evidence must not be edited or replaced.

## Scope lock

The amendment contains only:

1. D-07: explicit cross-platform dependency hash domains;
2. D-01: runtime/Lean certificate identity binding;
3. D-02: complete executable `ValueTypeV1` metadata enforcement.

It must not add physics records, source meanings, authoritative roots, physics operations, expected answers, or scientific-authority promotions. The mandatory challenge corpus remains the same ten specifications and 373 instances unless a separately reviewed defect proves an amendment necessary.

## Identity rule

The amended physics profile, verification policy, calculation request, computation ID, certificate, receipt, dependency closure, and bundle are expected to receive new identities because their contracts and evidence formats change. Equality of those hashes with v1 is neither expected nor an acceptance criterion.

Instead, the amendment must prove a complete scientific-payload equivalence ledger:

| Surface | Required comparison with v1 |
| --- | --- |
| Sources | Same 31 source IDs, typed locators, resolved canonical values, meanings, and authority boundaries |
| Derived graph | Same 160 node IDs, physics operations, ordered parents, parameters, and canonical exact values |
| Operations | Same 19 physics-operation semantics; only type enforcement may be strengthened |
| Roots | Same 16 root IDs, claims, canonical exact values, and `does_not_claim` limits |
| Challenges | Same 373 mandatory applications, affected roots, and rejection outcomes |
| Authority | Same claim-by-claim historical labels and ceilings; calculator-profile requalification initially remains unearned |

Any difference outside the expected evidence/contract-format delta stops amendment-only qualification and requires broader review.

## Ordered sequence

### Stage 0 — preserve and branch the evidence lineage

- Record the exact parent commit, frozen v1 artifact/hash, v5 failure artifact/hash, and non-author review/hash.
- Create a new versioned repair/evidence lineage; do not overwrite any v1 object.
- Generate a changed-file and transitive-impact manifest before implementation.

Exit gate: all parent evidence is present, hash-valid, Git-tracked, and marked non-promotional.

### Stage 1 — freeze dependency hash-domain semantics

- Implement `GIT_BLOB_BYTES_V1` as the primary identity for tracked dependencies.
- Implement `CANONICAL_TEXT_V1` only for explicitly declared semantic-text equivalence checks: strict UTF-8, no BOM, CRLF/CR to LF, and no other normalization.
- Retain `filesystem_sha256` only as an observed execution fact; never use it ambiguously as the tracked dependency identity.
- Generate the complete dependency closure and hash-domain ledger from the tested commit.

Exit gate: repair test `RAT-A-D07-CROSS_PLATFORM_DEPENDENCY_IDENTITY` passes, including LF/CRLF equivalence and genuine-content mutation rejection.

### Stage 2 — implement non-circular runtime/Lean binding

- Version the Lean-facing certificate or qualification envelope and its checker.
- Make Lean compute the domain-separated certificate identity from canonical parsed fields.
- Supply expected contract/evidence identities through an independently serialized verification context; remove caller-asserted accepted-hash authority.
- Bind certificate to receipt and receipt/certificate to the outer bundle. The final bundle hash is not placed inside the certificate, avoiding a circular identity.

Exit gate: repair test `RAT-B-D01-RUNTIME_LEAN_CERTIFICATE_BINDING` passes every positive and substitution/mutation control.

### Stage 3 — implement complete type-metadata enforcement

- Give every source, derived, and output node an independently trusted expected signature.
- Enforce mathematical kind, semantic type, dimension equivalence class, canonical unit, exact shape/rank, ordered index spaces, representation tags, domain status/prerequisites, and operation-edge compatibility.
- Derive or resolve expected metadata from trusted contracts; candidate-declared metadata cannot authorize itself.
- Generate complete metadata mutation coverage from the graph/signature schema.

Exit gate: repair test `RAT-C-D02-VALUE-TYPE-METADATA-ENFORCEMENT` passes for all 207 baseline nodes and every applicable generated mutation.

### Stage 4 — run scoped regression and no-unrelated-change gates

- Run the preserved 228-test repair corpus and the complete calculator test closure.
- Re-run Python and independent Julia/Nemo exact computation.
- Re-run the versioned Lean checker and all 373 mandatory challenges.
- Produce the complete v1-to-amended scientific-payload equivalence ledger.
- Fail if an expected-answer/oracle dependency, hidden dynamic dependency, manual exclusion, or trusted historical-runner import appears.

Exit gate: all tests pass; 31/160/16/19/373 censuses close; all v1 scientific payload comparisons match; no unexpected challenge survivor exists.

### Stage 5 — freeze the amended exact evidence from a clean checkout

- Use only files present in the tested Git commit.
- Generate new profile, policy, request, computation, certificate, receipt, closure, and bundle identities.
- Perform two separate local replay processes against the newly frozen object.
- Preserve an explicit delta manifest showing that identity changes arise only from D-07/D-01/D-02 and their necessary tests/contracts.

Exit gate: two replays match the new bundle; the v1 bundle remains byte-identical; all promotion flags remain false.

### Stage 6 — conduct amendment-only non-author review

The reviewer must not have authored the repairs. The review must:

- inspect every changed file and its transitive trust impact;
- independently execute all three repair acceptance tests;
- inspect the certificate/context/receipt/bundle binding chain;
- inspect the generated 207-node signature and metadata-mutation ledgers;
- verify the dependency hash-domain implementation on Windows and Linux fixtures;
- mechanically compare all 31 sources, 160 derived applications, 16 roots, 19 operation semantics, and 373 challenge results with v1;
- confirm no unrelated scientific semantics or claim boundaries changed.

The reviewer need not repeat unaffected scientific interpretation from zero, but no census may be sampled or assumed unchanged without the complete equivalence ledger.

Exit gate: `SUPPORTED_WITHIN_STATED_COMPUTATIONAL_SCOPE` with D-01, D-02, and D-07 closed, or the lineage remains unqualified.

### Stage 7 — repeat Linux egress-denied qualification

- Start from a fresh checkout of the reviewed amended commit.
- Provision dependencies before isolation and capture Git-blob, canonical-text, filesystem, executable, and environment identities under explicit domains.
- Enter a fresh Linux network namespace; prove only loopback, no usable IPv4/IPv6 default route, and failed probes before execution.
- Execute all 207 nodes, Python/Julia/Lean routes, and 373 challenges.
- Prove isolation again after execution.
- Compare all scientific receipt fields and the scientific-payload equivalence ledger with the reviewed amended Windows evidence.

Exit gate: one separately preserved Linux `PASS`. A runner limitation is `INCONCLUSIVE`; a contract, custody, calculation, certificate, or comparison mismatch is `FAIL`. No connected fallback is permitted.

### Stage 8 — separate requalification decision

Only after Stages 0–7 pass may a separate authority record consider the bounded status `C03_RV_EXACT_COMPUTATION_REQUALIFIED`. Passing tests cannot self-promote the calculator profile.

Even a positive decision must preserve:

```text
scientific_promotion = false
product_v1_release = false
production_activation = false
```

It verifies the specified calculation and repair lineage. It does not establish that nature obeys SU(5), validate CCFT or a ToE, qualify the generic runner globally, or reopen production rows.

## Stop conditions

Stop amendment-only execution and open a broader versioned review if any repair changes a source meaning, operation physics, graph parentage, root value, challenge applicability, authority ceiling, or claim limitation. Stop with no qualification if any repair test, replay, non-author amendment review, or Linux gate fails.
