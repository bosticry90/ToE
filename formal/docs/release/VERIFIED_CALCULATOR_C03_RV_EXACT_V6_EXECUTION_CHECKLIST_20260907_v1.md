# C03/RV Exact Computation — v6 Amended Qualification Execution Checklist

Status: `DRAFT_EXECUTION_CHECKLIST__NOT_EXECUTED`

This checklist executes the already-frozen v6 repair contracts. It does not change their acceptance criteria and is not evidence that any repair, review, Linux qualification, scientific promotion, product release, or production activation has succeeded.

Record results in a new hash-bound execution-result artifact. Do not edit this checklist into a result, overwrite a failed attempt, or modify the frozen v1 packet.

## Frozen control objects

- [ ] Repair lineage: `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_REPAIR_LINEAGE_20260907_v6.json`, hash `0cb60a86a275701cac8de23383e113f21ddbdf28b5fe852515c439bf04803b17`.
- [ ] Repair gates: `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_REPAIR_ACCEPTANCE_TESTS_20260907_v1.json`, hash `009590b4923f73956139916b2d43b4b1171b5a32f8125705d4666b90cc5542e9`.
- [ ] Payload-equivalence test: `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_PAYLOAD_EQUIVALENCE_TEST_20260907_v1.json`, hash `feab4e8cb67a7b51242af1cc87f68bfdb22cbf79c3c2017536f573243ba39d17`.
- [ ] Ordered sequence: `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_AMENDED_REQUALIFICATION_SEQUENCE_20260907_v1.md`.
- [ ] Frozen v1 bundle: `formal/docs/release/verified_calculator/c03_rv_exact/93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f.json`; bundle ID `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`; raw file SHA-256 `7496caaa2f63915cf3adf5d81776ee3298decd204f745ae65e8a38b6c80b1bcf`.
- [ ] Non-author review result: `SUPPORTED_WITH_REQUIRED_AMENDMENTS`, hash `d415ae3d690b4bcf87d6222f8618371af2d1a28b0c624843f95b8649cb816b15`.
- [ ] Linux v5 result: `FAIL`, result-record hash `e4a7a5e961b9c60a9e29d4beabb3b5e4984a0456f835ae17dad7a8d265e7a48f`.

Any mismatch in these control objects stops execution. Preserve the mismatch as `FAIL`; do not repair the reference object in place.

## 0. Attempt identity, custody, and operator declaration

- [ ] Allocate a unique attempt ID before execution. Never reuse an attempt ID after `FAIL` or `INCONCLUSIVE`.
- [ ] Record operator identity, UTC start time, host/OS, repository URL, branch, parent commit, and exact tested commit.
- [ ] Record whether the operator authored D-07, D-01, or D-02. This operator declaration does not substitute for the later non-author review.
- [ ] Start implementation from the committed v6 contract checkpoint and preserve the pre-existing dirty-tree inventory separately.
- [ ] Before evidence generation, use a fresh clean checkout of the tested implementation commit. Record `git status`, tracked-file census, submodule state if any, and proof that no untracked file supplies a runtime dependency.
- [ ] Validate every JSON contract against its schema/bounded parser and verify every domain-separated self-hash.
- [ ] Recompute the frozen v1 raw file hash and validate its content-addressed bundle ID without modifying it.
- [ ] Create a new append-only attempt directory for stdout, stderr, commands, exit codes, timestamps, resource use, and intermediate receipts.
- [ ] Confirm no comparison oracle or expected-output table is accessible to trusted execution except the reference bundle supplied later to the independent payload comparator.

Exit gate: custody is complete and every control object matches. Otherwise record `FAIL` before repair execution.

## 1. Scope-lock implementation audit

- [ ] Generate a changed-file manifest and transitive trust-impact graph before implementation.
- [ ] Classify every intended change as exactly one of `D-07`, `D-01`, `D-02`, `REPAIR_TEST`, or `MECHANICAL_EVIDENCE_VERSIONING`.
- [ ] Confirm zero new physics records, authoritative roots, physics operations, expected answers, authority promotions, and mandatory scientific challenge instances.
- [ ] Confirm the seven-record set remains C03 plus RV01–RV06, with 31 sources, 160 derived nodes, 16 roots, 19 operations, 10 challenge specifications, and 373 challenge instances.
- [ ] Reject any historical-runner, candidate-producer, oracle, or acceptance-table import into the trusted package.
- [ ] Stop amendment-only execution if source meaning, operation physics, graph parentage, root value, challenge applicability, claim wording/limitation, or authority ceiling changes.

Exit gate: every changed file is in scope and no scientific-semantic delta is proposed.

## 2. D-07 execution — cross-platform dependency identity

Implement and run `RAT-A-D07-CROSS_PLATFORM_DEPENDENCY_IDENTITY` exactly as frozen.

### Positive controls

- [ ] `A-P01-GIT-BLOB-PRIMARY`: every tracked dependency identity comes from `tested_commit:path` Git-blob bytes and records commit, path, object ID, and `git_blob_sha256`.
- [ ] `A-P02-LF-CRLF-EQUIVALENCE`: LF, CRLF, and mixed-newline fixtures have equal `CANONICAL_TEXT_V1` identities and distinct observed filesystem hashes where bytes differ.
- [ ] `A-P03-CLEAN-CHECKOUT-CLOSURE`: clean Windows and Linux checkouts produce the same path set, Git object IDs, Git-blob hashes, canonical-text identities, and domain-separated closure identity.

### Negative controls

- [ ] `A-N01-GENUINE-CONTENT-MUTATION`: a physics-bearing token change alters canonical identity and is rejected.
- [ ] `A-N02-TRAILING-WHITESPACE-MUTATION`: non-newline whitespace change is rejected.
- [ ] `A-N03-FINAL-NEWLINE-MUTATION`: adding/removing the final newline is rejected.
- [ ] `A-N04-BOM`: a UTF-8 BOM is rejected, not stripped.
- [ ] `A-N05-BINARY-NEWLINE-LAUNDERING`: applying text normalization to a binary artifact is rejected.
- [ ] `A-N06-WORKTREE-ONLY-DEPENDENCY`: an input absent from the tested commit fails closure/custody before trusted execution.

- [ ] Recheck the three v5 mismatch paths—`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`—from Git blobs under the new domain rules.
- [ ] Record the generated closure rather than assuming the old 73-path total; explain every added path through the transitive generator.
- [ ] Confirm zero unresolved dependencies and zero manual exclusions.

Exit gate: every positive control passes, every negative control rejects for the intended reason, and the D-07 result is `PASS`.

## 3. D-01 execution — runtime/Lean certificate identity

Implement and run `RAT-B-D01-RUNTIME_LEAN_CERTIFICATE_BINDING` exactly as frozen.

### Positive controls

- [ ] `B-P01-ACTUAL-RUNTIME-EVIDENCE`: create the certificate/envelope from one fresh trusted execution; Lean parses it, recomputes its domain-separated identity, validates the independent expected context, and returns the computed identity used by the receipt/bundle edge.
- [ ] `B-P02-SEPARATE-REPLAY`: a separate process reproduces all scientific/contract commitments and the same computed certificate identity.

### Negative controls

- [ ] `B-N01-VALID-SUBSTITUTE-SAME-OUTPUT`: reject a valid same-output certificate from a different computation/candidate/graph/source/trace.
- [ ] `B-N02-CALLER-CHOSEN-HASH`: reject or ignore `00…00`, `ff…ff`, and arbitrary caller-selected accepted identities; Lean reports only its computed identity.
- [ ] `B-N03-CONTRACT-IDENTITY`: reject altered computation, request, candidate, profile, or policy identities.
- [ ] `B-N04-GRAPH-TRACE-SOURCE`: reject altered graph, ordered trace, or source identities.
- [ ] `B-N05-OUTPUT-ROOT-VALUE`: reject altered root bindings or canonical exact output-value hashes.
- [ ] `B-N06-INDEPENDENT-EVIDENCE`: reject altered Julia or mandatory-challenge evidence or prevent `VERIFIED_EXACT`.
- [ ] `B-N07-STATUS-OR-PROMOTION`: reject raised status ceilings and any scientific/product/production promotion.
- [ ] `B-N08-RECEIPT-BUNDLE-EDGE`: reject a valid certificate paired with a receipt or bundle that names another certificate.

- [ ] For every mutation, recompute valid transport/file hashes so the intended semantic binding—not stale outer bytes—causes rejection.
- [ ] Inspect the executable checker interface and confirm it has no authoritative caller-supplied accepted-certificate-hash argument.
- [ ] Record certificate/envelope, independent context, checker source/binary/dependency identity, Lean-computed identity, receipt edge, bundle edge, and stable rejection codes.

Exit gate: both positives pass, all eight negatives reject for the intended reason, and the D-01 result is `PASS`.

## 4. D-02 execution — exhaustive `ValueTypeV1` enforcement

Implement and run `RAT-C-D02-VALUE-TYPE-METADATA-ENFORCEMENT` exactly as frozen.

### Baseline controls

- [ ] `C-P01-COMPLETE-BASELINE`: independently resolve/infer the complete trusted signature for all 31 source, 160 derived, and 16 output nodes; record `207/207` passing signature receipts.
- [ ] `C-P02-VALID-NATURAL-UNIT-QUOTIENT`: accept one declared quotient-equivalent dimension and reject undeclared equivalence.

### Generated mutation controls

- [ ] `C-N01-MATHEMATICAL-KIND` for every applicable node.
- [ ] `C-N02-SEMANTIC-TYPE` for every applicable node.
- [ ] `C-N03-DIMENSION` for every applicable node.
- [ ] `C-N04-UNIT-CONVENTION` for every applicable node.
- [ ] `C-N05-SHAPE-RANK` for every applicable node.
- [ ] `C-N06-INDEX-SPACE` for every applicable node, including COLOR-to-NATIVE_E substitution.
- [ ] `C-N07-REPRESENTATION-TAG` for every applicable node, including the reviewed BMHV substitution.
- [ ] `C-N08-DOMAIN` for every applicable node.
- [ ] `C-N09-EDGE-COMPATIBILITY` for every operation edge where a locally plausible but incompatible parent signature can be generated.

- [ ] Generate the node/axis applicability census from the frozen graph and trusted signature schema; do not hand-select or sample mutations.
- [ ] Use another profile-valid value when available; otherwise retain a typed synthetic invalid/unknown control.
- [ ] Confirm every mutation rejects at the intended node with expected/observed signatures and a stable failure code.
- [ ] Confirm candidate-declared metadata never supplies the trusted expected signature used to validate itself.
- [ ] Confirm no metadata-invalid candidate receives a runtime certificate or `VERIFIED_EXACT` output.

Exit gate: all baseline controls pass, every applicable generated mutation rejects, the coverage generator cannot be manually narrowed, and the D-02 result is `PASS`.

## 5. Regression and pre-freeze scientific-payload equivalence

- [ ] Run the preserved 228-test repair corpus.
- [ ] Run the complete generated calculator test closure, including every new D-07/D-01/D-02 positive and negative control. Record actual counts; do not retain `260 passed` as a fixed expected total after adding tests.
- [ ] Build the versioned Lean checker and record its exact source, toolchain, dependency, and executable identities.
- [ ] Recompute all 207 nodes in trusted Python and all 16 authoritative roots independently in Julia/Nemo.
- [ ] Run all 373 mandatory challenge instances and the complete 160-derived-node corruption census; require zero unexpected survivors.
- [ ] Generate draft amended evidence from the clean candidate implementation without reading v1 expected answers during trusted execution.
- [ ] Run `PET-V6-C03-RV-SCIENTIFIC-PAYLOAD-EQUIVALENCE` against the draft evidence and frozen v1 bundle using the independent projection comparator.
- [ ] Require all comparison surfaces to close: 1 model/convention row, 31 sources, 160 derived applications, 19 operations, 16 roots, 10 challenge specs, 373 challenge instances/results, 16 claim-ledger rows, 16 authority rows, and 1 scope/non-promotion row.
- [ ] Require zero `MISMATCH`, `MISSING`, `DUPLICATE`, and `UNCLASSIFIED_DELTA` rows. Map every evidence-only difference to exactly one frozen allowed-delta class.
- [ ] Independently inspect the changed-file/transitive-impact manifest for oracle dependencies, hidden runtime dependencies, manual exclusions, and out-of-scope semantic changes.

Exit gate: the three repair gates and the preliminary payload-equivalence test all report `PASS`.

## 6. Clean evidence generation, replay, and authoritative equivalence result

- [ ] Commit the scoped repair implementation and tests before authoritative evidence generation.
- [ ] Start from a new clean checkout of that exact commit. Do not reuse a dirty development environment as canonical evidence.
- [ ] Generate new profile, policy, request, computation, candidate, graph, certificate, receipt, dependency-closure, and bundle identities. Record why each identity changed.
- [ ] Freeze the amended bundle to a new content-addressed path. Confirm the v1 bundle remains byte-identical.
- [ ] Replay the new frozen bundle in two separate local processes and require matching canonical exact results and matching new receipt/bundle identities where policy requires them.
- [ ] Run the payload-equivalence test again against the frozen amended bundle. This post-freeze result supersedes the preliminary result for review.
- [ ] Record a complete delta manifest proving every non-scientific identity/content change arises transitively from D-07, D-01, D-02, their tests, or necessary evidence versioning.
- [ ] Preserve all flags as `scientific_promotion = false`, `product_v1_release = false`, and `production_activation = false`.

Exit gate: two amended replays match, the authoritative payload-equivalence result is `PASS`, and the frozen v1 object is unchanged.

## 7. Amendment-only non-author review

- [ ] Freeze a review request that names the exact implementation commit, new bundle, three repair results, payload-equivalence result, changed-file manifest, and this checklist.
- [ ] Assign a reviewer who did not author the repairs; record conflicts and any AI/model/provider overlap.
- [ ] Have the reviewer independently execute all three repair gates and verify their raw evidence.
- [ ] Inspect every changed file and its transitive trust impact, not merely the reported test summary.
- [ ] Inspect the D-01 certificate/context/receipt/bundle chain and substitution controls.
- [ ] Inspect the D-02 207-node signature ledger and complete generated metadata-mutation census.
- [ ] Inspect the D-07 Git-blob/canonical-text implementation and Windows/Linux fixtures.
- [ ] Mechanically verify every payload-equivalence ledger row; do not resample the 31/160/19/16/10/373/16/16 surfaces.
- [ ] Confirm the review does not promote SU(5), CCFT, a ToE, the historical runner, other topology rows, product v1, or production activation.
- [ ] Require the exact disposition `SUPPORTED_WITHIN_STATED_COMPUTATIONAL_SCOPE`; any open material defect keeps requalification unearned.

Exit gate: one new immutable amendment-review result closes D-07, D-01, and D-02 and accepts the payload-equivalence evidence within the bounded computational scope.

## 8. Linux egress-denied rerun

- [ ] Create a new versioned Linux test contract and acceptance record for the amended commit; do not edit or relabel v5 `FAIL`.
- [ ] Provision dependencies before isolation and record all Git-blob, canonical-text, observed filesystem, executable, and environment identities.
- [ ] Enter a fresh Linux network namespace and prove only loopback interfaces, no usable IPv4/IPv6 forwarding default route, and failed active egress probes.
- [ ] Execute all 207 nodes, Python/Julia/Lean routes, three repair regression gates where platform-applicable, and all 373 mandatory challenges inside isolation.
- [ ] Re-prove network state and failed egress probes after execution.
- [ ] Run the payload-equivalence test between the Linux amended scientific payload, reviewed Windows amended payload, and frozen v1 reference. Environment metadata may differ only as explicitly allowed.
- [ ] Preserve `PASS`, `FAIL`, or `INCONCLUSIVE`; never fall back to connected execution after an isolation failure.

Exit gate: a new Linux result is `PASS` and all bounded cross-platform scientific comparisons match.

## 9. Separate bounded requalification decision

- [ ] Confirm checklist Sections 0–8 each have one hash-bound passing result and no superseding failed/unresolved attempt.
- [ ] Confirm the three repair gates, authoritative payload equivalence, amendment-only review, and Linux egress-denied result all pass.
- [ ] Confirm existing claim-by-claim scientific authority is unchanged and remains external to computation identity.
- [ ] Submit the evidence to a separate authority decision; the calculator and tests cannot promote themselves.
- [ ] If accepted, use only the bounded status vocabulary authorized for `C03_RV_EXACT_COMPUTATION_REQUALIFIED`.
- [ ] Retain `scientific_promotion = false`, `product_v1_release = false`, and `production_activation = false`.

## Failure and evidence-recording rule

At the first failed mandatory item:

1. stop the current qualification stage;
2. preserve commands, stdout/stderr, environment/custody facts, partial ledgers, and the exact failure;
3. issue a new immutable `FAIL` or `INCONCLUSIVE` attempt result;
4. leave v1, v5, v6 contracts, and prior review evidence unchanged;
5. open a narrowly versioned repair only for the demonstrated defect;
6. do not average, waive, relabel, or conceal the failure.

Completion of this checklist would qualify an evidence package for a separate bounded decision. The checklist itself cannot establish that SU(5) describes nature, validate CCFT or a Theory of Everything, release product v1, or activate production authority.
