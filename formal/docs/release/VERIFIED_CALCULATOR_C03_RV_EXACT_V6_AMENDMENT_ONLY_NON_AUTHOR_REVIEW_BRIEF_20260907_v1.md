# VPC v6 amendment-only non-author review brief

## Review identity and independence

This is a request for a genuine post-execution amendment review. The reviewer
must not be an author of the v6 D-07, D-01, or D-02 repair implementation or its
qualification evidence. The reviewer must record name/agent identity,
affiliation or provider, review time, relevant expertise, conflicts, and limits
on independence. An AI reviewer must explicitly disclose shared model/provider
or prompt-lineage assumptions and must not be described as external expert peer
review.

The repair author may prepare this brief and answer factual questions but may
not issue the non-author disposition.

## Frozen objects under review

- tested scientific/repair commit:
  `3307e35514cc76d63b6039b240c625defbb737d5`;
- evidence-preservation commit:
  `e2f19a424f50e05164a24e67d949d1b2959894a4`;
- amended Windows bundle:
  `b5482f305b6b45e8dc928640c7d7d837ec28d7b3a8009644a4cf304fccca4ccc`;
- original bundle preserved unchanged:
  `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`;
- local repair acceptance result:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_REPAIR_ACCEPTANCE_RESULT_20260907_3307e355.json`;
- 643-row equivalence result:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_PAYLOAD_EQUIVALENCE_RESULT_20260907_3307e355.json`;
- 104-check execution result:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_EXECUTION_RUN_LOG_RESULT_20260907_3307e355.json`;
- changed-file manifest:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_CHANGED_FILE_MANIFEST_20260907_3307e355.json`;
- failed-attempt index:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_FAILED_ATTEMPT_INDEX_20260907_v2.json`.

Paths are relative to `formal/docs/release/` unless otherwise stated. Review the
actual row-level and control-level evidence, not only the summary counts.

## Bounded review question

Did v6 close D-01 and D-02 and narrowly repair D-07 custody without introducing
a new trust bypass or changing the previously supported C03/RV scientific
payload?

This is an amendment review of a prior exhaustive disposition of
`SUPPORTED_WITH_REQUIRED_AMENDMENTS`. It does not restart already-supported
unaffected physics unless the amendments or their dependency paths touched it.

## Required determinations

The review record must separately answer, with cited object paths and hashes:

1. **D-01:** Does the accepted Lean object bind the exact runtime certificate,
   request/profile/policy, sources, graph, roots/values, challenge evidence,
   type-signature set, receipt, and bundle edge? Do all 26 substitution and
   promotion attacks have the required disposition?
2. **D-02:** Are all applicable `ValueTypeV1` axes enforced for all 207 nodes?
   Do all 1,656 numeric-value-preserving metadata mutations and all 160 edge
   mutations fail at the relevant node? Are the type contracts independent of
   candidate claimed values?
3. **D-07:** Are Git-blob identity, canonical-text observations, and byte-exact
   binary checkout identity kept distinct? Do LF/CRLF equivalence and real
   content-mutation controls behave as declared? Did the additional source-byte
   repair narrow itself to custody rather than physics?
4. **Payload preservation:** Does the 643-row ledger contain every required row,
   evidence for every disposition, 643 matches, and zero missing, duplicate,
   unclassified, or non-allowlisted scientific changes?
5. **No unrelated semantic change:** Does the changed-file manifest accurately
   cover the transitive repair surface, with zero new records, roots, physics
   operations, expected-answer changes, authority promotions, or challenge
   instances? Did either preserved failed attempt reveal an unaddressed bypass?
6. **Claim boundary:** Do the bundle, receipts, ledger, procedure, and review
   artifacts continue to withhold SU(5), CCFT, ToE, product-v1, production, and
   global-runner promotion?

If the Linux result exists when review is performed, assess its custody and
cross-platform evidence as a separate section. A Linux PASS cannot compensate
for a D-01, D-02, payload, or claim-boundary defect. If Linux has not run, mark
that section `NOT_REVIEWED` without converting it into review support.

## Required output matrix

The reviewer must produce a machine-readable or tabular matrix with one row for
each required determination and each underlying acceptance-control family. Each
row must contain:

- review row ID and reviewed defect/surface;
- exact evidence path and object/file hash;
- independent action taken (inspection, recomputation, mutation, or replay);
- observed result and limitation;
- disposition: `SUPPORTED`, `REQUIRED_AMENDMENT`, `REJECTED`, or `INCONCLUSIVE`;
- whether the issue affects D-01, D-02, D-07, payload equivalence, or only
  environment metadata.

Summary-only `PASS` marks without evidence locators are invalid. Material
omissions are `INCONCLUSIVE`, not assumed support.

## Overall dispositions

- `SUPPORTED`: every required amendment is supported, no new material bypass is
  found, scientific payload preservation is supported, and claim limits hold.
- `SUPPORTED_WITH_REQUIRED_AMENDMENTS`: the bounded calculation remains
  supportable but at least one concrete material repair remains.
- `REJECTED`: a demonstrated defect invalidates the amended computational claim
  within the reviewed scope.
- `INCONCLUSIVE`: required evidence or reviewer capability is unavailable.

The review result must keep `scientific_promotion = false`,
`product_v1_release = false`, and `production_activation = false`. Any later
authority adjudication is a separate action and cannot be performed by this
review artifact automatically.
