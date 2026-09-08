# VPC v6 amendment-only non-author review brief v2

## Amendment from v1

This brief supersedes v1 only by adding the completed Linux egress-denied
qualification evidence. It does not change the bounded review question,
scientific payload, acceptance standard, or reviewer-independence requirement.

The reviewer must not be an author of the v6 D-07, D-01, or D-02 repair
implementation or its qualification evidence. The reviewer must record
identity, affiliation or provider, relevant expertise, conflicts, review time,
and limits on independence. An AI reviewer must disclose shared model/provider
and prompt-lineage assumptions and must not be described as external expert
peer review.

## Frozen objects under review

- tested scientific/repair commit:
  `3307e35514cc76d63b6039b240c625defbb737d5`;
- Windows evidence-preservation commit:
  `e2f19a424f50e05164a24e67d949d1b2959894a4`;
- Linux qualification-lineage commit:
  `eec9da7374515b0235d2b3d4cabca0871e4387a5`;
- Linux result-preservation commit:
  `5a822913557dc97e478ae96c97028d583973220f`;
- amended Windows bundle:
  `b5482f305b6b45e8dc928640c7d7d837ec28d7b3a8009644a4cf304fccca4ccc`;
- Linux bundle:
  `0f64b6d71f536416755e599e2e3ad440d455a02b67a9927c0cdc2ecf5f505a13`;
- original v1 bundle, preserved unchanged:
  `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`;
- local repair acceptance result:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_REPAIR_ACCEPTANCE_RESULT_20260907_3307e355.json`;
- local 643-row equivalence result:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_PAYLOAD_EQUIVALENCE_RESULT_20260907_3307e355.json`;
- local 104-check execution result:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_EXECUTION_RUN_LOG_RESULT_20260907_3307e355.json`;
- changed-file manifest:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_CHANGED_FILE_MANIFEST_20260907_3307e355.json`;
- failed-attempt index:
  `VERIFIED_CALCULATOR_C03_RV_EXACT_V6_FAILED_ATTEMPT_INDEX_20260907_v2.json`;
- Linux PASS result:
  `VERIFIED_CALCULATOR_C03_RV_LINUX_EGRESS_DENIED_EXECUTION_RESULT_20260907_v6.json`;
- Linux PASS attempt record:
  `verified_calculator/c03_rv_exact_v6_linux_attempts/VPC_C03_RV_EXACT_V6_GITHUB_RUN_34167712902_ATTEMPT_1/attempt_record.json`;
- GitHub run:
  `https://github.com/bosticry90/ToE/actions/runs/34167712902`;
- GitHub artifact ID `10035287072`, archive SHA-256
  `5e3244fd2a0745b0f62e7a1d03f0f30630a92e045f2f62ba8974396fdf449f39`.

Paths are relative to `formal/docs/release/` unless otherwise stated. Review
the row-level and control-level evidence, not only summary counts.

## Bounded review question

Did v6 close D-01 and D-02, narrowly repair D-07 custody, and reproduce the
fixed scientific payload on Linux under egress-denied trusted execution without
introducing a new trust bypass or changing the previously supported C03/RV
scientific payload?

This is an amendment review of the prior exhaustive disposition
`SUPPORTED_WITH_REQUIRED_AMENDMENTS`. It does not restart already-supported
unaffected physics unless an amendment or dependency path touched it.

## Required determinations

The review record must separately answer, with cited paths and hashes:

1. **D-01:** Does the accepted Lean object bind the exact runtime certificate,
   request/profile/policy, sources, graph, roots/values, challenge evidence,
   type-signature set, receipt, and bundle edge? Do all 26 substitution and
   promotion attacks have the required disposition on both relevant routes?
2. **D-02:** Are all applicable `ValueTypeV1` axes enforced for all 207 nodes?
   Do all 1,656 numeric-value-preserving metadata mutations and all 160 edge
   mutations fail at the relevant node? Are type contracts independent of
   candidate claimed values?
3. **D-07:** Are Git-blob identity, canonical-text observations, and byte-exact
   binary checkout identity kept distinct? Do LF/CRLF equivalence and genuine
   content-mutation controls behave as declared? Does the Linux peer closure
   match the Windows path identities and domain-separated closure identity?
4. **Linux boundary:** Did provisioning finish before isolation; did trusted
   execution run with only loopback, no IPv4/IPv6 default route, and failed
   active probes before and after; and was connected fallback absent?
5. **Linux execution:** Did all 270 tests, the 207-node exact calculation,
   Python/Julia/Lean routes, 373 challenges, 160 corruption controls, two
   replays, and all three repair gates pass inside isolation?
6. **Payload preservation:** Do both 643-row ledgers contain every required row,
   evidence for every disposition, 643 matches, and zero missing, duplicate,
   unclassified, or non-allowlisted scientific changes?
7. **No unrelated semantic change:** Does the changed-file manifest accurately
   cover the transitive repair surface, with zero new records, roots, physics
   operations, expected-answer changes, authority promotions, or challenge
   instances? Do the three preserved Linux failures reveal any unaddressed
   bypass after the narrow procedure repairs?
8. **Claim boundary:** Do all evidence artifacts continue to withhold SU(5),
   CCFT, ToE, product-v1, production, and global-runner promotion?

## Required output matrix

Produce a machine-readable or tabular matrix with one row for each required
determination and underlying acceptance-control family. Every row must include:

- review row ID and reviewed defect/surface;
- exact evidence path and object/file hash;
- independent action taken: inspection, recomputation, mutation, or replay;
- observed result and limitation;
- disposition: `SUPPORTED`, `REQUIRED_AMENDMENT`, `REJECTED`, or
  `INCONCLUSIVE`;
- whether the issue affects D-01, D-02, D-07, payload equivalence, Linux
  execution, or only environment metadata.

Summary-only PASS marks without evidence locators are invalid. Material
omissions are `INCONCLUSIVE`, not assumed support.

## Overall dispositions

- `SUPPORTED`: every required amendment is supported, no new material bypass is
  found, scientific-payload preservation and the Linux bounded claim are
  supported, and claim limits hold.
- `SUPPORTED_WITH_REQUIRED_AMENDMENTS`: the bounded calculation remains
  supportable but at least one concrete material repair remains.
- `REJECTED`: a demonstrated defect invalidates the amended computational claim
  within the reviewed scope.
- `INCONCLUSIVE`: required evidence or reviewer capability is unavailable.

The review result must keep `scientific_promotion = false`,
`product_v1_release = false`, and `production_activation = false`. Any bounded
requalification or authority adjudication is a separate action and cannot be
performed automatically by the review artifact.
