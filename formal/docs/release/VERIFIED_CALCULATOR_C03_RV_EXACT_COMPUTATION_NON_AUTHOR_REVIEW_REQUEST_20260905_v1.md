# C03/RV Exact Computation — Non-Author Review Request

Status: `PENDING_NON_AUTHOR_REVIEW`

This packet requests a scoped independent scientific/computational review of the pre-release exact C03/RV calculator milestone. It is not a request to validate SU(5), CCFT, the ToE, product v1, or production activation.

## Evidence under review

- Computation ID: `2b8ab72bd24775bfc8914e85546484f244dddc9cb5bd43dc116db0aacf2f4e8a`
- Candidate hash: `fe0c6fa2133a7a9ed8bb94df3a91265e91d9db1a16206b487895a3c7e4353966`
- Physics-profile hash: `e131c6f94014082b8dd78bb680f1acdcf76e924b0cbe8fb62eafdda5af860617`
- Verification-policy hash: `ecda89e1e6b47db2f2ec8057656cd7d622944c0202eda58ab0cd907e48c2711b`
- Verification-receipt hash: `68f7e4c7f23c264da19e53e5cf24db1fcf8ae61c79a58848cc2f4e647045028f`
- Frozen-bundle hash: `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`
- Milestone hash: `bf001d80e2ad9c87f45f801f5fe5fe051731799d70c5d3c62955f2c7ed61a7e2`

Primary artifacts:

- `formal/docs/release/verified_calculator/c03_rv_exact/93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f.json`
- `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_COMPUTATIONAL_MILESTONE_20260905_v1.json`
- `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_POLICY_FREEZE_20260905_v1.json`
- `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_SOURCE_MATERIAL_CONTRACT_20260905_v1.json`

## Requested review questions

1. Do the 19 trusted physics operations faithfully encode the intended C03/RV transformations without importing historical expected-answer logic into the trusted package?
2. Are all 160 derived nodes materially recomputed from the 31 hash-bound sources, rather than authorized by preserved transcript values?
3. Does the Julia/Nemo route independently reconstruct all 16 authoritative roots without consuming Python intermediates or comparison-answer receipts?
4. Does the Lean checker consume and bind the actual runtime certificate strongly enough for the claimed exact structural guarantees?
5. Does the 373-result mandatory challenge execution cover every accepted falsifier in the frozen registry, with correct per-root applicability and zero unexpected survivors?
6. Are the claim ledger and authority attachment faithful to existing claim-by-claim authority, while keeping calculator-profile requalification unearned?
7. Are there any common-mode assumptions, source semantics, operation definitions, or certificate gaps that make `VERIFIED_EXACT` too strong for any root?

## Required reviewer disposition

The reviewer should return one of:

- `SUPPORTED_WITHIN_STATED_COMPUTATIONAL_SCOPE`
- `SUPPORTED_WITH_REQUIRED_AMENDMENTS`
- `NOT_SUPPORTED`

The result should identify the reviewer, establish non-authorship of the implementation/evidence, list every artifact and hash actually inspected, answer each review question, enumerate required amendments or residual limitations, and state explicitly:

```text
scientific_promotion = false
product_v1_release = false
production_activation = false
```

Until a genuine non-author result is received and hash-bound, the authoritative review state remains `SCIENTIFIC_REQUALIFICATION_NOT_EARNED`.
