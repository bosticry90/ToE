# C03/RV Exact Computation — Linux Egress-Denied Acceptance Criteria v4

Status: `DEFINED_NOT_EXECUTED`

This version repairs the source-custody failure exposed by preserved v3 run `34009722386`. It does not modify the frozen exact packet or reinterpret v1–v3.

All unaffected v1 criteria, v2 `AC2-06`, and v3 `AC3-07`/`AC3-24` remain mandatory.

## Source-custody criterion

| ID | Criterion | Required evidence | Pass condition |
| --- | --- | --- | --- |
| AC4-10 | The complete runtime source corpus is present in the tested Git object | A pre-isolation canonical manifest derived from the fixed normalization profile descriptor, containing the descriptor, normalization contract, parent allowlist, every declared allowed input, and the C03/RV material contract; for each path record the declared hash, actual raw SHA-256, byte size, and `git ls-tree` membership at `GITHUB_SHA` | Exactly 25 unique files exist; all 25 occur in the tested commit; every actual hash equals its frozen declaration; zero paths are missing, duplicated, outside the repository, or dependent on untracked workspace state. |

## v4 repair controls

| ID | Criterion | Pass condition |
| --- | --- | --- |
| RC4-01 | v1–v3 evidence remains immutable | All three result records and raw archives verify their declared hashes and retain `INCONCLUSIVE`. |
| RC4-02 | Added sources are preservation, not regeneration | The 24 newly tracked files match the hashes that predated v3; no source value or profile declaration changes. |
| RC4-03 | The custody manifest is checked twice | It is created before isolation and revalidated inside the namespace before `qualify()` begins. |
| RC4-04 | The clean-checkout property is tested directly | Source membership is resolved against `GITHUB_SHA`, not inferred from local file existence or a dirty-tree execution. |
| RC4-05 | The scientific object is unchanged | The reference bundle remains `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`, and every frozen computation/profile/policy/candidate/graph/certificate identifier remains unchanged. |
| RC4-06 | Result vocabulary is versioned | Test, attempt, provisioning, failure, result, and workflow-disposition objects identify v4 and link v3. |

## v4 verdict

`PASS` requires every inherited criterion plus AC4-10 and RC4-01 through RC4-06 in one preserved run. A missing/untracked/mismatched source is `INCONCLUSIVE` before graph execution; a later exact or comparison mismatch is `FAIL`. Neither outcome may be hidden by a connected fallback.

Even a reviewed PASS would establish only egress-denied Linux reproduction after online provisioning. It would not repair review defects D-01/D-02, scientifically requalify the profile, release product v1, activate production, or validate SU(5), CCFT, or a ToE.

```text
scientific_promotion = false
product_v1_release = false
production_activation = false
```
