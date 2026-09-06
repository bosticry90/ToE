# C03/RV Exact Computation — Linux Egress-Denied Acceptance Criteria v5

Status: `DEFINED_NOT_EXECUTED`

This version completes the runtime-custody repair following inconclusive v4 run `34010749703`. All unaffected v1 criteria, v2 `AC2-06`, v3 `AC3-07`/`AC3-24`, and v4 `AC4-10` remain mandatory.

## Expanded runtime-custody criterion

| ID | Criterion | Required evidence | Pass condition |
| --- | --- | --- | --- |
| AC5-10 | Every file needed before the final bundle is emitted is present in the tested Git object | The v4 25-file source corpus plus the three exact authority records named by `AUTHORITY_RECORDS`, recorded in the pre-isolation provisioning manifest and rechecked inside isolation | Exactly 28 unique runtime-custody files are in `GITHUB_SHA`; all declared/actual hashes and sizes match; the three authority hashes are `6156ec...d5c2`, `682476...d76`, and `614184...afd`; no untracked workspace state is required. |
| AC5-11 | Every file named by the frozen dependency closure is present in the tested Git object | The 73 unique path/hash pairs generated into the already-frozen dependency manifest, recorded before isolation and rechecked inside isolation | All 73 paths are in `GITHUB_SHA` and match their frozen raw SHA-256 values. The previously untracked `generic_runner/__init__.py` and `rv_source_derivation_v1.py` must match `d31ab6...db9` and `1bcdfa...302`; no local-only dependency is accepted. |

## v5 repair controls

| ID | Criterion | Pass condition |
| --- | --- | --- |
| RC5-01 | v1–v4 remain preserved | Four result records and raw archives verify and remain `INCONCLUSIVE`. |
| RC5-02 | Authority preservation is byte-exact | The three newly tracked records equal their pre-v4 expected SHA-256 values; their scientific labels/content are not regenerated or edited. |
| RC5-03 | Custody is established before and during isolation | Git-object membership is captured before isolation; all 28 bytes/hashes are rechecked before `qualify()` inside isolation. |
| RC5-04 | A complete PASS still requires post-execution isolation | Final network state and active probes must pass after qualification; reaching authority attachment is insufficient. |
| RC5-05 | The frozen computation is unchanged | Reference bundle and all scientific/computational identities remain fixed. |
| RC5-06 | No authority promotion follows from availability | Authority files are attachments about claims, not computation inputs; review status remains `SCIENTIFIC_REQUALIFICATION_NOT_EARNED`. |
| RC5-07 | The frozen dependency closure is executable from the tested commit | Its complete generated 73-file path set is checked for Git membership and byte identity before isolation and again before qualification. |

## v5 verdict

`PASS` requires one complete preserved result satisfying all inherited criteria, the 28-file runtime-custody gate, and the 73-file frozen dependency-closure custody gate. It remains a bounded Linux egress-denied computational reproduction only. It does not cure the non-author review’s D-01/D-02 defects and cannot release or scientifically promote anything.

```text
scientific_promotion = false
product_v1_release = false
production_activation = false
```
