# C03/RV Exact Computation — Linux Egress-Denied Acceptance Criteria v2

Status: `DEFINED_NOT_EXECUTED`

This is the versioned measurement repair following the inconclusive v1 attempt recorded in `VERIFIED_CALCULATOR_C03_RV_LINUX_EGRESS_DENIED_EXECUTION_RESULT_20260905_v1.json`. It changes no physics, exact graph, source, challenge, certificate, frozen bundle, or authority contract.

All v1 acceptance criteria remain mandatory except AC-06, whose `/sys/class/net` gate is superseded below. The v1 attempt demonstrated that an inherited sysfs mount can expose host interface names even after `unshare --net`; therefore `/sys/class/net` is diagnostic only and cannot establish the process network namespace's interface set.

## Superseding interface criterion

| ID | Criterion | Required evidence | Pass condition |
| --- | --- | --- | --- |
| AC2-06 | The process network namespace exposes only loopback according to namespace-aware interfaces | Independent snapshots from Python `socket.if_nameindex()` and parsed `/proc/net/dev`, taken before and after trusted execution; `/sys/class/net` retained separately as non-gating diagnostic context | Both namespace-aware mechanisms report exactly `['lo']` at both observations. They agree with one another. The sysfs diagnostic cannot override or promote this result. |

## v2 repair controls

| ID | Criterion | Pass condition |
| --- | --- | --- |
| RC-01 | The v1 result is preserved | Run `34007693980`, artifact `9981631172`, archive SHA-256 `d62713d8542680d43a828a5956c9fd466fc55e024ca61870b85a1ed23ce41bdb`, and the `INCONCLUSIVE` disposition remain recorded. |
| RC-02 | Only the measurement defect is repaired | The frozen bundle remains `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`; all exact computation/profile/policy/candidate/certificate/closure identities remain unchanged. |
| RC-03 | No weakened network gate is introduced | IPv4/IPv6 no-default-route checks and both active network-unreachable probes still pass before and after qualification. |
| RC-04 | The namespace-aware census is fail-closed | Missing, malformed, disagreeing, or non-loopback `socket.if_nameindex()` or `/proc/net/dev` evidence fails the attempt. |
| RC-05 | Result vocabulary is versioned | The execution result and provisioning/attempt/failure records identify v2 and link the superseded v1 result. |

## v2 verdict

`PASS` requires every unaffected AC-01 through AC-23 criterion from v1, AC2-06, and RC-01 through RC-05 in one preserved run. `FAIL`, `INCONCLUSIVE`, and `NOT_RUN` retain their v1 meanings. A successful v2 run earns only bounded Linux egress-denied computational evidence and cannot retroactively convert the v1 attempt into a pass.

```text
scientific_promotion = false
product_v1_release = false
production_activation = false
```
