# C03/RV Exact Computation — Linux Egress-Denied Acceptance Criteria v3

Status: `DEFINED_NOT_EXECUTED`

This is the versioned route-observation repair following the inconclusive v2 attempt recorded in `VERIFIED_CALCULATOR_C03_RV_LINUX_EGRESS_DENIED_EXECUTION_RESULT_20260905_v2.json`. It changes no physics, exact graph, source, challenge, certificate, frozen bundle, or authority contract.

All v1 acceptance criteria remain mandatory except AC-06 and AC-07. AC-06 remains superseded by AC2-06 from v2. AC-07 is superseded below because an explicit `unreachable`, `blackhole`, `prohibit`, or `throw` default route is a non-forwarding rejection rule rather than usable egress. The iproute2 `ip-route(8)` semantics define `unicast` as a real path, while those four route types discard traffic or terminate lookup without furnishing a path.

## Superseding route and evidence criteria

| ID | Criterion | Required evidence | Pass condition |
| --- | --- | --- | --- |
| AC3-07 | No usable forwarding default route exists | Canonical JSON output from local, pre-hashed iproute2 invocations `ip -j -4 route show default` and `ip -j -6 route show default`, before and after trusted execution; raw `/proc/net/route` and `/proc/net/ipv6_route` retained diagnostically | No returned default route has a forwarding type. A route without an explicit type is conservatively treated as `unicast` and fails. Only explicit `unreachable`, `blackhole`, `prohibit`, or `throw` types are non-forwarding. Unknown or malformed rows fail closed. |
| AC3-24 | Initial evidence survives an early assertion failure | `initial_network_state.json` is written atomically before the first isolation assertion; `final_network_state.json` is written before final assertions when execution reaches that phase | The artifact contains the applicable raw state even when a gate fails, allowing the disposition to be independently reviewed rather than inferred from a traceback. |

## v3 repair controls

| ID | Criterion | Pass condition |
| --- | --- | --- |
| RC3-01 | Both earlier attempts are preserved | v1 run `34007693980` and v2 run `34008583231`, their result records, raw archives, hashes, and `INCONCLUSIVE` dispositions remain recorded. |
| RC3-02 | The scientific target is unchanged | The frozen bundle remains `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`; all exact computation/profile/policy/candidate/certificate/closure identities remain unchanged. |
| RC3-03 | Route classification is fail closed | Missing iproute2, nonzero query exit, invalid JSON, non-list results, missing/unknown route type, or any forwarding default route fails the attempt. |
| RC3-04 | Non-forwarding sentinels do not substitute for active evidence | Loopback-only dual interface censuses and all four active probes before/after remain mandatory. A permitted reject route cannot by itself produce a PASS. |
| RC3-05 | iproute2 is part of the provisioned evidence | The exact `ip` executable path and SHA-256 are captured before isolation and the isolated driver uses that same hash-bound executable. |
| RC3-06 | Result vocabulary is versioned | Attempt, provisioning, result, failure, workflow-disposition, and test objects identify v3 and link the preserved v2 outcome. |

## v3 verdict

`PASS` requires every unaffected AC-01 through AC-23 criterion from v1, AC2-06, AC3-07, AC3-24, and RC3-01 through RC3-06 in one preserved run. `FAIL`, `INCONCLUSIVE`, and `NOT_RUN` retain their v1 meanings. A successful v3 run earns only bounded Linux egress-denied computational evidence and cannot retroactively convert either earlier attempt into a pass.

```text
scientific_promotion = false
product_v1_release = false
production_activation = false
```
