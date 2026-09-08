# C03/RV Exact Computation — Linux Egress-Denied Acceptance Criteria

Status: `DEFINED_NOT_EXECUTED`

These criteria govern the post-milestone Linux qualification of the already frozen exact C03/RV computation. They define what a future result must demonstrate; they do not record a Linux result or change any frozen computation, policy, profile, candidate, receipt, certificate, source, or authority state.

The tested reference is the content-addressed bundle:

```text
formal/docs/release/verified_calculator/c03_rv_exact/93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f.json
```

The qualification boundary is deliberately:

```text
environment provisioning -> provisioning manifest freeze -> kernel network isolation -> trusted execution
```

Therefore a passing result establishes egress-denied/offline **calculation and verification**, not offline environment construction and not a general hostile-code sandbox.

## Result dispositions

| Disposition | Meaning |
| --- | --- |
| `PASS` | Every mandatory criterion below passed in one CI attempt and the complete result artifact was preserved. |
| `FAIL` | The isolated execution completed far enough to establish that one or more scientific, reproducibility, identity, or isolation criteria failed. No qualification is earned. |
| `INCONCLUSIVE` | The required boundary could not be established or the evidence is incomplete—for example `unshare` is unavailable, provisioning/build fails, a required artifact is missing, or the runner terminates before the relevant assertion can be observed. No qualification is earned. |
| `NOT_RUN` | No actual attempt has been executed. This is the current state. |

The workflow must fail closed. It may never replace unavailable namespace isolation with an ordinary connected run. A retry is a distinct attempt; it does not overwrite, reinterpret, or erase prior failed/inconclusive evidence.

## Mandatory acceptance criteria

| ID | Criterion | Required evidence | Pass condition |
| --- | --- | --- | --- |
| AC-01 | Frozen target identity | Path plus recomputed hashes for bundle, computation, candidate, profile, policy, graph, runtime certificate, and dependency closure | Every identity equals the declared frozen reference before scientific comparison begins. |
| AC-02 | Explicit provisioning/execution separation | Ordered UTC phase timestamps and phase labels | Dependency installation and Lean/Julia preparation finish before the isolation observation; no provisioning action occurs after isolation. |
| AC-03 | Provisioned dependency identities are frozen | Canonical provisioning manifest and raw SHA-256 containing the Git commit, runner image/architecture/OS, `requirements.ci.lock`, Julia `Project.toml`/`Manifest.toml`, Lean toolchain/lake files, Python/Julia/Lean-checker executable hashes, and complete sorted `pip freeze --all` | The manifest self-hash and raw SHA-256 verify, every declared path exists, and it is passed unchanged into the isolated process. |
| AC-04 | Kernel-enforced boundary exists | Successful `unshare --net --fork --pid --mount-proc` entry and namespace marker | The qualification driver and all descendants run inside a new Linux network namespace. Namespace creation failure yields `INCONCLUSIVE`, never a connected fallback. |
| AC-05 | Isolation covers the trusted process tree | Workflow command boundary plus process inheritance | Python source resolution/verifier, Julia/Nemo, Lean checker, challenges, freeze, and replay are launched only after entering the namespace and inherit it. |
| AC-06 | Only loopback is exposed | `/sys/class/net` snapshot before and after trusted execution | The sorted interface set is exactly `['lo']` both times. |
| AC-07 | No default route exists | `/proc/net/route` and `/proc/net/ipv6_route` snapshots before and after | There is no IPv4 or IPv6 default route at either observation. |
| AC-08 | Active egress fails for network reasons | At least two numeric-address IPv4 TCP probes to distinct public destinations, before and after execution, with errno names/codes | Every probe returns `ENETUNREACH`, `EHOSTUNREACH`, or `EADDRNOTAVAIL`; none connects, times out ambiguously, or fails only at DNS. |
| AC-09 | Isolation brackets the calculation | UTC timestamps for provisioning capture, isolation observation, qualification start/completion, and post-qualification isolation observation | Timestamps are monotonic in that order and both network-state observations satisfy AC-06 through AC-08. |
| AC-10 | Source and software closure is self-contained | Frozen dependency manifest and source-evidence bindings; generated closure identity | Closure hash is `5f08deda84148b2ac4249de4b44b914fd27c6274a127762017d614d5282cd204`, with 54 Python files, 5 Julia files, 4 Lean files, 9 fixed artifacts, zero unresolved dependencies, and zero manual exclusions. |
| AC-11 | Full exact graph executes | Linux candidate graph and evaluator evidence | Exactly 31 source, 160 derived, and 16 output nodes (`207` total) are parsed, resolved, and evaluated under the frozen profile/policy. |
| AC-12 | Trusted Python exact verification succeeds | Per-node and per-root Python receipts | Every ancestor is recomputed and all 16 roots obtain exact canonical values without an expected-answer input. |
| AC-13 | Independent Julia/Nemo verification succeeds | Julia process receipt and per-root receipt hashes | Julia/Nemo independently reconstructs all 16 roots from frozen source-bound inputs and matches canonical field/value representations. |
| AC-14 | Lean checks actual runtime evidence | Runtime certificate, external certificate-file hash, checker invocation/result, and per-root certificate binding | Lean accepts the certificate emitted by this execution and bound to the actual contract, source, graph, and output hashes. |
| AC-15 | Mandatory challenge census closes | Every challenge packet/result and per-root coverage | All 373 frozen mandatory instances pass with correct affected roots and baseline-derived descendant confinement. |
| AC-16 | Intermediate corruption census closes | All `ALL_DERIVED_INTERMEDIATE_CORRUPTION` results | All 160 derived-node corruptions are rejected and unexpected survivors are exactly `[]`. |
| AC-17 | Linux evidence replays | Linux frozen bundle plus structural replay result | The generated Linux bundle is internally content-addressed, its filename/hash agree, and replay status is `MATCHED`. |
| AC-18 | Scientific payload matches Windows field by field | Machine-readable comparison for every verification-receipt field except `environment`, plus explicit identifier comparisons | Field sets are identical and every non-environment field comparison is `true`, including all exact outputs, source evidence, challenges, claim ledger, statuses, and certificate bindings. |
| AC-19 | Cross-platform distinction is genuine and bounded | Windows and Linux environment records | Platform metadata differs as expected; only environment metadata, the induced receipt hash, and outer Linux bundle hash may differ. No scientific mismatch is waived as a platform difference. |
| AC-20 | Result evidence is tamper-evident and complete | Canonical result object, result hash, Git commit, workflow/run identity, provisioning manifest hash, logs, exit code, Linux bundle, and uploaded artifact identity | All declared hashes verify and the retained artifact is sufficient to reproduce the PASS/FAIL decision without relying on transient console output. |
| AC-21 | Qualification remains non-promotional | Result object and all summary surfaces | `scientific_promotion=false`, `product_v1_release=false`, and `production_activation=false`. Route C, rows 77–96, global runner authority, SU(5), CCFT, and ToE statuses are unchanged. |
| AC-22 | Failed and inconclusive attempts are preserved | Artifact upload configured with `if: always()`, stderr hash/log, exit-code record, and failure record when no PASS result exists | Every attempt retains the evidence that exists. Absence of a PASS result cannot be reported as a pass. |
| AC-23 | The scope statement remains exact | Result report and any downstream summary | The claim is “Linux egress-denied/offline trusted calculation and verification after provisioned environment construction,” never “offline build,” “air-gapped supply chain,” or “secure arbitrary-code sandbox.” |

## Exact cross-platform comparison surface

The result must expose comparisons rather than only a single aggregate boolean. The following must match exactly:

- computation, candidate, profile, policy, graph, runtime-certificate, and dependency-closure identities;
- the complete request and candidate scientific content;
- all 31 resolved source-evidence bindings;
- all recomputed node and 16 canonical root values;
- every per-root verification class and Python/Julia/Lean evidence binding;
- all 373 challenge results and per-root challenge coverage;
- all 16 claim-ledger entries, their limitations, and `does_not_claim` fields;
- execution, replay, scientific-promotion, product-release, and production-activation fields.

Only the receipt `environment` object may be removed before equality comparison. The Windows and Linux environment objects, their resulting receipt hashes, and outer bundle hashes must be reported separately, not hidden or normalized into artificial equality.

## Verdict algorithm

1. Verify artifact integrity and classify whether a complete attempt exists.
2. If the namespace boundary was not entered or required evidence is absent, record `INCONCLUSIVE`.
3. If the boundary was entered but any mandatory criterion is false, record `FAIL`.
4. Record `PASS` only if AC-01 through AC-23 are all supported by the same preserved attempt.
5. Have a reviewer sign the criterion-by-criterion result; CI success alone is execution evidence, not reviewed acceptance.
6. Preserve the result under a new content address. Do not alter the frozen Windows bundle or exact-profile milestone.

Even a reviewed `PASS` earns only the bounded Linux/offline computational qualification evidence. Scientific-profile requalification remains a separate non-author decision, and product v1 remains gated on every other defined subsystem.
