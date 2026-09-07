# VPC v6 Linux egress-denied qualification run procedure v2

## Amendment from v1

This procedure supersedes v1 after GitHub run `34162706535` exposed two static
postcondition errors. V1 contained a mistyped graph hash even though the Linux
graph matched the preserved Windows bundle. It also demanded equality of the
complete verification-receipt hash even though environment identity is an
explicit receipt field permitted to differ across platforms. The scientific
target, tested commit, calculator code, sources, operation vocabulary, roots,
and expected answers are unchanged.

## Purpose and fixed target

This procedure tests the amended C03/RV exact scientific payload at Git commit
`3307e35514cc76d63b6039b240c625defbb737d5`. It compares the Linux result with
the preserved Windows amended bundle
`b5482f305b6b45e8dc928640c7d7d837ec28d7b3a8009644a4cf304fccca4ccc`.
It does not regenerate a more convenient reference target.

The executable workflow is
`.github/workflows/verified-calculator-v6-linux-egress-denied.yml`. The trusted
in-namespace driver is
`formal/tooling/scientific_compute/run_vpc_v6_linux_egress_denied.sh`.

## Boundary being tested

The claim is **egress-denied/offline trusted execution after environment
provisioning**. Dependency installation, Julia package instantiation, and Lean
build/cache acquisition occur before isolation and may use the network. They
must be recorded as provisioning, not described as offline construction.

The workflow then enters a fresh Linux network namespace. The namespace must:

- expose only loopback;
- have no IPv4 default route;
- have no IPv6 default route;
- reject active IPv4 and IPv6 TCP egress probes before trusted execution; and
- retain the same boundary and reject the probes again after execution.

If `unshare`, namespace creation, route inspection, or an active probe is
unavailable or ambiguous, the attempt is not a PASS. The workflow must not fall
back to ordinary connected execution. This is resource and egress confinement,
not a hostile-code sandbox.

## Ordered execution

1. Check out the qualification-lineage commit with full Git history.
2. Create a detached clean worktree at exactly `3307e355...737d5`.
3. Confirm the Windows bundle and 643-row seed ledger are present.
4. Provision pinned Python and Julia dependencies and build both Lean checkers.
5. Record dependency/artifact hashes, tool locations, tested commit, workflow
   identity, and the fact that provisioning preceded isolation.
6. Enter the fresh network namespace and record the isolation start time.
7. Record interface and IPv4/IPv6 route state and run both active probes.
8. Run the generated eight-root, 270-test calculator closure.
9. Run all 207 nodes, 19 operations, 16 roots, Python/Julia/Lean routes, and 373
   mandatory challenges through the v6 qualification entry point.
10. Require the frozen computation, graph, runtime-certificate, Lean-envelope,
    and dependency-closure identifiers. Record, but do not require equality of,
    the environment-bearing complete receipt and bundle hashes.
11. Replay the Linux bundle in two separate Python processes.
12. Extract the Linux dependency closure and run D-07/D-01/D-02 acceptance with
    it as the peer closure; all three gates must PASS.
13. Compare the Windows and Linux scientific projections over all 643 rows;
    require 643 matches and no unclassified or non-allowlisted mismatch.
14. Repeat the interface, route, and active-probe checks.
15. Seal and upload every available artifact whether the attempt passes, fails,
    or remains inconclusive.

## Acceptance criteria

A Linux PASS requires all ordered stages above to complete, including:

- exact tested commit `3307e355...737d5`;
- dependency closure `a01b60485d9b9fcdd3b7307af16204d735abf1ee8ef9cff9177b77fc6773d058`;
- computation `20a479ef428a9f079b7ea0c3b5506689383e26d2242579180777489818bbaeb8`;
- graph `ddf90176934cb018775ef7bb78ce8f5516fce40afbe7b4ed491e6116f4b46801`;
- runtime certificate `401d6aa6f502c751113931975d222f261d59849897b7e24e9e504404dfa88502`;
- Lean envelope `ad7aef9e7039ce0412c782368c3c6c1d2a678ead68c7c1e4c3be26ebd2d1ca4c`;
- a receipt whose 643-row scientific projection matches the Windows receipt;
- 270 passing tests, two matching replays, D-07/D-01/D-02 PASS, and 643/643
  Windows/Linux scientific matches; and
- `scientific_promotion`, `product_v1_release`, and `production_activation`
  remaining false.

Environment metadata, the complete receipt hash, and the Linux bundle's overall
content address may differ. Exact scientific values, graph evidence, challenge
outcomes, certificate commitments, and non-promotion state may not. The Windows
receipt hash `200720b0...ed9e` is retained as custody evidence, not imposed as a
cross-platform equality requirement.

## Disposition

The workflow preserves the actual evidence and terminal stage for PASS, FAIL, or
INCONCLUSIVE outcomes. A Linux PASS does not perform authority adjudication and
does not substitute for the amendment-only non-author review.
