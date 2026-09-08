# VPC v6 amendment-only non-author review result v1

## Disposition

**SUPPORTED**, within the frozen amendment-only computational scope.

The evidence supports that v6 closes D-01 and D-02, narrowly repairs D-07
custody, preserves the fixed C03/RV scientific payload, and reproduces it on
Linux under egress-denied trusted execution. I found no new material trust
bypass in the reviewed repair surface.

This review does **not** perform bounded-requalification or authority
adjudication. It keeps:

```text
scientific_promotion = false
product_v1_release = false
production_activation = false
```

## Reviewer disclosure

I am a same-provider OpenAI Codex AI reviewer operating as task
`/root/v6_amendment_review`. I did not author the D-07, D-01, or D-02 repairs
or their reviewed qualification evidence. I inherited prompt and repository
context from the wider Codex task lineage. I am not an external human expert,
an independent model provider, an experimental physicist, or an independent
peer-review venue. This is a non-author computational amendment review, not
external scientific peer review.

## Independent checks performed

From a detached clean worktree at
`3307e35514cc76d63b6039b240c625defbb737d5`, I:

- rebuilt `vpc_qualification_envelope_checker` and
  `vpc_certificate_checker` successfully (9 Lean jobs);
- independently reran the full repair-acceptance tool: D-07 PASS, D-01 PASS
  for all 26 controls, and D-02 PASS for 207 baselines, 1,656 metadata
  mutations, and 160 edge mutations;
- ran the focused v6 repair/execution-record tests: 12 passed in 54.90 s;
- independently evaluated the actual 207-node v2 candidate and obtained 207
  trusted signature receipts, 16 output bindings, graph hash
  `ddf90176934cb018775ef7bb78ce8f5516fce40afbe7b4ed491e6116f4b46801`,
  and runtime-certificate hash
  `401d6aa6f502c751113931975d222f261d59849897b7e24e9e504404dfa88502`;
- injected each of the eight `ValueTypeV1` metadata-axis mutations through the
  integrated verifier path while retaining the numeric value; all eight were
  rejected at the relevant trusted check;
- replayed the original v1, Windows v6, and Linux v6 bundles; all matched;
- inspected the preserved 104-check local run log (80 PASS, 1 INCONCLUSIVE,
  23 NOT_RUN) as the truthful pre-Linux checkpoint rather than retroactively
  rewriting it with later Linux or review evidence;
- regenerated both 643-row ledgers and mechanically checked row uniqueness,
  the exact PE00-PE09 census, every projection hash and evidence pair, and
  empty mismatch fields; both were 643/643 MATCH and row-identical to the
  preserved ledgers;
- independently verified the changed-file manifest exactly equals the 23-path
  Git delta from `97311c3c...` to `3307e355...`; no physics-operation
  implementation, record, root, expected answer, authority state, or
  challenge instance changed;
- downloaded GitHub artifact `10035287072`, reproduced archive hash
  `5e3244fd2a0745b0f62e7a1d03f0f30630a92e045f2f62ba8974396fdf449f39`,
  validated all 25 declared evidence files and all 27 artifact payload-file
  hashes, and inspected the network evidence and Linux execution outputs;
- reviewed the three prior Linux attempts and the narrow workflow/procedure
  changes that preceded the accepted PASS.

## Findings

### D-01

Supported. The Lean qualification envelope is connected to the actual runtime
certificate and commits to the request/profile/policy, sources, graph, trace,
roots and values, Julia result, challenge evidence, type signatures,
non-promotion state, receipt, and bundle edge. All 26 substitution and
promotion controls passed on their applicable routes. Windows and Linux v6
bundles both replayed successfully with the same computation, graph,
certificate, and Lean-envelope identities.

### D-02

Supported. The trusted 207-node signature registry is constructed independently
of candidate claimed values. All 1,656 value-preserving metadata mutations and
all 160 edge mutations were rejected. An additional integrated check confirmed
enforcement of mathematical kind, semantic type, physical dimension, unit
convention, shape, index spaces, representation tags, and domain.

### D-07

Supported. Git-blob identity is distinct from canonical-text observation and
byte-exact binary identity. LF/CRLF equivalence works only in the declared
canonical-text domain; BOM, invalid UTF-8, whitespace/final-newline differences,
binary mutations, and genuine content mutations remain visible. The Windows
and Linux stable path identities and domain-separated closure identity agree.

### Linux boundary and execution

Supported. GitHub run `34167712902` provisioned dependencies before isolation,
entered the network namespace successfully, exposed only loopback, had no IPv4
or IPv6 default route, and failed active IPv4/IPv6 probes with errno 101 before
and after execution. The before/after network records were byte-identical and
no connected fallback ran.

Inside isolation, 270/270 tests passed; the 207-node exact calculation,
Python/Julia/Lean routes, 373 mandatory challenges, 160/160 corruption
rejections, all three repair gates, and two separate replays completed. This is
egress-denied trusted execution after connected environment provisioning, not
offline environment construction or hostile-code sandboxing.

The three earlier Linux records remain informative and preserved: one was
inconclusive before runner allocation because of workflow validation; one
failed after successful trusted execution because the comparison used a
mistyped graph identity and overstrict full-receipt equality; and one failed
because a copied bundle lost its content-addressed filename, which replay
correctly rejected. I found no unaddressed scientific bypass in the narrow
procedural repairs leading to the PASS.

### Payload and claims

Supported. Both the original-v1-to-Windows-v6 and Windows-v6-to-Linux ledgers
contain 643 unique, fully evidenced matches with zero missing, duplicate,
unclassified, or non-allowlisted scientific change. All 16 claim-ledger entries
remain bounded to computation and explicitly withhold SU(5), CCFT, ToE, and
global-runner validation.

## Scope boundary

This result supports the amended exact computation and its specified Linux
reproduction. It does not establish that SU(5) describes nature, validate CCFT
or a Theory of Everything, qualify the historical runner globally, release
product v1, activate production, prove offline dependency installation, or
constitute external human expert review.

The complete 18-row evidence and disposition matrix is in the companion JSON
result with the same filename stem. Bounded-requalification and any authority
change remain separate actions.
