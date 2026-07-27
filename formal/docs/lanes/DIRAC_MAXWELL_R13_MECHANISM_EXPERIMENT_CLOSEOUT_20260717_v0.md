# Dirac-Maxwell R13 Mechanism Experiment Closeout 20260717 v0

Document ID:
- `DIRAC_MAXWELL_R13_MECHANISM_EXPERIMENT_CLOSEOUT_20260717_v0`

Status:
- `AUTHORITATIVE_RESULT_REVIEW_SUMMARY_ONLY`
- `R13_LANE_TERMINATED`
- `NO_NEW_SCIENTIFIC_PROMOTION`

Machine-readable authority:
- `formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_RECONCILIATION_RESULT_REVIEW_20260717_v2.json`
- SHA-256:
  `da2cbf87a042a387b84f469ffec106746f19976e6acdc193469e21aa3e0a619e`

## Exact status

```text
six-run experiment:
EXECUTED SUCCESSFULLY

execution custody:
ACCEPTED

saved-trajectory nonperturbation:
PASSED

raw observables:
RECONSTRUCTED

observable-semantics reconciliation:
NOT COMPLETED

reason:
EXECUTION-MARKER / EVIDENCE-ASSEMBLER FIELD-CONTRACT MISMATCH

H_A-H_E:
NOT EVALUATED

R13:
UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK

canonical robustness:
NUMERICALLY_BLOCKED

new E-REPRO:
NONE

R13 lane:
TERMINATED
```

## Authoritative closeout statement

The instrumented R13 mechanism experiment completed under accepted frozen authority,
with complete custody and byte-identical saved instrumented/control trajectories.
Independent review reproduced the raw numerical observables but blocked mechanism
classification because producer and verifier dominance-share reductions used different
binary64 summation semantics. A bounded reconciliation program was then authorized. Its
independently accepted v2 calculation failed closed on its single permitted invocation
before reading payload arrays because the execution marker and evidence assembler
required differently named run-ID fields. Under the frozen one-calculation stopping
rule, no retry or successor packet was authorized.

The R13 lane is therefore closed as `UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK`;
`H_A`-`H_E` remain unevaluated, the canonical robustness result remains
`NUMERICALLY_BLOCKED`, and no new `E-REPRO`, pillar, seam, or master-action claim is
created.

## Scientific interpretation

The failed invocation did not read the payload arrays and did not perform the requested
observable comparison. The result is neither `PREDICATE_INVARIANT` nor
`BLOCKED_OBSERVABLE_DECISION_INSTABILITY`. It is an evidence-processing interface
failure between the producer key `exact_run_ids` and the consumer requirement
`requested_run_ids`.

This is not evidence for or against a Maxwell-Dirac instability, either historical
reduction semantics, or any candidate mechanism hypothesis. The accepted bounded
Maxwell-Dirac result, canonical `NUMERICALLY_BLOCKED` robustness result, preserved
six-run evidence, and unchanged fourteen-file source tree remain in force.

## Frozen stopping boundary

- Authorized calculation invocations: `1`
- Observed calculation invocations: `1`
- Completed comparisons: `0`
- Retry authorized: `false`
- Second calculation authorized: `false`
- Packet v3 authorized: `false`
- Assembler repair authorized inside the closed lane: `false`
- Simulation authorized: `false`
- R13 automatic continuation authorized: `false`

Any future R13 work requires a fresh full-project priority decision. The easy field-name
repair does not create continuation authority.

## Historical lifecycle-test boundary

The byte-bound packet-preparation test encodes the historical pre-review state in which
the independent v2 review artifact must not exist. After the authorized lifecycle
advanced, four assertions in that preparation test are intentionally false in the
current state. Therefore:

```text
full repository green:
NOT CLAIMED
```

The failures are reported as historical, phase-sensitive preparation checks. Their
original bytes are preserved. Current-state acceptance is instead covered by the packet
review, result review, post-R13 gate tests, and Lean authority build. Quarantine or an
explicit historical-test classification is future maintenance debt and does not reopen
the scientific lane.

## Rotation

The immediate R13 chain is finished. Current authority returns to the accepted wider
priority map and selects only
`prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet`. GfE and
every other external comparator remain dormant.
