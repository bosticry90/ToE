# Independent result review: analytic sphere-oracle qualification V0

## Accepted result

```text
verdict:
ACCEPTED_ANALYTIC_SPHERE_ORACLE_QUALIFIED

review gates:
39 PASS
1 PASS WITH CUSTODY QUALIFICATION
0 FAIL

execution count:
1 / 1 CONSUMED

production cubature:
UNADJUDICATED
```

The independent review accepts the analytic homogeneous-sphere Newtonian and
Yukawa oracle on the eight frozen non-overlapping cases and the two evaluator
overlap grids. The review did not rerun the oracle or call production cubature.

## Custody reconstruction

Five execution surfaces were hash-verified. The release and canonical result
files are byte-identical. The scientific payload and launch-custody objects
match their atomic output files exactly.

Custody reproduced:

```text
launches:                 1
worker exit code:         0
timeout:                  NONE
atomic stages complete:   6 / 6
raw outcome records:      1
peak job memory:          23,298,048 bytes
surviving processes:      0
```

The raw transcript hash and exact six-stage order were reproduced. Every
stage file matches the release record and completed within its frozen cap.

One non-scientific qualification is preserved: `current_stage.json` remains
an `IN_PROGRESS` monitor pointer for O6. It is not decision-bearing. The
authoritative O6 atomic stage file, raw `STAGE_END`, worker exit code, canonical
result, and zero-survivor record all establish completion. No post-run file was
altered to hide this discrepancy.

## Derivation audit

The review independently reconstructed the exact small-`x` coefficients

```text
1, 1/10, 1/280, 1/15120, 1/1330560
```

from `a_k=6(k+1)/(2k+3)!`.

The execution record contains the Newtonian shell reduction, Yukawa angular
kernel identity, radial antiderivative, both sphere form factors, center
separation in the exponential, `A_Y=1/3`, sphere-mass normalization, exchange
symmetry, joule units, strict non-overlap, point-particle limit, and the scaled
surface-gap identity. The independent derivation audit passed.

## Stable evaluator audit

Evaluator regimes were independently reconstructed from the frozen `x`
values. All eight case assignments agree with the preregistered small-series,
moderate-direct, and large-scaled boundaries.

All six overlap differences were recomputed from the committed left and right
values and remain inside their frozen tolerances. The `x=1000` case used the
scaled route, with no direct hyperbolic fallback and no silent overflow or
underflow.

## Radial convergence and analytic agreement

The review recomputed every decision from the stored high-precision values:

```text
radial precision plateaus:
11 / 11 PASSED

analytic-radial case comparisons:
8 / 8 PASSED

largest relative difference:
9.1935311209820829...e-15
```

All absolute and relative differences agree with their recorded values and
remain within the frozen envelopes. The three failed Stage A sphere cases are
present, but this review draws no conclusion about their old production
cubature values.

The prior independence qualification remains binding: the radial calculation
validates the reduced numerical value after angular reduction; the separately
passed derivation establishes two-sphere factorization.

## Mutation audit

The exact eight mutation identities were reproduced. Each has a
decision-bearing numerical failure reason: six yield nonzero energy
discrepancies, the forced large-`x` direct route raises overflow, and the forced
small-`x` direct route exceeds its `H` tolerance. All eight mutations therefore
pass independent review.

## Scientific interpretation

The project now has an accepted, efficient reference interaction for the
frozen non-overlapping homogeneous-sphere cases. This supports a fresh decision
about a bounded comparison with the failed production method.

It does not yet establish:

- A continuous uniform-error bound over every `0<x<=1000` point.
- That the old production cubature is wrong or slow.
- Authority to replace the production kernel.
- Valid torque, DFT, 150-vector, Jacobian, or identifiability results.
- Stage B eligibility.

## Authority rotation

This review authorizes a fresh scientific-response selector only. The selector
may compare bounded response routes, including a small production-versus-oracle
comparison, but this review does not authorize that comparison directly.

```text
current authority:
select_post_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_execution_result_scientific_response_v0
```
