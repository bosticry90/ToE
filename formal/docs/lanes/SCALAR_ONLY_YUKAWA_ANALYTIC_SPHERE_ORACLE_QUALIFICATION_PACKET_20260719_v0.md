# Scalar-only Yukawa analytic sphere-oracle qualification packet V0

## Preparation result

```text
verdict:
PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_PACKET_V0

status:
PREPARED_PENDING_INDEPENDENT_REVIEW

oracle qualification execution:
NOT AUTHORIZED / NOT PERFORMED

production cubature comparison:
NOT AUTHORIZED
```

This packet consumes only
`prepare_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0`.
It freezes one small oracle-qualification contract and rotates authority to
independent packet review. No Newtonian or Yukawa interaction value was
computed during preparation.

## Scientific question

Can the exact Newtonian and homogeneous-sphere Yukawa expressions be derived
under the project conventions, evaluated stably for the required domain
`0 < R/lambda <= 1000`, and confirmed by one independent one-dimensional
high-precision calculation?

This packet does not judge the failed four-dimensional production cubature.

## Frozen physical conventions and derivation burden

For each homogeneous sphere,

```text
M_i = (4*pi/3)*rho_i*R_i^3
D   = R1 + R2 + g
g   = D - R1 - R2 > 0
A_Y = 1/3
```

The Newtonian derivation must establish, for strict non-overlap,

```text
U_N(D) = -G*M1*M2/D.
```

With `x_i=R_i/lambda`, the Yukawa derivation must establish

```text
F(x) = 3*(x*cosh(x)-sinh(x))/x^3

U_Y(D) = -(1/3)*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)/D.
```

The derivation must verify both sphere factors, use center separation in the
exponential, prove the point-particle limit `F(x)->1`, preserve dimensions and
the attractive sign, and prove symmetry under exchange of the spheres. A
standard-formula citation cannot replace these obligations.

## Stable evaluator

Every branch returns the common scaled factor

```text
H(x) = exp(-x)*F(x).
```

The primary regimes are frozen before execution:

| Regime | Primary domain | Required expression |
|---|---:|---|
| Small | `0 < x <= 0.1` | `H=exp(-x)*(1+x^2/10+x^4/280+x^6/15120+x^8/1330560)` |
| Moderate | `0.1 < x <= 40` | `H=exp(-x)*3*(x*cosh(x)-sinh(x))/x^3` |
| Large | `40 < x <= 1000` | `H=3*((x-1)+(x+1)*exp(-2*x))/(2*x^3)` |

The pair evaluator must use the stable identity

```text
exp(-D/lambda)*F(x1)*F(x2)
  = exp(-g/lambda)*H(x1)*H(x2)
```

and therefore

```text
U_Y = -(1/3)*G*M1*M2*exp(-g/lambda)*H(x1)*H(x2)/D.
```

The large branch may not construct `sinh(x)` or `cosh(x)` directly. The pair
energy must also be available in the log domain. Silent overflow or underflow
is prohibited; binary64 underflow must retain a high-precision value and
`log10(abs(U_Y))` with an explicit underflow label.

Two overlap grids are preregistered:

```text
small/direct:  x = {0.05, 0.1, 0.2}
  |delta H| <= 5e-14 + 5e-11*|H_reference|

direct/scaled: x = {20, 32, 40}
  |delta H| <= 5e-15 + 5e-13*|H_reference|
```

Regime boundaries may not change after execution begins.

## Eight frozen non-overlapping cases

Both densities are `19250 kg/m^3`. Center distance is mechanically
`D=R1+R2+g`.

| Case | R1 (m) | R2 (m) | g (m) | lambda (m) | x1 | x2 |
|---|---:|---:|---:|---:|---:|---:|
| `LEGACY_STAGE_A_00_LARGE_X` | 0.005 | 0.005 | 0.001 | 0.0001 | 50 | 50 |
| `LEGACY_STAGE_A_01_TRANSITION` | 0.005 | 0.005 | 0.02 | 0.005 | 1 | 1 |
| `LEGACY_STAGE_A_02_LONG_RANGE` | 0.005 | 0.005 | 0.07 | 0.1 | 0.05 | 0.05 |
| `SMALL_X_UNEQUAL_WIDE` | 0.001 | 0.003 | 0.02 | 1 | 0.001 | 0.003 |
| `MIXED_X_UNEQUAL` | 0.002 | 0.008 | 0.002 | 0.004 | 0.5 | 2 |
| `SMALL_GAP_LARGE_X` | 0.005 | 0.005 | 0.00001 | 0.00001 | 500 | 500 |
| `EXTREME_X_1000_UNEQUAL` | 0.005 | 0.0025 | 0.000005 | 0.000005 | 1000 | 500 |
| `LONG_RANGE_UNEQUAL_WIDE` | 0.002 | 0.008 | 0.05 | 0.5 | 0.004 | 0.016 |

The grid covers small, transition, large, and extreme `x`; equal and unequal
radii; wide separation; small positive gaps; all three failed Stage A sphere
configurations; and the required `x=1000` endpoint. Adding, removing, or moving
a case after seeing results is forbidden.

## One independent numerical cross-check

Exactly one independent path is allowed. It computes the scaled radial moment
without calling either closed-form factor:

```text
H_radial(x) = 3/(2*x) * integral_0^1 [
  u*exp(-x*(1-u))*(-expm1(-2*x*u))
] du.
```

This is the scaled form of

```text
exp(-x)*3/x^3 * integral_0^x t*sinh(t) dt.
```

The path uses arbitrary-precision tanh-sinh quadrature at 50, 80, and 120
decimal digits on all eight cases. It may not import the analytic form-factor
implementation, the closed-form scaled factor, the production kernel, the old
four-dimensional cubature, or the 39-case grid.

The 80-to-120-digit self-convergence rule is

```text
|H_120-H_80| <= 1e-30 + 1e-24*|H_120|.
```

The stable production-independent evaluator must agree with the radial path
within

```text
H:   |delta| <= 5e-15 + 5e-12*|H_reference|
U_Y: |delta| <= 1e-38 J + 5e-12*|U_reference|.
```

Failure to self-converge is a failed cross-check, not permission to treat the
most expensive value as an oracle.

## Resource and execution custody

The future execution is capped at 600 seconds and 2048 MiB. Stage caps are:

| Stage | Maximum seconds |
|---|---:|
| Preflight and custody | 20 |
| Derivation, domain, and dimensions | 60 |
| Stable evaluator and overlaps | 90 |
| Independent radial cross-check | 300 |
| Mutations and adjudication | 90 |
| Atomic finalization | 40 |

The launcher must preserve its raw transcript, timeout-initiation timestamp,
the complete child-process tree, child-termination timestamps, and a mandatory
zero-surviving-process check. Process-group termination is mandatory.

Each stage writes one atomic status from `NOT_STARTED`, `COMPLETE`, `FAILED`, or
`TIMEOUT`. Completed stage evidence may be decision-bearing only where this
packet preregisters it. The packet-wide qualified outcome requires all stages
to complete. Budget or custody failure fails closed, and result-dependent
budget changes are forbidden.

## Eight live-path mutations

All mutations must traverse the future production-independent oracle
evaluator, radial cross-check, and adjudicator. Metadata-only rejection is not
sufficient.

1. Interpret radius as diameter.
2. Substitute surface gap for center distance.
3. Omit the `4*pi/3` mass factor.
4. Omit `A_Y=1/3`.
5. Omit the second sphere form factor.
6. Reverse the Yukawa exponential sign.
7. Force direct `sinh/cosh` evaluation in the large-`x` branch.
8. Force the cancellation-prone direct formula in the small-`x` branch.

Every mutation must fail its frozen predicate.

## Future execution outputs and terminal outcomes

After an accepted independent packet review, one execution may output only
derivation statuses, Newtonian and Yukawa oracle values, overlap records,
radial cross-check values, errors, precision/runtime/custody records, mutation
results, and one of:

```text
ANALYTIC_SPHERE_ORACLE_QUALIFIED
ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE
ANALYTIC_ORACLE_CROSS_CHECK_FAILED
ANALYTIC_ORACLE_QUALIFICATION_TIMEOUT
SPHERE_ORACLE_NOT_VALID_OVER_REQUIRED_DOMAIN
```

Only `ANALYTIC_SPHERE_ORACLE_QUALIFIED` may make a later production-method
comparison eligible for a fresh scientific-response selector.

## Independent packet review

The review may return:

```text
ANALYTIC_SPHERE_ORACLE_QUALIFICATION_CONTRACT_READY
BLOCKED_ANALYTIC_DERIVATION_CONTRACT
BLOCKED_STABLE_EVALUATOR_CONTRACT
BLOCKED_REPRESENTATIVE_CASE_GRID
BLOCKED_INDEPENDENT_CROSS_CHECK_CONTRACT
BLOCKED_RESOURCE_AND_PROCESS_CUSTODY
BLOCKED_MUTATION_ROUTING
BLOCKED_SCOPE_OR_PROVENANCE
```

Only the ready outcome authorizes one small oracle-qualification execution.
It does not authorize production-cubature comparison, integration replacement,
Stage A rerun or V2, torque, DFT, identifiability, or Stage B. Independent
result review and a fresh selector are required after that future execution.

## Scope firewall

Packet preparation performed no oracle evaluation, integration, mutation,
production comparison, torque, DFT, harmonic-vector construction, Jacobian,
SVD, identifiability analysis, or forecast.

```text
current authority:
review_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0_result
```
