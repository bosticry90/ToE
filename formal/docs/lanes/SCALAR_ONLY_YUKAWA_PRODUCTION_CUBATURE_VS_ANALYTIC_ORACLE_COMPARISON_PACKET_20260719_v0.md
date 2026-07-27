# Scalar-only Yukawa production-cubature versus analytic-oracle comparison packet V0

Date: 2026-07-19  
Status: `PREPARED_PENDING_INDEPENDENT_REVIEW`

```text
verdict:
PREPARED_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_V0
```

## Purpose

This packet consumes:

```text
prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0
```

It prepares one bounded energy-level comparison between the failed fixed-order
four-dimensional sphere cubature and the accepted homogeneous-sphere analytic
oracle. It performs no comparison during preparation.

```text
trusted analytic oracle:
QUALIFIED AND ACCEPTED

production cubature:
UNADJUDICATED

comparison execution:
NOT AUTHORIZED

repair or replacement:
NOT AUTHORIZED
```

## Frozen scientific paths

The packet hash-pins all decision-bearing implementations.

The exact Stage A Yukawa cubature remains:

```text
scalar_only_yukawa_torsion_balance_production_v1.py
::reduced_four_dimensional_density_integral_yukawa_energy
```

The already reviewed parameterized fixed-tensor mirror remains:

```text
scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0.py
::_fixed_density_integral
```

It uses binary64 Gauss–Legendre nodes in all four dimensions
`r1, mu1, r2, mu2`, with the frozen coordinate map, volume normalization, and
pairwise accumulation. No algorithmic repair is permitted.

The mirror supplies a Newtonian companion channel using the same nodes,
weights, coordinate map, and volume normalization. This is explicitly a
comparison diagnostic; it is not represented as a previously produced Stage A
scientific output. An equal-radius legacy control must verify that its Yukawa
channel reproduces the exact Stage A function at every frozen order.

The oracle is read-only and remains:

```text
scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py
::_uy_stable_float
::_radial_h
```

Oracle fields cannot be imported from or overwritten by production results.

## Frozen comparison domain

All eight accepted oracle cases are reused. No new favorable point is added:

1. `LEGACY_STAGE_A_00_LARGE_X`
2. `LEGACY_STAGE_A_01_TRANSITION`
3. `LEGACY_STAGE_A_02_LONG_RANGE`
4. `SMALL_X_UNEQUAL_WIDE`
5. `MIXED_X_UNEQUAL`
6. `SMALL_GAP_LARGE_X`
7. `EXTREME_X_1000_UNEQUAL`
8. `LONG_RANGE_UNEQUAL_WIDE`

All are strictly non-overlapping. Together they cover all three exact Stage A
failures, wide separation, small positive gaps, transition behavior, long
range, small `x`, and large `x` through `x=1000`.

The frozen production orders are:

```text
8, 16, 24, 32, 40, 48
```

Every case/order/component cell must receive a separate atomic record. There
are 96 required scientific cells:

```text
8 cases × 6 orders × 2 components
```

Order 48 is a production value, never a reference oracle.

## Component and metric contract

Newtonian and Yukawa values are judged separately. Combined energy is retained
only as a diagnostic and cannot decide component accuracy.

For each component, case, and order:

```text
epsilon_abs = abs(U_production - U_oracle)

epsilon_rel =
  abs(U_production - U_oracle)
  / max(abs(U_oracle), 1e-36 J)

q_n = epsilon_n / epsilon_previous
```

The frozen accuracy rule is:

```text
epsilon_abs <= 1e-36 J + 1e-6 * abs(U_oracle)
```

Each record also contains signed ratio where defined, runtime, nominal kernel
evaluations, observed work, and memory. A single improved last order is not a
convergence result; all decision predicates require a multi-order trend.

## Frozen classifications

Multilabel reporting is permitted only when every corresponding numerical
predicate passes.

### `PRODUCTION_CUBATURE_VALIDATED_ON_TESTED_CASES`

Both components pass every case at orders 32, 40, and 48, and the order-40 to
order-48 change also passes the frozen accuracy envelope.

### `IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED`

At least four cases fail at orders 32, 40, and 48 while their signed ratios
remain constant to 0.5% relative spread and their median ratio differs from one
by at least 0.1%.

### `YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED`

Newtonian passes every case at orders 32, 40, and 48, while Yukawa fails at
least one case at all three orders and matches a registered Yukawa mutation
fingerprint.

### `FIXED_ORDER_CUBATURE_INADEQUATE`

At least one case/component fails at order 48 and, over orders 24 through 48,
the errors either increase by at least 5% once or stall with at least two
convergence ratios of 0.95 or greater.

### `SLOW_BUT_CONVERGENT_AND_ECONOMICALLY_INFERIOR`

At least one case/component still fails at order 48, every error strictly
decreases from order 16 onward with every convergence ratio below 0.95, and the
fitted order/runtime needed for accuracy exceeds the frozen work envelope.

### `REGIME_DEPENDENT_PRODUCTION_FAILURE`

The same component passes all final three orders in at least one physical
regime and fails all final three orders in another.

### `NEAR_CONTACT_OR_TRANSITION_REGIME_UNDERSAMPLED`

The regime-dependent predicate passes; every failing small-gap or transition
case stalls at order 40 or 48; and at least one wide long-range case passes the
final three orders.

### `PRODUCTION_FAILURE_NOT_LOCALIZED`

At least one component fails, but none of the registered root-cause predicates
is fully satisfied. Near-threshold findings remain here rather than being
rounded into a preferred diagnosis.

### `PRODUCTION_COMPARISON_TIMEOUT`

Any total, stage, case, or order cap is exceeded, or any required atomic cell is
missing.

Visual trend selection, post-result predicate changes, and favorable rounding
are prohibited.

## Ten production-path controls

The future execution must route all controls through the actual comparison
implementation:

1. Newtonian point-equivalent agreement.
2. Missing `A_Y=1/3`.
3. Surface gap substituted for center distance.
4. Radius interpreted as diameter.
5. One cubature dimension held at order 8.
6. A 1% quadrature-weight normalization bias.
7. Newtonian and Yukawa channel swap.
8. Order-40 work mislabeled as order 48.
9. Production output written into an oracle field.
10. A constant 2% multiplicative production bias.

Channel swap, order overclaim, and oracle overwrite are custody/firewall
failures and cannot be converted into scientific classifications.

## Resource and custody contract

```text
total wall-clock cap:     1200 seconds
memory cap:               4096 MiB
process-group termination: MANDATORY
raw launcher transcript:   PRESERVED
zero surviving processes: REQUIRED
```

Per-cell caps are:

| Order | Seconds |
|---:|---:|
| 8 | 2 |
| 16 | 5 |
| 24 | 10 |
| 32 | 20 |
| 40 | 40 |
| 48 | 60 |

Six stage caps total 1,120 seconds, below the overall 1,200-second ceiling.
Budget changes after seeing results are forbidden.

## Packet-review outcomes

```text
PRODUCTION_COMPARISON_CONTRACT_READY
BLOCKED_PRODUCTION_PATH_IDENTITY
BLOCKED_ORACLE_CUSTODY
BLOCKED_CASE_GRID_CONTRACT
BLOCKED_METRIC_OR_CLASSIFICATION_CONTRACT
BLOCKED_MUTATION_ROUTING
BLOCKED_RESOURCE_OR_CUSTODY_CONTRACT
BLOCKED_SCOPE_OR_PROVENANCE
```

Only `PRODUCTION_COMPARISON_CONTRACT_READY` may authorize one bounded comparison
execution. Review acceptance does not authorize repair, replacement, Stage A,
or any downstream apparatus calculation.

## Scope firewall

This preparation did not:

- execute production cubature;
- rerun the oracle;
- repair or replace the kernel;
- compute torque or DFT coefficients;
- produce the real 150-component vector;
- compute a Jacobian, SVD, or identifiability result;
- rerun Stage A;
- begin Stage B.

```text
current authority:
review_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0_result
```
