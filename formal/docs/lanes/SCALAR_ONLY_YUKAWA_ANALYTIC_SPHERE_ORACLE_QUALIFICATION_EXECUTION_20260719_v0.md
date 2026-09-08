# Analytic sphere-oracle qualification execution V0

## Principal execution result

```text
principal result:
ANALYTIC_SPHERE_ORACLE_QUALIFIED

execution status:
COMPLETED ONCE — PENDING INDEPENDENT RESULT REVIEW

authorized executions:
1

executions consumed:
1 / 1

production cubature:
UNADJUDICATED
```

The single authorized analytic-oracle execution completed without retry. It
qualified only the non-overlapping homogeneous-sphere reference interaction on
the eight frozen cases and two frozen evaluator-overlap grids. Independent
result review is required before the result can support any new selection.

## Stage results

```text
analytic derivation:       PASS
stable evaluator:          PASS
radial self-convergence:   PASS
analytic-radial agreement: PASS
mutation controls:         8 / 8 DETECTED
```

All six atomic stages completed. Worker scientific time was approximately
3.20 seconds; the radial stage used approximately 3.11 seconds.

## Derivation gate

The execution recorded the exterior-kernel angular identity

```text
integral_-1^1 exp(-k*sqrt(D^2+r^2-2*D*r*mu))/sqrt(...) dmu
  = 2*exp(-k*D)*sinh(k*r)/(k*D*r),  D>r,
```

and the radial identity

```text
integral_0^R r*sinh(k*r) dr
  = (k*R*cosh(k*R)-sinh(k*R))/k^2.
```

Together with `M_i=(4*pi/3)*rho_i*R_i^3`, strict pair non-overlap, and a
second sphere integration, these give

```text
U_N = -G*M1*M2/D

U_Y = -(1/3)*G*M1*M2*F(R1/lambda)*F(R2/lambda)
      *exp(-D/lambda)/D.
```

Both form factors, the center-distance exponential, `A_Y=1/3`, exchange
symmetry, energy units, and the point-particle limit passed. Radial numerical
agreement did not substitute for this gate.

## Stable evaluator

The small-series, moderate-direct, and large-scaled routes passed all frozen
overlap probes:

| Overlap | x | absolute difference | tolerance |
|---|---:|---:|---:|
| small/direct | 0.05 | `1.0114e-13` | `4.7623e-11` |
| small/direct | 0.10 | `1.6653e-15` | `4.5337e-11` |
| small/direct | 0.20 | `6.1062e-15` | `4.1151e-11` |
| direct/scaled | 20 | `4.3368e-19` | `6.7813e-15` |
| direct/scaled | 32 | `0` | `5.7095e-15` |
| direct/scaled | 40 | `1.0842e-19` | `5.4570e-15` |

The `x=1000` case used the scaled branch. No direct large-`x` hyperbolic path,
silent overflow, or silent underflow occurred.

## Eight analytic-radial comparisons

The table reports joules. Relative difference compares the stable analytic
Yukawa value with the 120-digit self-converged radial reference.

| Case | Newtonian | Yukawa analytic | Yukawa radial | relative difference | regimes |
|---|---:|---:|---:|---:|---|
| `LEGACY_STAGE_A_00_LARGE_X` | `-6.16413e-13` | `-3.22523e-24` | `-3.22523e-24` | `2.22e-16` | scaled/scaled |
| `LEGACY_STAGE_A_01_TRANSITION` | `-2.26018e-13` | `-2.27462e-16` | `-2.27462e-16` | `9.19e-15` | direct/direct |
| `LEGACY_STAGE_A_02_LONG_RANGE` | `-8.47568e-14` | `-1.27009e-14` | `-1.27009e-14` | `5.54e-15` | series/series |
| `SMALL_X_UNEQUAL_WIDE` | `-4.88199e-16` | `-1.58874e-16` | `-1.58874e-16` | `7.87e-15` | series/series |
| `MIXED_X_UNEQUAL` | `-1.48123e-13` | `-3.68348e-15` | `-3.68348e-15` | `7.51e-15` | direct/direct |
| `SMALL_GAP_LARGE_X` | `-6.77377e-13` | `-2.97837e-24` | `-2.97837e-24` | `6.84e-16` | scaled/scaled |
| `EXTREME_X_1000_UNEQUAL` | `-1.12934e-13` | `-1.24264e-25` | `-1.24264e-25` | `3.63e-15` | scaled/scaled |
| `LONG_RANGE_UNEQUAL_WIDE` | `-2.96246e-14` | `-8.75847e-15` | `-8.75847e-15` | `4.41e-15` | series/series |

All eight comparisons passed the frozen
`1e-38 J + 5e-12*abs(reference)` envelope. The largest observed relative
difference was approximately `9.20e-15`.

## Radial self-convergence

The independent one-dimensional `expm1`-scaled radial moment passed the
80-to-120-digit plateau at all 11 distinct `x` values from `0.001` through
`1000`. The observed differences ranged from approximately `4.75e-88` to
`8.78e-82`, far inside their frozen absolute-plus-relative tolerances.

This confirms the numerical reduced integral after analytic angular
reduction. It is not a separate proof of the two-sphere factorization.

## Mutations

All eight live-path mutations were detected:

1. Radius interpreted as diameter.
2. Surface gap used as center distance.
3. Sphere mass missing `4*pi/3`.
4. Yukawa amplitude missing `1/3`.
5. Second sphere form factor omitted.
6. Yukawa exponential sign reversed.
7. Direct `sinh/cosh` forced at `x=1000` and overflowed.
8. Cancellation-prone direct small-`x` path exceeded tolerance.

No mutation was rejected from metadata alone.

## Execution custody

```text
launches:
1

run id:
e844a8af-4c7e-4f17-8a09-0c3003b372ad

worker exit code:
0

peak job memory:
23,298,048 bytes

memory limit:
2,048 MiB

surviving processes:
0
```

The worker ran inside a new Windows process group and a kill-on-close Job
Object with a job-memory limit. The raw launcher transcript, launch identity,
stage records, child termination time, peak memory, and zero-survivor check are
preserved. No timeout occurred.

## Claim ceiling

This result does not judge or replace the old four-dimensional production
cubature. It validates no torque, DFT, apparatus harmonic vector, Jacobian,
identifiability result, or Stage B forecast.

```text
current authority:
review_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_execution_result
```
