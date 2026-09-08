# Independent review: analytic sphere-oracle qualification packet V0

## Review result

```text
verdict:
ANALYTIC_SPHERE_ORACLE_QUALIFICATION_CONTRACT_READY

review gates:
40 / 40 PASSED

authorized oracle executions:
1

executions performed:
0

production comparison:
NOT AUTHORIZED
```

The packet is mathematically complete, numerically executable, resource
bounded, and narrow enough for one legitimate qualification execution. This
review did not calculate an interaction value, evaluate the radial integral,
run a mutation, or qualify the oracle.

## Authority and custody

Five packet surfaces were hash-verified: the human packet, machine packet,
generator, tests, and Lean formalization. The packet was pending independent
review, all 42 preparation gates passed, and the scientific execution count
was zero.

## Independent case-grid reproduction

All eight rows independently reproduce

```text
D > R1 + R2
g = D - R1 - R2 > 0.
```

The grid includes small, transition, large, and `x=1000` radii-to-range
ratios; equal and unequal radii; wide separation; small positive gaps; and all
three failed Stage A sphere configurations.

The accepted numerical claim is limited to the eight frozen cases and the two
frozen evaluator-overlap grids. Acceptance does not preregister a continuous
uniform-error claim over every point in `0 < x <= 1000`.

## Formula audit

The Newtonian contract correctly freezes

```text
M_i = (4*pi/3)*rho_i*R_i^3
U_N = -G*M1*M2/D
```

for strictly non-overlapping homogeneous spheres, with joule units and the
attractive sign.

The Yukawa contract correctly binds

```text
A_Y = 1/3
F(x) = 3*(x*cosh(x)-sinh(x))/x^3
U_Y = -(1/3)*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)/D.
```

Both form factors, the center-distance exponential, the point-particle limit,
sphere-exchange symmetry, units, and sign are decision-bearing derivation
obligations.

The small-`x` coefficients were independently reconstructed from

```text
a_k = 6*(k+1)/(2*k+3)!,  k=0,...,4,
```

giving exactly

```text
1, 1/10, 1/280, 1/15120, 1/1330560.
```

The moderate branch is finite through `x=40`. The large branch uses

```text
H(x)=exp(-x)F(x)
    =3*((x-1)+(x+1)*exp(-2*x))/(2*x^3)
```

and the pair identity

```text
exp(-D/lambda)F(x1)F(x2)
  = exp(-g/lambda)H(x1)H(x2).
```

Thus no direct hyperbolic evaluation is permitted at `x=1000`. The log-domain
and explicit underflow record prevent a silent zero from being interpreted as
physical convergence. Both overlap grids have frozen absolute and relative
tolerances, and their boundaries cannot move after results exist.

## Radial cross-check audit and qualification

The one-dimensional path uses

```text
H_radial(x)=3/(2*x)*integral_0^1
  u*exp(-x*(1-u))*(-expm1(-2*x*u)) du.
```

This follows from the radial density moment

```text
exp(-x)*3/x^3*integral_0^x t*sinh(t) dt
```

after `t=x*u`. It integrates the radial moment numerically and cannot call the
closed-form form factor, the closed-form scaled factor, the production kernel,
or the four-dimensional cubature. Its 50/80/120-digit ladder, 80-to-120
plateau, and absolute-plus-relative agreement rule are executable.

One claim qualification is binding:

> The radial path is independent at the numerical implementation level after
> analytic angular reduction. It does not independently prove two-sphere
> factorization. The derivation gate must pass before radial agreement can
> qualify the oracle, and radial agreement cannot override a failed derivation.

The future execution must report separately:

```text
analytic derivation:          PASS / FAIL
stable evaluator:             PASS / FAIL / NOT_EVALUATED
radial self-convergence:      PASS / FAIL / TIMEOUT
analytic-radial agreement:    PASS / FAIL / NOT_EVALUATED
```

A nonconverged radial value may neither confirm nor reject the formula.

## Mutations and custody

The eight mutations cover geometry semantics, mass normalization, Yukawa
normalization, the second form factor, exponential sign, large-`x` overflow,
and small-`x` cancellation. They must traverse the live future evaluator,
radial cross-check, and adjudicator; metadata-only rejection is forbidden.

The 600-second and 2048-MiB envelope is complete. Six stage caps sum exactly
to the total budget. Process-group termination, raw launcher transcript,
timeout initiation, child termination records, zero surviving processes, and
stage-atomic outputs are mandatory. A qualified result requires every stage
to complete.

## Accepted outcome and stop rules

One execution may issue only one of the five frozen outcomes. Only
`ANALYTIC_SPHERE_ORACLE_QUALIFIED` can make a later production-method
comparison eligible for a fresh selector.

Acceptance does not authorize production-cubature comparison or replacement,
another broad diagnosis, Stage A rerun or V2, torque, DFT, apparatus harmonics,
the 150-vector, Jacobian/SVD, identifiability, or Stage B.

The future execution must stop for independent result review.

```text
current authority:
execute_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_once
```
