# Scalar-only Yukawa sphere-kernel diagnosis and reference-oracle packet 20260719 v0

Date: `2026-07-19`  
Target: `prepare_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_v0`  
Status: `PREPARED_PENDING_INDEPENDENT_REVIEW`  
Verdict: `PREPARED_BOUNDED_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_PACKET_V0`

## Exact authority

This packet consumes the selected route:

```text
BOUNDED_PRODUCTION_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE
```

It prepares a diagnostic contract only. No production kernel, reference oracle,
torque, DFT, convergence table, cost estimate, or root-cause result has been
computed. Independent review is required before one diagnosis may execute.

```text
next target:
review_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_v0_result

diagnostic execution:
NOT AUTHORIZED

Stage A rerun / V2 / identifiability / Stage B:
NOT AUTHORIZED
```

## Accepted failure anchor

The packet preserves, without reinterpretation:

```text
production versus order 24: 6.867902041407599e-2
order 16 versus order 24:    4.202776018628042e-1
required cubature tolerance: 1e-6

angular DFT 256 versus 512:  1.481612456806414e-6
required DFT tolerance:      1e-8
```

These values establish validation failure but no root cause and no physical
unidentifiability.

## Frozen non-overlapping diagnostic domain

Every diagnostic pair satisfies

\[
D=R_1+R_2+g,
\qquad g>0.
\]

The stratified grid contains three radius pairs:

```text
(2 mm, 3 mm)
(5 mm, 5 mm) — production pair
(5 mm, 10 mm)
```

and three surface gaps:

```text
0.1 mm
1 mm
10 mm
```

For every radius/gap combination, with
`R_eff=sqrt(R1*R2)`, four scalar ranges are frozen:

```text
lambda = g/10
lambda = g
lambda = R_eff
lambda = 10*max(g,R_eff)
```

This gives 36 stratified cases. The three original Stage A sphere-benchmark
cases are retained as explicit legacy-reproduction cases, for 39 total rows.
No case may be added, removed, or shifted after outputs are seen. All 12 frozen
high-precision anchor evaluations are declared in the machine packet.

## Separate component contract

Each path must report Newtonian and Yukawa values independently, including
absolute error, relative error, convergence, units, and limiting behavior.
The combined diagnostic value must also report

\[
C=\frac{|U_N|+|U_Y|}{\max(|U_N+U_Y|,10^{-300}\ {\rm J})}.
\]

The combined value cannot decide either component's accuracy.

## Exact and reduced reference oracles

For each non-overlapping homogeneous pair, the Newtonian candidate oracle is

\[
U_N(D)=-\frac{GM_1M_2}{D}.
\]

For `x=R/lambda`, the Yukawa candidate oracle is

\[
F(x)=\frac{3(x\cosh x-\sinh x)}{x^3},
\]

\[
U_Y(D)=-\frac{A_YGM_1M_2}{D}
F(R_1/\lambda)F(R_2/\lambda)e^{-D/\lambda},
\qquad A_Y=\frac13.
\]

The packet requires an independent derivation of the shell theorem, Yukawa
sphere exterior field, two-sphere composition, project normalization, and the
stable scaled form

\[
H(x)=e^{-x}F(x)
=\frac{3[(x-1)+(x+1)e^{-2x}]}{2x^3},
\]

so that

\[
U_Y=-\frac{A_YGM_1M_2}{D}H(x_1)H(x_2)e^{-g/\lambda}
\]

can be evaluated without overflow. The oracle implementation may not import
the production form-factor function.

## Four evaluation paths

1. **Frozen production path:** binary64 four-dimensional Gauss-Legendre orders
   `8, 12, 16, 24, 32, 48`, with all four dimensions refined together.
2. **Independent analytic path:** shell/form-factor formulas at 120 decimal
   digits for all 39 cases.
3. **Semi-analytic radial path:**
   `F(x)=3/x^3 integral_0^x t sinh(t) dt` with adaptive tanh-sinh at
   `50, 80, 120` digits for all 39 cases.
4. **Direct adaptive density path:** nondimensional four-dimensional adaptive
   tanh-sinh at digit/degree levels `(50,6), (80,8), (120,10)` on the 12 frozen
   anchors.

Changing the order of the failed tensor-product method does not create an
independent oracle.

## Oracle convergence and budget

The two finest high-precision levels must satisfy

```text
abs(last - previous)
  <= 1e-36 J + 1e-10*abs(last)
```

and independent oracles must agree under the same combined rule. Production
accuracy is judged only after the oracle passes, using

```text
abs(production - reference)
  <= 1e-36 J + 1e-6*abs(reference).
```

The direct adaptive route is bounded by two million function evaluations and
180 seconds per anchor, 3600 seconds total, and 4096 MiB. Exhaustion fails
closed as `REFERENCE_ORACLE_INADEQUATE`; budgets and tolerances cannot be
changed after results.

## Near-contact localization

For point-pair separation `s`, define

\[
\chi=\frac{s-g}{\max(g,\lambda)}.
\]

Signed energy, absolute-integrand contribution, node fraction, and local
kernel-variation ratios are recorded in bins

```text
[0,0.25], (0.25,1], (1,4], (4,infinity).
```

The near-contact region is dominant when the absolute fraction at `chi<=1` is
at least `0.90`. Independent adaptation of the three finite subdomains must
improve error by at least tenfold before
`NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED` may be assigned.

## Precision, summation, and symmetry

The diagnosis compares IEEE binary64 with `50, 80, 120` decimal digits;
ordinary, pairwise, Kahan, and exact/high-precision accumulation; separate and
combined components; raw SI and nondimensional coordinates; and analytically
reduced versus explicit-azimuth controls on the three legacy cases.

## Pair energy before torque

Torque work remains blocked until the pair-energy oracles pass. Then the packet
compares analytic energy derivatives, the frozen force/lever route, and
five-point energy derivatives at steps

```text
1e-3, 5e-4, 2.5e-4, 1.25e-4 rad
```

over three gaps, three scalar ranges, two angles, and separate Newtonian and
Yukawa components. The combined tolerance is
`1e-22 N m + 1e-8*abs(tau_oracle)`.

## Independent DFT isolation

The exact synthetic torque uses

```text
n=2: A=2e-15 N m, phi= pi/7
n=4: A=7e-16 N m, phi=-pi/9
n=6: A=3e-16 N m, phi= pi/11
```

with expected convention

\[
c_n=\frac{A_n}{2}e^{i\phi_n}.
\]

The frozen grids are `N=32,64,128,256,512,1024`, with absolute tolerance
`1e-28 N m` and relative tolerance `1e-12`. A known `n=258` term tests aliasing:
it aliases into `n=2` at `N=256` but not into the retained coefficients at
`N=512`.

If analytic torque fails, the classification is
`ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE`. If analytic torque passes but
validated production torque fails, the classification is
`KERNEL_NOISE_DRIVES_DFT_FAILURE`.

## Ten production-routed mutations

The same diagnostic chain must reject:

1. A missing radial `r^2` volume factor.
2. Radius interpreted as diameter.
3. Surface gap used as center distance.
4. `A_Y=1` instead of `1/3`.
5. Reversed Yukawa exponential sign.
6. Reversed `tau=-dU/dtheta` sign.
7. One integration dimension left at order 8.
8. One missing sphere form factor.
9. Doubled DFT normalization.
10. Reversed DFT phase convention.

Test-only substitute kernels are forbidden.

## Diagnostic outcomes

Multiple labels may be reported, with a frozen principal-priority rule:

```text
REFERENCE_ORACLE_INADEQUATE
IMPLEMENTATION_DEFECT_LOCALIZED
NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED
FIXED_ORDER_CUBATURE_INADEQUATE
ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE
KERNEL_NOISE_DRIVES_DFT_FAILURE
INTERNAL_APPARATUS_FORWARD_MODEL_NOT_ECONOMICALLY_VALIDATABLE
```

Oracle availability is reported separately as either
`ANALYTIC_OR_REDUCED_SPHERE_ORACLE_AVAILABLE` or
`ANALYTIC_OR_REDUCED_SPHERE_ORACLE_NOT_VALIDATED`.

## Output and authority firewall

Authorized future outputs are component/reference values, convergence and
near-contact tables, precision/summation comparisons, torque/DFT checks,
root-cause labels, a recommended method, and cost estimate.

Forbidden outputs include the final real-150 vector, Jacobian, singular values,
`eta_lambda`, identifiability, noise, forecasts, and scalar-range or `alpha`
claims.

The packet contains nine unexecuted work packages and passes 30 preparation
gates. Only an independent review outcome of
`KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_CONTRACT_READY` may authorize one bounded
diagnosis. That execution must stop for independent result review before any
repair, replacement, redesign, closure, or Stage A reopening is selected.
