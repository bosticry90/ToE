# Scalar-only Yukawa sphere-kernel diagnosis packet review 20260719 v0

Date: `2026-07-19`  
Target: `review_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_v0_result`  
Verdict: `KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_CONTRACT_READY`  
Status: `INDEPENDENT_PACKET_REVIEW_COMPLETE — 36 / 36 GATES PASSED`

## Accepted contract

```text
diagnostic cases:              39
strictly non-overlapping:      39 / 39
evaluation paths:              4
mutations:                     10
work packages executed:        0 / 9
authorized diagnosis runs:     1
performed diagnosis runs:      0
```

The review accepts a reproducible diagnostic procedure, not a root cause or a
replacement method. No kernel, oracle, interaction value, convergence table,
torque, DFT, cost, or classification was computed during review.

## Non-overlap and regime reproduction

For every row the review independently reconstructed

\[
g=D-R_1-R_2>0,
\qquad D>R_1+R_2.
\]

The smallest frozen gap is `1e-4 m`. The 39 cases cover the three legacy Stage
A configurations and dimensionless ranges including:

```text
g/lambda: approximately 1.4e-3 through 10
R/lambda: 0.02 through 1000
```

They therefore include small positive gaps, wide separation, `lambda << g`,
`lambda ~ g`, `lambda ~ R`, and `lambda >> g,R` regimes. Center distance,
surface gap, radius, and diameter are separate contract fields.

## Independent analytic audit

The Newtonian oracle is restricted to non-overlapping homogeneous spheres and
uses the external shell theorem:

\[
U_N=-GM_1M_2/D.
\]

The Yukawa oracle is justified separately by the homogeneous-sphere exterior
field and two-sphere composition. The review verified the frozen `A_Y=1/3`,
sphere mass normalization, two form factors, center-distance exponential, and
joule dimensions:

\[
U_Y=-\frac{A_YGM_1M_2}{D}F(R_1/\lambda)F(R_2/\lambda)e^{-D/\lambda}.
\]

The Newtonian shell theorem is not used as a substitute justification for the
Yukawa form factor.

## Stable analytic evaluation

The domain reaches `x=R/lambda=1000`, so separate binary64 `cosh(x)` and
`sinh(x)` calls would be unsafe. The packet instead freezes

\[
H(x)=e^{-x}F(x)
=\frac{3[(x-1)+(x+1)e^{-2x}]}{2x^3}
\]

and evaluates the physical combination with `exp(-g/lambda) H(x1) H(x2)`.
The small-`x` series is also frozen. The smallest `x` in this specific 39-case
grid is `0.02`, above the `1e-3` series branch, while the independent radial
oracle cross-checks all cases. Thus no decision-bearing case relies on an
untested cancellation branch.

## Path independence and self-convergence

The four declared paths are scientifically distinct:

1. Frozen binary64 four-dimensional fixed tensor cubature.
2. Independently implemented analytic external-sphere formula.
3. One-dimensional high-precision radial form-factor integral.
4. Adaptive arbitrary-precision direct density integration on 12 anchors.

The analytic implementation may not import the production form-factor
function, and nearby orders of the same tensor method are explicitly not an
independent oracle.

The reduced and direct paths freeze `50,80,120` digit refinement; the direct
path also freezes adaptive degrees `6,8,10`. The final two levels must plateau
under `1e-36 J + 1e-10*abs(reference)` before production can be judged.
Evaluation, per-anchor time, total time, and memory caps fail closed as
`REFERENCE_ORACLE_INADEQUATE`.

## Components, near contact, torque, and DFT

Newtonian and Yukawa values, errors, and convergence remain separate. A
combined value reports cancellation but cannot decide component accuracy.

Near-contact contributions use the frozen excess coordinate

\[
\chi=(s-g)/\max(g,\lambda)
\]

with bins at `0,0.25,1,4,infinity`. Domain decomposition requires at least 90%
absolute contribution at `chi<=1` and a tenfold error improvement.

Energy oracles must pass before torque. Torque then compares analytic
derivatives, force/lever transport, and four-step five-point differentiation.

The analytic DFT test uses known `n=2,4,6` amplitudes and phases under
`c_n=(A_n/2)exp(i phi_n)`. The `n=258` control explicitly tests the expected
`N=256` alias without contaminating retained `N=512` coefficients. Production
DFT classification remains blocked until pair energy and torque are validated.

## Mutations and evidence-triggered labels

All ten mutations must traverse the live diagnostic implementation; test-only
substitutes are forbidden. The review verified distinct controls for volume,
radius/diameter, gap/distance, Yukawa strength and exponent, torque sign,
dimension refinement, form factors, DFT normalization, and phase.

Root-cause reporting is multilabel. Oracle, implementation, cubature,
near-contact, DFT, and economic labels each have separate predicates. The
packet remains unresolved if no frozen predicate is satisfied; a generic label
cannot be inferred from the original tolerance failure alone.

## One-execution authority and stop

Acceptance authorizes exactly:

```text
execute_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0_once
```

The diagnosis may emit only the preregistered component, oracle, convergence,
near-contact, torque, DFT, root-cause, remedy-recommendation, and cost records.
It must stop for independent result review.

This review does not authorize implementation correction, method replacement,
an immediate retry, Stage A reopening, a final real-150 vector, Jacobian, SVD,
`eta_lambda`, identifiability, V2, Stage B, or a forecast.
