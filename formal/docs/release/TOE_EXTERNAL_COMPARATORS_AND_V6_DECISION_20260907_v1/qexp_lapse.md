# QEXP_GRAVITATIONAL_LAPSE_COMPARATOR

Status: `EXTERNAL_COMPARATOR__NO_NATIVE_AUTHORITY_EFFECT`.
Implementation: `SPEC_ONLY_NOT_IMPLEMENTED`; verification: `NONE`.

## Bounded question and mathematics

Can a derived lapse be compared with this family **under one fixed definition
of potential, radial coordinate, clock normalization and real branch**?

For dimensionless real x and p, define

\[
F_p(x)=(1+px)^{1/p}\quad(p\ne0,\ 1+px>0),\qquad F_0(x)=e^x.
\]

The positive-base domain is deliberate; isolated real extensions of integer or
rational powers are not silently included. Direct expansion gives

\[
F_p(x)=1+x+\frac{1-p}{2}x^2+
\frac{(1-p)(1-2p)}6x^3+O(x^4).
\]

The logarithm has expansion
\(\log F_p=x-px^2/2+p^2x^3/3-\cdots\), proving the fixed-x limit
\(p\to0\). Special cases are \(F_1=1+x\), \(F_2=\sqrt{1+2x}\), and
\(F_p=e_q(x)\) for \(q=1-p\) on the common domain. The entropy literature
uses q-exponentials, but maximization requires a specified entropy, constraints,
measure and normalizability conditions; functional identity alone supplies none
of these. [Research paper on q-exponentials](https://pmc.ncbi.nlm.nih.gov/articles/PMC7763042/).

For a positive probability vector, direct differentiation of
\(S_q=k(1-\sum_i w_i^q)/(q-1)\) gives diagonal Hessian
\(-kq w_i^{q-2}\). Thus the usual concavity statement for positive q cannot
be transferred to q=-1, the formal p=2 member. Boundary probabilities need
separate treatment. This is algebra, not a thermodynamic derivation of gravity.

## Physical interpretation lock

With \(x=-GM/(rc^2)\), areal r and Schwarzschild time normalized at infinity,
the p=2 positive member is the exterior static-clock lapse for r>2GM/c².
This is a specified GR comparator, not a universal time-dilation formula.
Moving clocks, rotation, interiors and dynamical spacetimes need other data.

A future static spherical completion would need at least
\(ds^2=-N(r)^2c^2dt^2+A(r)^2dr^2+r^2d\Omega^2\), matter content, field
equations and boundary conditions. **A(r) is not selected here.** A zero of N
does not by itself establish an event horizon. Even a lapse redshift comparison
must specify stationary emitter/receiver worldlines and time normalization;
null trajectories and other observables require the spatial geometry.

The family is coordinate/potential-definition sensitive: redefining
\(y=(F_p(x)^r-1)/r\) for nonzero r makes the same function look like F_r(y).
Therefore p is not an invariant new constant without a physical definition of
x. A future native theory must derive its parameter, not select it after fitting.

The Einstein-1907 exponential attribution is not accepted. The cited historical
analysis discusses the early linear redshift relation; original-source historical
priority and novelty remain literature tasks, not calculator evidence.
[Historical analysis](https://pmc.ncbi.nlm.nih.gov/articles/PMC11275274/).
Fisher's translated original concerns Einstein equations with a massless scalar;
it is not automatic evidence of one shared physical p across theories.
[Fisher translation and original journal reference](https://arxiv.org/abs/gr-qc/9911008v1).
The Reddit original was not supplied; no author-credit or novelty claim is made.

## Proposed VPC seam and controls

| Seam | Required inputs | Proposed root / failure test |
| --- | --- | --- |
| Mathematical family -> local expansion | p, x, branch and expansion order | Canonical coefficients; mutate quadratic sign and cubic factor |
| Family -> special members | Fixed symbols and domain predicates | p=0 limit, p=1, p=2 and q mapping; reject division by zero and negative-base leakage |
| Native lapse -> comparator | Derived lapse and independently fixed potential convention | Coefficient comparison; reject post-hoc potential redefinition masquerading as new physics |
| Lapse -> metric -> observable | Full metric, matter, worldlines, boundary conditions | Field-equation residual and invariant observable; stop if spatial metric is missing |

Finite Taylor coefficients belong to a rational-function exact subproblem.
The exponential limit, generic real power, and any curvature/metric calculation
need separately supported semantics and certificates. A SymPy scratch check
cannot award VPC exact assurance. Future numerical comparisons must distinguish
truncation error from arithmetic enclosure and parameter uncertainty.

Not claimed: a new gravity theory, a horizon for arbitrary p, Tsallis gravity,
novelty, native CCFT recovery, experimental agreement, or VPC qualification.
