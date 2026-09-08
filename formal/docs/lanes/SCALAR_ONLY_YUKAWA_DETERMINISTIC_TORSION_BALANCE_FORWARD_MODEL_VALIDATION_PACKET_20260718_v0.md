# Scalar-only Yukawa deterministic torsion-balance forward-model validation packet v0

Date: `2026-07-18`  
Target: `prepare_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v0`  
Verdict: `PREPARED_DETERMINISTIC_FORWARD_MODEL_VALIDATION_CONTRACT_PENDING_INDEPENDENT_REVIEW`

## Boundary

```text
result type:
DETERMINISTIC FORWARD-MODEL VALIDATION CONTRACT

Gaussian noise:
NONE

covariance:
NONE

Monte Carlo trials:
NONE

profile likelihood:
NONE

sensitivity forecast:
NONE

execution:
NOT AUTHORIZED
```

This packet prepares Stage A only. It asks whether one internal two-sphere-pair
apparatus has a correct, convergent, meaning-preserving map from geometry to
Newtonian/Yukawa energy, torque, harmonics, deterministic perturbation
directions, and a real 150-component output vector.

It is not an Eöt-Wash reconstruction and uses no real or synthetic observations.

## Frozen comparison and apparatus

The supplied comparison uses

\[
u(r;\lambda_0)=-\frac{Gm_Dm_A}{r}
\left[1+\frac13 e^{-r/\lambda_0}\right]
\]

at the point-mass level. `A_Y=1/3` is fixed. `lambda0=0` is an exact software
sentinel for the Newtonian/Einstein limit. No `lambda0` or `alpha` is selected.

The apparatus contains two uniform detector spheres and two uniform attractor
spheres:

```text
rho_D = rho_A:
19250 kg m^-3

a_D = a_A:
5.0e-3 m

L_D = L_A:
3.0e-2 m

surface gaps:
25 log-spaced values from 1.0e-4 m to 1.0e-2 m

positive scalar ranges:
25 log-spaced values from 1.0e-5 m to 1.0e-1 m

reference validation range:
lambda_ref = 1.0e-3 m
```

Detector centers are

\[
\mathbf x_D^{(s)}=(sL_D,0,0),\qquad s\in\{-1,+1\}.
\]

Attractor centers are

\[
\mathbf x_A^{(t)}=
(tL_A\cos\theta,tL_A\sin\theta,-z),
\qquad
z=a_D+a_A+d,
\qquad t\in\{-1,+1\}.
\]

The support structures are massless. Every body pair remains non-overlapping.

## One production kernel

All production and benchmark paths must call the same functions in this order:

```text
pair_distance
-> pair_energy_and_radial_derivative
-> apparatus_energy
-> analytic_energy_derivative_torque
-> discrete_harmonic_transform
-> real_150_vector
```

For one non-overlapping uniform-sphere pair,

\[
u_N(r)=-\frac{GM_D M_A}{r},
\]

\[
u_Y(r;\lambda_0)=
-\frac{G A_Y M_D M_A}{r}
F(a_D/\lambda_0)F(a_A/\lambda_0)e^{-r/\lambda_0},
\]

where

\[
F(x)=\frac{3(x\cosh x-\sinh x)}{x^3}.
\]

For stable large-`x` evaluation, production must use

\[
H(x)=e^{-x}F(x)
=\frac{3}{2x^3}\left[(x-1)+(x+1)e^{-2x}\right]
\]

and

\[
F(a_D/\lambda_0)F(a_A/\lambda_0)e^{-r/\lambda_0}
=H(a_D/\lambda_0)H(a_A/\lambda_0)
e^{-(r-a_D-a_A)/\lambda_0}.
\]

For `x < 1e-3`, `F(x)` must use its even power series through `x^6` and
`H(x)=exp(-x)F(x)`. Overflow, underflow, and branch behavior must be reported;
underflow may represent a zero Yukawa contribution only after the scaled
expression has been used.

## Production torque and independent cross-checks

Let `q=s*t` and

\[
r_q^2=L_D^2+L_A^2+z^2-2qL_DL_A\cos\theta.
\]

Each `q` occurs twice, so

\[
U(\theta,d)=2\sum_{q=\pm1}u(r_q).
\]

The production torque is analytic differentiation of the same energy:

\[
\tau_z(\theta,d)=-2\sum_{q=\pm1}
u'(r_q)\frac{qL_DL_A\sin\theta}{r_q}.
\]

Two independent cross-checks are mandatory:

1. Direct pair-force/lever-arm torque summed over all four pairs.
2. Five-point central differentiation of `U(theta,d)` with angular steps
   `1e-3`, `5e-4`, `2.5e-4`, and `1.25e-4 rad`.

Neither cross-check may become the production path after results are viewed.

## Exact harmonic convention

Positive angle is counterclockwise about `+z` when viewed from `+z`. `theta=0`
places attractor and detector axes along `+x`. Positive torque is about `+z`.

The continuous coefficient is

\[
c_n(d,\lambda_0)=\frac{1}{2\pi}
\int_0^{2\pi}\tau_z(\theta,d;\lambda_0)e^{-in\theta}\,d\theta.
\]

For

\[
\tau=a_0+\sum_{n\ge1}[a_n\cos(n\theta)+b_n\sin(n\theta)],
\]

the frozen relation is

\[
a_n=2\Re c_n,
\qquad
b_n=-2\Im c_n.
\]

Production uses `N_theta=256` equally spaced samples
`theta_k=2*pi*k/N_theta` and

\[
c_n^{(N)}=\frac1N\sum_{k=0}^{N-1}
\tau_z(\theta_k)e^{-in\theta_k}.
\]

The retained harmonics are `n=2,4,6`. The real vector is gap-major:

```text
gap 0: Re(c2), Im(c2), Re(c4), Im(c4), Re(c6), Im(c6)
gap 1: Re(c2), Im(c2), Re(c4), Im(c4), Re(c6), Im(c6)
...
gap 24: Re(c2), Im(c2), Re(c4), Im(c4), Re(c6), Im(c6)
```

This is exactly 150 real `N m` values. No complex Gaussian or 300-vector
interpretation is permitted.

## Four production-routed analytic benchmarks

1. **Point Newtonian:** `u=-Gm1m2/r`, `u'=+Gm1m2/r^2`, including sign,
   inverse-distance energy, and inverse-square force scaling.
2. **Point Yukawa:**
   `u=-G A_Y m1m2 exp(-r/lambda0)/r` and
   `u'=G A_Y m1m2 exp(-r/lambda0)(1/r^2+1/(lambda0*r))`.
3. **Uniform-sphere form factor:** production form-factor energy versus a
   deterministic reduced four-dimensional Gauss-Legendre density integral at
   `(r,lambda0)=(0.011,1e-4),(0.03,5e-3),(0.08,0.1) m`.
4. **Apparatus torque/symmetry:** production analytic torque versus both the
   force/lever and five-point energy-derivative cross-checks, including the
   exact symmetry zeros.

Every benchmark invokes the production distance, energy, derivative, torque,
and harmonic functions applicable to it. A separate demonstration kernel is
prohibited.

## Deliberate mutations

All five mutations must be applied one at a time and must fail their designated
controls:

1. Flip the Yukawa energy sign.
2. Replace `A_Y=1/3` by `A_Y=1`.
3. Remove one uniform-sphere form factor.
4. Flip the `tau=-dU/dtheta` sign.
5. Replace the DFT normalization `1/N` by `2/N`.

A mutation that survives its designated control blocks execution as
`BLOCKED_PRODUCTION_KERNEL_VALIDATION`.

## Symmetry and phase controls

The nominal geometry obeys

\[
U(\theta+\pi)=U(\theta),\quad U(-\theta)=U(\theta),
\quad \tau(-\theta)=-\tau(\theta).
\]

The execution must verify:

- odd `n=1,3,5` harmonics vanish;
- nominal even cosine quadratures vanish;
- even sine quadratures `n=2,4,6` are nonzero at identifiable configurations;
- torque vanishes at `theta=0,pi/2,pi,3pi/2`;
- reversing `theta` maps `c_n -> conjugate(c_n)`;
- a rigid angular-zero shift `delta=pi/16` maps
  `c_n -> exp(-i*n*delta)c_n`; and
- Newtonian/Yukawa distance scaling matches the frozen kernels.

## Numerical convergence

For a refined result `y_ref` and coarser result `y`, define

\[
E(y,y_{\rm ref})=
\frac{|y-y_{\rm ref}|}{\max(|y_{\rm ref}|,10^{-22}\ {\rm N\,m})}.
\]

The frozen ladders and tolerances are:

```text
angular DFT:
N = 128, 256, 512
production 256 versus reference 512: E < 1e-8

reduced Gauss-Legendre density cubature:
orders 8, 12, 16, 24 on every radial and cosine coordinate
order 16 versus 24: relative error < 1e-6

analytic torque versus force/lever torque:
relative error < 1e-10 or absolute error < 1e-22 N m

five-point energy derivative:
must exhibit refinement and agree at the finest step within
relative error 1e-8 or absolute error 1e-22 N m

repeated deterministic run:
bit-identical canonical output bytes and SHA-256
```

Near-zero forbidden channels are judged by the absolute floor, not unstable
relative error.

## Sixteen deterministic perturbation maps

All nominal perturbations are zero. They are deterministic directions, not
random variables and have no priors.

| Direction | Unit | Test range | Exact map |
| --- | --- | --- | --- |
| Torque calibration | fraction | `±0.02` | multiply final torque by `1+k_tau` |
| Source density scale | fraction | `±0.01` | `rho_A -> rho_A(1+k_A)` |
| Detector density scale | fraction | `±0.01` | `rho_D -> rho_D(1+k_D)` |
| Detector lever offset | m | `±1e-4` | `L_D -> L_D+dL_D` |
| Attractor lever offset | m | `±1e-4` | `L_A -> L_A+dL_A` |
| Gap offset | m | `±1e-5` | every `d_j -> d_j+dd`; nonpositive gaps invalid |
| Attractor-axis x offset | m | `±1e-4` | add `dx` to every attractor-center x coordinate |
| Attractor-axis y offset | m | `±1e-4` | add `dy` to every attractor-center y coordinate |
| Angular-zero offset | rad | `±1e-3` | evaluate geometry at `theta-dtheta` |
| Harmonic leakage | fraction | `±0.002` | frozen adjacent-harmonic map below |
| Background 2Re | N m | `±1e-17` | add to Re(c2) at every gap |
| Background 2Im | N m | `±1e-17` | add to Im(c2) at every gap |
| Background 4Re | N m | `±1e-17` | add to Re(c4) at every gap |
| Background 4Im | N m | `±1e-17` | add to Im(c4) at every gap |
| Background 6Re | N m | `±1e-17` | add to Re(c6) at every gap |
| Background 6Im | N m | `±1e-17` | add to Im(c6) at every gap |

With complex vector `z=(c2,c4,c6)`, leakage is exactly

\[
z'=(I+\ell L)z,
\qquad
L=\begin{pmatrix}0&1&0\\1&0&1\\0&1&0\end{pmatrix}.
\]

The transformation order is physical geometry/density, energy and torque,
harmonics, calibration, leakage, then additive backgrounds. Every test range
must preserve positive radii, lever arms, densities, and gaps.

## Deterministic Jacobian and identifiability

At each positive scalar range, construct

\[
J_{ij}=\frac{\partial y_i}{\partial p_j}
\]

for `p=(log(lambda0), sixteen perturbation directions)`. Derivatives use
centered differences with a second half-step check, except exactly linear
calibration, leakage, and backgrounds, which use analytic columns.

Columns are standardized by their frozen test scales and the whole matrix by

\[
\tau_{\rm ref}=\max_i|y_{N,i}|,
\]

with fail-closed behavior if `tau_ref <= 1e-30 N m`.

The SVD numerical-rank rule is

\[
s_k/s_1\ge10^{-10}.
\]

Pairwise columns are exactly degenerate when the normalized residual after best
one-column projection is at most `1e-10`, and nearly degenerate when absolute
correlation is at least `0.999`.

Scalar-range shape identifiability is

\[
\eta_\lambda=
\frac{\|(I-P_N)j_{\log\lambda}\|}
{\|j_{\log\lambda}\|},
\]

where `P_N` projects onto the deterministic nuisance-column space.

```text
identifiable:
eta_lambda >= 1e-3 and derivative norm above 1e-10 of tau_ref

near-degenerate:
1e-6 <= eta_lambda < 1e-3

indistinguishable:
eta_lambda < 1e-6 or derivative norm below the floor
```

Stage A may pass only if at least five contiguous positive range points in the
transition domain are identifiable and the classifications survive the angular
and derivative refinements. Otherwise the result is
`BLOCKED_PARAMETER_IDENTIFIABILITY`.

The torque-calibration, source-density, and detector-density columns are
expected to be exactly amplitude-degenerate. The execution must report this;
it may not claim that those three parameters are separately identifiable.

## Canonical deterministic outputs

The execution must prepare, but this packet does not create:

1. One Newtonian real-150 vector.
2. One Yukawa real-150 vector for each of 25 positive ranges.
3. One total real-150 reference vector at `lambda_ref=1e-3 m`.
4. Sixteen deterministic perturbation-response vectors at every evaluated range.
5. SVD, rank, correlation, null-direction, and `eta_lambda` tables.

Canonical tabular serialization is UTF-8, LF-only CSV, gap-major ordering, and
finite floats formatted as signed scientific notation with 17 digits after the
decimal point. Manifests use sorted-key UTF-8 JSON. Every file receives a
SHA-256 hash. Repeated executions must produce byte-identical canonical files.

## Work packages and controls

Exactly ten work packages and fifteen execution controls are prepared and
unexecuted. The controls cover four production-routed benchmarks, five
mutations, symmetry/phase behavior, two torque cross-checks, convergence,
serialization reproducibility, and Jacobian identifiability.

## Packet-review outcomes

```text
DETERMINISTIC_FORWARD_MODEL_VALIDATION_CONTRACT_READY
BLOCKED_HARMONIC_CONVENTION_INCOMPLETE
BLOCKED_PRODUCTION_KERNEL_VALIDATION
BLOCKED_TORQUE_DERIVATIVE_CONTRACT
BLOCKED_GEOMETRY_OR_SYMMETRY_FAILURE
BLOCKED_NUMERICAL_CONVERGENCE
BLOCKED_DETERMINISTIC_NUISANCE_MAPPING
BLOCKED_PARAMETER_IDENTIFIABILITY
BLOCKED_SCOPE_OR_PROVENANCE
```

The independent review must select exactly one. Acceptance authorizes one
bounded deterministic execution only after a separate authority transition.

## Preparation result

All 30 preparation controls pass. No work package, benchmark, mutation,
convergence check, Jacobian, or output has been executed or produced.

```text
Stage A packet:
PREPARED_PENDING_INDEPENDENT_REVIEW

work packages:
0 / 10 EXECUTED

execution controls:
0 / 15 EXECUTED

deterministic vectors:
0 PRODUCED

Gaussian noise:
NONE

Monte Carlo:
NONE

Stage B:
DEFERRED / NOT AUTHORIZED

current authority:
review_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v0_result
```
