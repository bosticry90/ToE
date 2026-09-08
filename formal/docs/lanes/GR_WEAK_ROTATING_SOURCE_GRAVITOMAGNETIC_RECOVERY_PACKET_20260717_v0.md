# GR Weak Rotating-Source Gravitomagnetic Recovery Packet v0

Packet ID:
- `GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0`

Classification:
- `PREPARED_PENDING_INDEPENDENT_REVIEW`
- `BOUNDED_GR_KNOWN_PHYSICS_RECOVERY_CONTRACT`
- `NO_DERIVATION_EXECUTED`

Consumed target:
- `prepare_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0`

Next target, and no other:
- `review_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0_result`

## Question

Under the frozen stationary, weak-field, slow-rotation, compact-source,
exterior, gauge, boundary, and orbital assumptions, can the project GR sector
derive the leading gravitomagnetic metric component and Lense-Thirring nodal
precession without importing or fitting their coefficients?

The required transport is

```text
project GR action/equation surface
-> tensor 0i field equation
-> T_0i mass-current source
-> exterior g_0i current dipole
-> test-particle perturbation
-> secular orbital-node rate.
```

This packet freezes that calculation. It does not perform it.

## Exact project-source boundary

The future derivation must begin from these actual project surfaces:

1. `formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean`
   - exact object: `actionRep32 : ActionRep32Scaffold`;
   - present claim: structural action scaffold;
   - explicit limitation: the analytic derivation of `firstVariationRep32` from
     an action functional remains open.
2. `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
   - exact objects: `WeakFieldPoissonLimitStatement3D`,
     `UnitsAndCalibration.h_kappa_relation`, and the bounded discrete residual
     route;
   - present claim: bounded/discrete Newtonian Poisson recovery under explicit
     assumptions;
   - explicit limitation: not a continuum tensor or Einstein-equation result.
3. `formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`
   - exact boundary: bounded/discrete weak-field v0 only;
   - no continuum limit, uniqueness, or infinite-domain inversion promotion;
   - the blocker inventory remains binding.

The future calculation must therefore first show that the selected project
surface supplies, or validly transports to, a continuum tensor metric equation.
It must not substitute the standard linearized Einstein equation and then call
that substitution a derivation from the project sector. Failure at this first
step is the registered result `FIELD_EQUATION_SURFACE_FAILURE`.

## Retained convention policy

The packet does not reopen the closed SR tooling lane. It freezes the retained
policy directly:

```text
x^0 = c t
eta_mu_nu = diag(+1,-1,-1,-1)
dimensionful target = SI
g_mu_nu = eta_mu_nu + h_mu_nu
|h_mu_nu| << 1
spatial component labels use the Euclidean three-vector convention
```

Indices on four-dimensional objects are raised and lowered only with the
frozen Minkowski metric at linear order. In particular, for the leading
slow-source current,

```text
T^{0i} = c j_m^i + higher order,
T_{0i} = -c j_{m i} + higher order,
j_m = rho_m v.
```

## Approximation and source freeze

Required regime:

- stationary source: `partial_0 T_mu_nu = 0` at retained order;
- retained source conservation `partial_mu T^{mu nu} = 0`, required for
  compatibility with harmonic gauge;
- isolated, spatially compact source of radius `R_s`;
- exterior evaluation point `r > R_s`;
- weak field, first order in `h_mu_nu`;
- slow internal motion `epsilon_v = |v|/c << 1`;
- retain terms linear in source angular momentum `J`;
- neglect radiation, retardation, and time derivatives at retained order;
- asymptotic flatness in asymptotically Cartesian mass-centered coordinates;
- stationary localized mass-current conservation `nabla dot j_m = 0`, derived
  as the leading slow-source continuity consequence;
- mass-centered origin `integral rho_m x d^3x = 0`;
- zero-total-momentum rest frame `integral j_m d^3x = 0`;
- retain the mass monopole only as the nonrotating orbital background and the
  current dipole `J` as the rotational perturbation;
- discard the mass dipole, higher current multipoles, spin-squared terms,
  higher post-Newtonian terms, and source deformations;
- internal stresses `T^{ij}` and pressure are not used to manufacture the
  leading `0i` current-dipole coefficient; any contribution claimed at the
  retained order must be separately derived and power counted.

Angular momentum is frozen as

```text
J = integral x cross j_m(x) d^3x.
```

The future multipole step must derive, rather than assume, the antisymmetric
current-moment reduction from stationary current conservation, compact support,
and integration by parts. In the frozen three-vector orientation its target
identity is

```text
integral j_{m i} x'_j d^3x' = -(1/2) epsilon_ijk J_k.
```

## Gauge and boundary freeze

The comparison convention is trace-reversed harmonic gauge:

```text
hbar_mu_nu = h_mu_nu - (1/2) eta_mu_nu h,
h = eta^{alpha beta} h_alpha_beta,
partial^mu hbar_mu_nu = 0.
```

The residual harmonic-gauge freedom is `box xi_mu = 0`; in the stationary slice,
`nabla^2 xi_mu = 0`. The future derivation must impose regularity and asymptotic
decay and use an asymptotically Cartesian mass-centered harmonic representative.
A residual transformation may not be used to insert, remove, or renormalize the
leading current-dipole coefficient. Since `eta_0i = 0`, the comparison
representative satisfies `hbar_0i = h_0i = g_0i` at linear order.

Boundary conditions:

- the perturbation vanishes at spatial infinity;
- the exterior rotational solution contains no growing or nondecaying
  homogeneous mode;
- the solution is matched to a localized stationary source;
- the Poisson Green normalization used for the oracle comparison is
  `nabla^2(1/|x-x'|) = -4 pi delta^3(x-x')`.

## Independently frozen recovery oracles

Every expression in this section is an
`INDEPENDENT_RECOVERY_ORACLE_NOT_DERIVATION_INPUT`. A future derivation may see
these values only after it has emitted its own canonical result and provenance.
They may be used for comparison, never for coefficient selection, calibration,
normalization, or intermediate rewriting.

With the retained signature and `x^0=ct`, the standard-GR comparison chain is:

```text
box hbar_mu_nu = -(16 pi G / c^4) T_mu_nu,
box = (1/c^2) partial_t^2 - nabla^2,
nabla^2 hbar_0i = +(16 pi G / c^4) T_0i              [stationary],
hbar_0i(x) = -(4 G / c^4) integral T_0i(x')/|x-x'| d^3x',
g_0i^rot(x) = +(2 G / c^3) (J cross r)_i / r^3.
```

For `J = J z_hat`, an ascending-node convention oriented right-handed about
`+z`, and osculating Kepler elements `(a,e)`, the signed nodal oracle is

```text
dot(Omega)_LT = +(2 G J)/(c^2 a^3 (1-e^2)^(3/2)).
```

The sign is part of the frozen coordinate, source-orientation, and node
convention. The invariant control is that reversing `J` reverses both the
rotational metric term and the nodal contribution.

## Authorized future derivation route

After an independent packet review accepts the contract, one bounded
calculation may attempt these stages:

1. Starting-surface stage: derive or justify the continuum tensor field
   equation from the exact project GR source binding. Imported Einstein
   equations are forbidden as project-derived results.
2. Linearization stage: form the trace-reversed first-order equation and its
   `0i` stationary component using the retained signature.
3. Source stage: derive the leading slow-source relation between `T^{0i}`,
   `T_{0i}`, and `j_m`; state all discarded orders.
4. Green/multipole stage: solve with the frozen boundary conditions and expand
   the compact current source through the angular-momentum dipole.
5. Metric stage: extract the computed `g_0i` without consulting its coefficient
   oracle.
6. Orbital stage: start from `S_pp = -m c integral ds`, expand consistently to
   first order in the rotational perturbation and the required slow-orbit
   order, isolate the `J`-dependent disturbing term, average over one Kepler
   orbit using a derived or independently checked
   `<r^-3> = a^-3 (1-e^2)^(-3/2)`, and derive the secular nodal rate.
7. Comparison stage: only after stages 1-6 are frozen, compare the computed
   metric and orbital coefficients with the independent oracles.

No numerical orbit integration is authorized.

## Required controls

The future calculation must execute these eight controls through the same
derivation path:

1. `ZERO_ANGULAR_MOMENTUM`: `J=0` removes `g_0i^rot` and the rotational nodal
   contribution.
2. `ANGULAR_MOMENTUM_SIGN_REVERSAL`: `J -> -J` reverses both signs without
   changing their magnitudes.
3. `WRONG_SOURCE_COMPONENT`: replacing `T_0i` by `T_00` cannot reproduce the
   current-dipole rotational field.
4. `MIXED_METRIC_COMPONENT_REMOVAL`: setting the rotational `g_0i` components
   to zero destroys the Lense-Thirring term.
5. `WRONG_GREEN_NORMALIZATION`: a deliberately wrong Green coefficient changes
   the derived metric coefficient and fails oracle comparison.
6. `SIGNATURE_MIX`: importing a `(-,+,+,+)` sign rule without a complete
   conversion fails `SIGNATURE_CONVENTION_MISMATCH` before comparison.
7. `COEFFICIENT_FIT_ATTEMPT`: using the oracle or observational value to set an
   intermediate coefficient fails `RECOVERY_COEFFICIENT_FITTING_FORBIDDEN`.
8. `NONDECAYING_EXTERIOR_MODE`: retaining a growing or nondecaying rotational
   exterior mode fails `ASYMPTOTIC_FLATNESS_BOUNDARY_FAILURE`.

## Result classes

Maximum success result:
- `BOUNDED_GR_ROTATING_WEAK_FIELD_RECOVERY_CANDIDATE_PENDING_RESULT_REVIEW`.

Success means only that, under every frozen premise, the project route derived
the standard leading `g_0i` current-dipole coefficient and signed nodal
coefficient without fitting. It does not become accepted until a separate
result review.

Failure results:

- `FIELD_EQUATION_SURFACE_FAILURE`: no valid project-action/equation route to a
  continuum tensor `0i` equation;
- `SOURCE_IDENTIFICATION_FAILURE`: inconsistent `T^{0i}`, `T_0i`, mass-current,
  or angular-momentum identification;
- `FIELD_EQUATION_NORMALIZATION_OR_SIGN_FAILURE`: wrong stationary `0i`
  normalization or sign;
- `EXTERIOR_CURRENT_DIPOLE_FAILURE`: wrong exterior structure, coefficient, or
  boundary behavior;
- `OBSERVABLE_TRANSPORT_FAILURE`: acceptable metric stage but wrong orbital
  nodal coefficient or sign;
- `SUPPLIED_TARGET_OR_COEFFICIENT_DEPENDENCE`: the desired result was imported,
  fitted, or used as an intermediate premise.

Any failure is a scientifically usable bounded obstruction. It must not be
repaired by fitting or by replacing the project source with the oracle.

## Independent-review acceptance criteria

The packet review must verify:

```text
selected authority and exact project bindings: PASS
retained coordinate/signature/SI convention: PASS
project surface versus standard-GR oracle separation: PASS
stationary weak slow-rotation regime: CLOSED
T^{0i}/T_0i/current/J definitions and power counting: CLOSED
trace reversal, harmonic gauge, residual gauge, and boundaries: CLOSED
metric coefficient oracle isolated from derivation inputs: PASS
nodal coefficient oracle isolated from derivation inputs: PASS
orbital derivation route and orientation convention: CLOSED
eight controls: ATOMIC AND REQUIRED
failure classification: COMPLETE
derivation, fitting, simulation, and empirical comparison now: NOT EXECUTED
```

An accepted packet review may authorize one bounded analytic derivation on
these frozen surfaces. It may not authorize empirical analysis or migration.

## Hard stop and nonclaims

This packet does not authorize or claim:

- the derivation itself;
- coefficient fitting or calibration;
- satellite or LARES-2 data processing;
- empirical validation or a modified-gravity bound;
- numerical orbit integration;
- a Kerr derivation or strong-field result;
- a complete post-Newtonian framework;
- Earth gravity-field or multipole modeling beyond the frozen compact-source
  current dipole;
- general symbolic tensor infrastructure;
- repository-wide convention migration;
- full GR recovery or GR-pillar completion;
- gravitational radiation;
- QFT-GR or any other seam closure;
- candidate master-action validation or promotion;
- activation of Gravity from Entropy or another comparator;
- reopening R13 or the SR restoration-tooling lane;
- an automation or literature watch.

Stopping rule:

> Freeze one source-to-field-to-orbit derivation contract, two independent
> coefficient oracles, eight controls, exact failure classes, and stop for
> independent packet review.
