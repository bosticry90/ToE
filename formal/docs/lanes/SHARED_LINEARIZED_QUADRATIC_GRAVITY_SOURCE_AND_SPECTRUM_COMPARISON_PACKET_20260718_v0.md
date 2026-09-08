# Shared Linearized Quadratic-Gravity Source and Spectrum Comparison Packet v0

Date: 2026-07-18  
Target: `prepare_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0`  
Verdict: `PREPARED_PENDING_INDEPENDENT_REVIEW`  
Selected next target: `review_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0_result`

## Preparation boundary

This packet freezes one possible comparison execution. It contains no metric
variation, linearized field equation, propagator, pole mass, residue, Green
function, or source response result.

```text
status:                    SUPPLIED COMPARISON FAMILY
ToE adoption:              NONE
native principle:          NONE
candidate-action authority:NONE
comparison execution:      NOT AUTHORIZED
metric variation:          NOT EXECUTED
```

The action below is simultaneously classified as:

```text
COMPARISON ACTION FAMILY
NOT A TOE CANDIDATE
NOT A SUCCESSOR MASTER ACTION
NOT A NATIVE POSTULATE
```

A future successful control or calculation cannot promote it. Any execution
requires independent acceptance of this packet and must itself stop for an
independent result review.

## 1. Exact supplied comparison action

Use coordinates `x^mu = (x^0,x^i)` with `x^0 = c t`, so `d^4x` has SI dimension
`m^4`. Freeze

```text
A_EH  := c^3 / (16 pi G)
kappa := 8 pi G / c^4

S_g^cmp[g;alpha,beta]
  := A_EH integral_Omega d^4x sqrt(-g)
       [R + alpha R^2 + beta R_mu_nu R^mu_nu].
```

Parameters and dimensions:

```text
c > 0                 [m s^-1]
G > 0                 [m^3 kg^-1 s^-2]
A_EH                   [kg s^-1]
R, R_mu_nu             [m^-2]
alpha, beta in Real    [m^2]
g_mu_nu, h_mu_nu       dimensionless
S_g^cmp                 [J s]
```

`alpha` and `beta` remain exact symbolic comparison parameters. They are not
observational fits, project coefficients, or small perturbation parameters. The
comparison sets the cosmological term to zero solely so Minkowski space can be
the common background.

Term provenance:

- `R`: supplied Einstein–Hilbert comparator.
- `R^2`: supplied scalar-curvature quadratic comparator, including the bounded analytic-f(R) representative.
- `R_mu_nu R^mu_nu`: supplied generic local metric quadratic comparator carrying the additional spin-2 question.
- No term is derived from a ToE seam, Ck rule, matter sector, or master action.

Primary orientation sources include [Stelle's classical higher-derivative analysis](https://doi.org/10.1007/BF00760427), [Hindawi–Ovrut–Waldram's canonical field-content analysis](https://arxiv.org/abs/hep-th/9509142), [Berry–Gair's analytic f(R) linearization](https://arxiv.org/abs/1104.0819), and [Stabile's general fourth-order Newtonian analysis](https://arxiv.org/abs/1007.1917). These sources are post-derivation oracles, not substitutes for the required derivation.

## 2. External conserved comparison source

No `S_m` belonging to the ToE is asserted. Introduce a symmetric external
comparison source `T_mu_nu` only through its first variation at the background:

```text
delta S_ext |_eta
  := -(1/(2c)) integral d^4x T_mu_nu delta g^mu_nu,

equivalently at linear order,

S_ext^(1)[h;T]
  := +(1/(2c)) integral d^4x h_mu_nu T^mu_nu.
```

This normalization is frozen so stationarity of `S_g^cmp + S_ext` yields the
comparison equation normalization

```text
E_mu_nu^lin = kappa T_mu_nu,
kappa = 8 pi G / c^4,
```

after `E_mu_nu^lin` is actually derived. The equation itself is not supplied by
this packet.

Source contract:

```text
T_mu_nu = T_nu_mu
partial_mu T^mu_nu = 0
T_mu_nu has SI dimension J m^-3
T_mu_nu is externally supplied and nondynamical
```

For the stationary mass-density probe, define `rho := T_00/c^2` and require a
localized or distributionally controlled source. For the current probe, use the
covariant component `T_0i` exactly as written and require the full stationary
conservation condition. No project matter equation, stress-energy variation, or
matter-field content is inferred.

## 3. Four-dimensional quadratic basis and Gauss–Bonnet scope

The unreduced local quadratic basis is

```text
R^2,
R_mu_nu R^mu_nu,
R_mu_nu_rho_sigma R^mu_nu_rho_sigma.
```

In four dimensions define

```text
E_4 := R_mu_nu_rho_sigma R^mu_nu_rho_sigma
       - 4 R_mu_nu R^mu_nu
       + R^2.
```

For fixed topology and smooth compactly supported metric variations inside
`Omega compactly contained in M`, the bulk variation of
`integral sqrt(-g) E_4` vanishes. Thus a coefficient `gamma` multiplying
Riemann-squared can be reduced locally by

```text
gamma Riemann^2
  = gamma E_4 + 4 gamma Ricci^2 - gamma R^2,

alpha_reduced = alpha_unreduced - gamma,
beta_reduced  = beta_unreduced  + 4 gamma.
```

This is the only equivalence used to select the two-parameter quadratic basis.
It is limited to four-dimensional compact-support local-bulk equations. It does
not identify boundary charges, boundary actions, global topology, arbitrary
boundary conditions, non-four-dimensional theories, or nonlocal theories.

The independent review must reject this packet if it silently transports the
Gauss–Bonnet reduction beyond that domain.

## 4. Geometry, background, and perturbative order

Freeze

```text
eta_mu_nu = diag(+1,-1,-1,-1)
g_mu_nu   = eta_mu_nu + h_mu_nu
|h_mu_nu| << 1
indices on h and T raised/lowered with eta at linear order
Lambda = 0
```

Curvature convention:

```text
R^rho_{ sigma mu nu}
 := partial_mu Gamma^rho_{nu sigma}
    - partial_nu Gamma^rho_{mu sigma}
    + Gamma^rho_{mu lambda} Gamma^lambda_{nu sigma}
    - Gamma^rho_{nu lambda} Gamma^lambda_{mu sigma},

R_sigma_nu := R^rho_{ sigma rho nu},
R := g^sigma_nu R_sigma_nu.
```

Flat derivative and wave operator:

```text
partial^mu := eta^mu_nu partial_nu
Box := eta^mu_nu partial_mu partial_nu
     = c^-2 partial_t^2 - spatial_laplacian.
```

Order contract:

- Expand the gravitational action through `O(h^2)` to obtain the linear operator.
- Keep the source coupling through `O(h)`.
- Derive the field equation through `O(h)` and discard `O(h^2)` equation terms.
- Treat `alpha` and `beta` exactly; this is not an expansion in the couplings.
- Verify Minkowski with zero source is a background before inversion.

## 5. Fourier, gauge, and Green-function conventions

The four-dimensional Fourier pair is

```text
f(x) = integral d^4k/(2 pi)^4 exp[-i k_mu x^mu] f_tilde(k),
f_tilde(k) = integral d^4x exp[+i k_mu x^mu] f(x),

k_mu x^mu = k_0 x^0 - bold_k dot bold_x,
k_0 = omega/c,
exp[-i k.x] = exp[i(bold_k dot bold_x - omega t)],
partial_mu -> -i k_mu,
Box -> -k^2,
k^2 = (omega/c)^2 - |bold_k|^2.
```

This extends the repository derivation-layer plane-wave convention
`exp[i(kx-omega t)]` rather than creating a conflicting sign convention.

For stationary transforms (`omega=0`):

```text
f(bold_x) = integral d^3q/(2 pi)^3 exp[i bold_q dot bold_x] f_tilde(bold_q),
spatial_laplacian -> -q^2,
1/r and exp(-m r)/r kernels vanish at spatial infinity.
```

Gauge:

```text
h_bar_mu_nu := h_mu_nu - (1/2) eta_mu_nu h
F_nu := partial^mu h_bar_mu_nu
de Donder condition: F_nu = 0
gauge parameter: xi = 1
S_gf := -(A_EH/(2 xi)) integral d^4x F_nu F^nu
```

The executor must keep gauge-sector projectors until inversion and demonstrate
that the conserved-source saturated physical poles and residues are independent
of longitudinal gauge terms.

Boundary prescriptions:

- Classical time-dependent comparison: retarded prescription, represented in momentum space by the appropriate `+i0 k_0` continuation under the frozen Fourier sign.
- Pole/residue table: report the rational saturated propagator with the Feynman `+i0` labeling used only to identify pole orientation and residues.
- Stationary outputs: choose the unique spatial solution decaying at infinity; growing Yukawa branches are forbidden.

The two prescriptions must not be conflated.

## 6. Conserved-source projector basis

Away from a pole define

```text
theta_mu_nu := eta_mu_nu - k_mu k_nu/k^2,

P2_mu_nu,rho_sigma
 := (1/2)(theta_mu_rho theta_nu_sigma
          + theta_mu_sigma theta_nu_rho)
    - (1/3) theta_mu_nu theta_rho_sigma,

P0s_mu_nu,rho_sigma
 := (1/3) theta_mu_nu theta_rho_sigma.
```

The execution must define the remaining longitudinal Barnes–Rivers projectors
needed to invert the gauge-fixed operator, then show explicitly why they vanish
from the amplitude saturated with conserved sources. At the massless pole, the
projector result is interpreted through the conserved-source saturated limit;
no standalone singular `theta` expression may be treated as the observable.

## 7. Frozen derivation path — not executed

One shared derivation must perform these steps in order:

1. Start with the unreduced four-dimensional quadratic basis and prove the stated local-bulk Gauss–Bonnet reduction.
2. Vary the reduced metric action with respect to `g^mu_nu`, retaining all boundary terms until the compact-support condition removes them.
3. Record the exact comparison Euler tensor `E_mu_nu[g;alpha,beta]` and verify its covariant divergence identity.
4. Verify the zero-source Minkowski background for `Lambda=0`.
5. Set `g=eta+h` and derive `E_mu_nu^lin` to first order without importing the final formula.
6. Add the frozen external-source variation and confirm the normalization `E_mu_nu^lin=kappa T_mu_nu`.
7. Independently expand `S_g^cmp+S_gf` through quadratic order in `h` and show its Euler equation agrees with step 5.
8. Decompose and invert the quadratic operator in the complete spin-projector basis.
9. Saturate with conserved sources and derive all physical poles, residues, degeneracies, and source couplings.
10. Fourier-invert the same response for the stationary 00 and 0i channels.

Literature expressions may be compared only after the internally normalized
objects have been derived. A disagreement is a block, not permission to copy an
oracle result.

## 8. Mode, pole, and residue obligation register

The prepared register begins with zero judgments:

| Sector | Presence | Pole | Mass squared | Residue sign | Tachyon condition | Coupled source component |
|---|---|---|---|---|---|---|
| massless spin-2 | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED |
| massive scalar candidate | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED |
| massive spin-2 candidate | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED | TO_BE_DERIVED |

The execution must derive, rather than preassign:

- pole locations and masses in the frozen SI normalization;
- residues of the conserved-source saturated amplitude;
- tachyon-free parameter inequalities;
- every degenerate locus where poles merge or the operator loses rank;
- infinite-mass/decoupling limits and their order of limits;
- trace versus transverse current coupling;
- whether a formal mode is absent, infinitely heavy, weakly coupled, or merely unexcited by a chosen source.

Binding vocabulary:

```text
GHOST:
wrong-sign kinetic term or negative physical residue under the frozen treatment

TACHYON:
negative derived mass-squared under the frozen signature and pole convention

CLASSICAL_INSTABILITY:
growth or background/evolution instability established separately

MATTER_INSTABILITY:
instability requiring a specified matter environment or coupling

HEAVY_DECOUPLED_MODE:
mode remains formally present but its derived range/coupling suppresses the tested response
```

No one label may be substituted for another.

## 9. Prepared 00 and 0i output obligations

### Stationary 00 response

Derive from the shared saturated propagator:

```text
h_00[stationary conserved T_mu_nu]
```

and then specialize to a controlled mass-density source. The result must expose:

- the massless long-range `1/r` kernel;
- each scalar Yukawa kernel, if derived;
- each massive-spin-2 Yukawa kernel, if derived;
- tensor/source coefficients rather than only a named potential;
- dependence on `alpha` and `beta` through derived masses and residues;
- the exact `alpha=beta=0` Einstein limit.

### Stationary 0i response

Derive from the same operator and conventions:

```text
h_0i[stationary conserved T_mu_nu].
```

The result must state separately whether the scalar and massive spin-2 sectors
couple to `T_0i`, list long-range and Yukawa kernels, and retain exact index and
sign conventions. It stops at the field response: no orbital averaging,
precession, Lense–Thirring observable, or LARES-2 quantity is permitted.

## 10. Shared-path controls

Every control must use the same variation, linearization, gauge-fixed operator,
projector inversion, source saturation, and Fourier inversion as the main run.

| Control | Frozen mutation | Required behavior |
|---|---|---|
| C1_EH_BASELINE | `alpha=0, beta=0` | Derived equation normalization and 00/0i response match supplied linearized Einstein comparator. |
| C2_SCALAR_REPRESENTATIVE | `beta=0` | No generic massive spin-2 pole/correction; any scalar sector is derived, not presumed. |
| C3_CURRENT_ZERO | `T_0i=0` with a conserved stationary source | Current-sourced stationary `h_0i` contribution vanishes. |
| C4_CURRENT_SIGN | `T_0i -> -T_0i` | Linear stationary `h_0i -> -h_0i`. |
| C5_SOURCE_CONSERVATION | deliberately violate `partial_mu T^mu_nu=0` | Fail closed before interpreting a gauge-invariant saturated response. |
| C6_HEAVY_MODE_LIMIT | take each derived pole mass to infinity along a stated nonsingular parameter path | Corresponding Yukawa response decouples while formal mode status is reported accurately. |
| C7_DERIVED_SCALAR_DEGENERACY | use the scalar-decoupling/degenerate locus only after deriving it | Scalar pole behavior agrees between operator and Green-function routes. |
| C8_GAUGE_SECTOR | retain longitudinal projectors before conserved-source saturation | Physical conserved-source poles/residues do not depend on gauge-sector terms. |
| C9_DIMENSIONS_NORMALIZATION | audit every term and the EH limit | All action terms have units of action and the derived RHS coefficient is `kappa`. |
| C10_GAUSS_BONNET_LOCAL_BULK | compare unreduced and reduced bases under compact-support variation | Local bulk equations agree; no boundary/global claim is emitted. |

No coefficient may be chosen to force GR, eliminate a pole, reproduce a desired
frame-dragging sign, or satisfy an empirical bound.

## 11. Prepared outputs and fail-closed conditions

An accepted execution would be required to emit:

1. exact normalized action and source record;
2. Gauss–Bonnet local-bulk reduction proof;
3. exact metric Euler tensor and linearized equation;
4. quadratic gauge-fixed operator and projector decomposition;
5. conserved-source saturated propagator;
6. pole/mass/residue/tachyon/degeneracy table;
7. stationary 00 Green function and controlled mass-density specialization;
8. stationary 0i Green function and controlled current specialization;
9. all ten shared-path control results;
10. explicit comparison with literature oracles after derivation;
11. limitations and exact stopping statement.

Execution must fail closed if any of the following remains ambiguous:

- curvature, Fourier, gauge, source, or index sign convention;
- EH or source normalization;
- Gauss–Bonnet domain;
- treatment of a degenerate pole or noninvertible operator;
- source conservation;
- boundary or Green-function prescription;
- separation of ghost, tachyon, and other instability claims;
- inability to reproduce the Einstein control without coefficient fitting.

## 12. Hard stop and nonclaims

Packet preparation does not authorize:

- metric variation or linearized field-equation derivation;
- propagator, pole, residue, or Green-function computation;
- numerical or empirical coefficient fitting;
- modified-gravity parameter constraints;
- orbital averaging or precession;
- Lense–Thirring or LARES-2 analysis;
- matter-sector selection;
- comparison-family or action adoption;
- a native gravitational principle or new postulate;
- master-action construction or mutation;
- population of the closed V2 matrix;
- reopening automated action selection.

```text
comparison packet:       PREPARED_PENDING_INDEPENDENT_REVIEW
comparison execution:    NOT AUTHORIZED
real mode judgments:     NONE
real Green functions:    NONE
authoritative matrix:    0 / 70
selected next authority:
review_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0_result
```
