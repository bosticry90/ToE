# Shared Linearized Quadratic-Gravity Source and Spectrum Comparison Packet Review v0

Date: 2026-07-18  
Target: `review_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0_result`  
Verdict: `ACCEPTED_FOR_ONE_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_COMPARISON_EXECUTION`  
Selected next target: `execute_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0`

## Outcome

The packet is accepted for exactly one bounded comparison execution. It freezes
one action normalization, one external conserved-source convention, one metric
variation and operator-inversion path, and one Green-function path for both 00
and 0i outputs. It does not preload any field equation, mode, pole, residue, or
Green function.

```text
independent review gates:       15 / 15 PASSED
authorized executions:          1
derivation stages completed:     0 / 10
mode judgments:                  0 / 3
physical outputs:                0 / 11
shared-path controls executed:   0 / 10
comparison-action adoption:      NONE
native gravitational principle: NOT IDENTIFIED
```

Acceptance authorizes the comparison derivation only. It does not adopt the
action or authorize orbital, empirical, matter-sector, or master-action work.

## Independent reproduction

The review froze the packet's human record, structured JSON, generator, focused
tests, and Lean surface by SHA-256. It then independently reproduced the
dimension and source-normalization algebra rather than accepting the printed
`kappa` field.

With dimensions ordered as `(M,L,T)`, the frozen constants give

```text
[c]       = (0, 1,-1)
[G]       = (-1,3,-2)
[A_EH]    = [c^3/G] = (1,0,-1)
[d^4x]    = (0,4,0) because x^0=ct
[R]       = (0,-2,0)
[T_mu_nu] = (1,-1,-2)

[A_EH d^4x R] = (1,2,-1) = J s
[(1/c)d^4x T] = (1,2,-1) = J s.
```

For the frozen inverse-metric variation,

```text
delta S_g   = A_EH integral H_mu_nu delta g^mu_nu,
delta S_ext = -(1/(2c)) integral T_mu_nu delta g^mu_nu.
```

Stationarity therefore gives

```text
A_EH H_mu_nu - (1/(2c)) T_mu_nu = 0,

H_mu_nu
  = [1/(2c A_EH)] T_mu_nu
  = [1/(2c)] [16 pi G/c^3] T_mu_nu
  = (8 pi G/c^4) T_mu_nu.
```

The sign and coefficient are internally coherent. This check does not supply
the still-uncomputed tensor `H_mu_nu`.

## Primary comparator spot-checks

- [Hindawi, Ovrut, and Waldram](https://arxiv.org/abs/hep-th/9509142) support using massless gravity, a massive scalar, and a massive spin-2 field as expected comparison questions, while also supplying a flat-space ghost oracle in their stated canonical treatment. The packet correctly records no mode as present before derivation.
- [Stabile](https://arxiv.org/abs/1007.1917) supports the two-scale fourth-order weak-field comparison and the relevance of the Gauss–Bonnet relation. The packet limits its reduction to four-dimensional compact-support local-bulk equations.
- [Berry and Gair](https://arxiv.org/abs/1104.0819) support treating analytic `R+alpha R^2` as a scalar-mode comparison representative, not as a whole-family or project result.
- [Iyer and Wald](https://arxiv.org/abs/gr-qc/9403028) support the general covariant variational/Noether setting, but the packet does not use that literature to manufacture its external source or final equation.

These are post-derivation oracles. They are not executable inputs.

## Fifteen review gates

### G1 — Exact authority and custody: PASS

The packet consumes the accepted survey-result review and current authority
names this packet review. All five preparation artifacts match the frozen
hashes recorded by the review tool.

### G2 — Immutable comparison-only status: PASS

All packet surfaces bind the action as a supplied comparison family, not a ToE
candidate, successor master action, native postulate, or adopted theory. A
successful execution cannot mutate those labels.

### G3 — Common normalization and SI dimensions: PASS

The independent calculation above reproduces action dimensions. Because the
common factor `c^3/(16 pi G)` multiplies all three curvature terms, both `alpha`
and `beta` have dimension `m^2`. They remain exact symbolic parameters.

### G4 — External-source sign and coefficient: PASS

The independent stationarity calculation reproduces the positive
`kappa=8 pi G/c^4` coefficient. The source is defined only through its first
variation at Minkowski, is nondynamical, and obeys supplied
`partial_mu T^mu_nu=0`. It is not a nonlinear matter action or ToE stress tensor.

### G5 — Four-dimensional Gauss–Bonnet scope: PASS

From

```text
E_4=Riemann^2-4 Ricci^2+R^2,
```

the packet's map

```text
alpha_reduced=alpha_unreduced-gamma,
beta_reduced=beta_unreduced+4 gamma
```

is algebraically correct. Transport is prohibited for boundary charges,
boundary actions, global topology, arbitrary boundary conditions, other
dimensions, and nonlocal theories.

### G6 — Minkowski admitted but still execution-gated: PASS

The exact comparison action has no cosmological term. At zero source,
Minkowski has vanishing Riemann, Ricci, scalar curvature, and curvature
derivatives, so it is structurally admissible for every symbolic `alpha,beta`.
The executor must nevertheless derive the exact Euler tensor and pass D4 before
constructing a propagator; this review does not mark D4 complete.

### G7 — Linearization exact in the couplings: PASS

The gravitational action must be expanded through `O(h^2)` and the equation
through `O(h)`, while `alpha,beta` remain exact. No small-coupling truncation is
allowed. Heavy-mode and small-coupling limits occur only as derived controls.

### G8 — Curvature, Fourier, and boundary conventions: PASS

The Riemann/Ricci signs, `(+,-,-,-)` signature, `x^0=ct`, `Box`, Fourier pair,
derivative symbol, stationary inverse transform, and spatial decay condition are
explicit and mutually consistent with the repository plane-wave convention.

### G9 — Gauge fixing preserves the mode question: PASS

De Donder gauge fixes diffeomorphism redundancy only. The packet requires the
complete longitudinal Barnes–Rivers sectors during inversion and removes them
only after saturation with a conserved source. It does not assume that the
Einstein trace-reversed equation diagonalizes the higher-derivative operator.

### G10 — No preloaded modes or literature formulas: PASS

All three mode rows say `TO_BE_DERIVED`; all ten derivation stages are
`NOT_EXECUTED`; all eleven outputs are `NOT_COMPUTED`. Literature comparison is
permitted only after the internally normalized equation and propagator exist.

### G11 — Pole and residue semantics: PASS WITH BINDING CLARIFICATION

The packet requires conserved-source saturation and distinguishes ghost,
tachyon, classical instability, matter instability, and heavy decoupling. For
execution, the following operational rule is now binding:

> At each simple physical pole, first decompose the conserved-source saturated
> amplitude into the frozen spin-2 or scalar projector channel. After factoring
> out the common positive `G`/source normalization, report the pole residue
> relative to the positive Einstein massless-spin-2 reference for a normalized
> physical polarization/source channel. A repeated, merged, or non-diagonalizable
> pole receives no sign label until a limiting or diagonalized analysis resolves
> it.

This clarification makes the residue test reproducible without preassigning its
answer.

### G12 — One operator supplies 00 and 0i: PASS

D8–D10 require one gauge-fixed operator, one projector inversion, and one
conserved-source saturated response. Both stationary Green functions must be
components of that shared object. Importing separate Newtonian and current
formulas is prohibited.

### G13 — Retarded, pole-reporting, and static roles are disjoint: PASS

The full classical operator uses the retarded continuation; Feynman `+i0` is a
pole-orientation/residue reporting label; stationary responses use the decaying
spatial inverse. Growing Yukawa branches and mid-derivation convention switches
are prohibited.

### G14 — Ten shared-path controls are sufficient and unrun: PASS

The Einstein, beta-zero, current-zero, current-sign, source-conservation,
heavy-mode, derived-degeneracy, gauge-sector, dimensional, and Gauss–Bonnet
controls all traverse the main derivation. None has been executed, and no
coefficient fitting is allowed.

### G15 — One execution and hard stop: PASS

The packet does not authorize a second run, theory adoption, coefficient
selection, empirical constraints, orbital averaging, precession, Lense–Thirring,
LARES-2, a matter sector, a native principle, a new postulate, or master-action
mutation. Execution must stop for independent result review.

## One-execution authorization contract

Acceptance authorizes exactly one execution of the ten frozen derivation stages
and ten controls under the following additional gates:

1. Hash and revalidate the accepted packet before any symbolic variation.
2. Treat `alpha,beta` as exact real parameters with units `m^2`.
3. Keep the external source first-order, supplied, symmetric, and conserved.
4. Pass D1–D7 before any projector inversion.
5. Pass the Minkowski background check before defining momentum-space poles.
6. Derive the complete gauge-fixed operator and then saturate with conserved sources.
7. Apply the operational residue rule from G11.
8. Derive 00 and 0i from the same saturated operator and Fourier convention.
9. Execute all ten controls through the same path; fail closed on any control failure.
10. Compare with literature only after derivation and record every convention translation.
11. Emit all eleven prepared outputs or a localized blocked result.
12. Stop at `review_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0_result`.

The execution may produce comparison findings about pole structure and source
response. Every such finding remains `SUPPLIED_COMPARISON_RESULT`, not a ToE
claim.

## Acceptance does not authorize

- action adoption or coefficient selection;
- empirical fitting or modified-gravity constraints;
- orbital averaging, precession, frame dragging, or LARES-2;
- nonlinear backreaction or a covariant matter completion;
- a ToE-native stress tensor, gravitational principle, or postulate;
- master-action construction or mutation;
- V2 matrix population or automated theory selection.

## Current posture

```text
comparison packet:             ACCEPTED
authorized executions:         1
derivation stages:              0 / 10
mode judgments:                0 / 3
physical outputs:              0 / 11
shared-path controls:           0 / 10
comparison action:             SUPPLIED COMPARISON ONLY
native gravitational principle:NOT IDENTIFIED
gravitational action:          NOT SELECTED
frame dragging:                NOT RESUMED
selected next authority:
execute_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0
```
