# ToE Candidate Master Action v0

Spec ID:
- `TOE_CANDIDATE_MASTER_ACTION_v0`

Classification:
- `P-POLICY`

Purpose:
- Provide a disciplined, explicit candidate master action in one place.
- Keep the candidate bounded and non-canonical while consolidation work continues.
- Define a common object surface for cross-pillar bridge/transport work.

Non-claim boundary:
- working-form artifact only.
- explicitly non-canonical.
- does not assert external truth by itself.
- does not assert uniqueness by itself.
- does not promote theorem labels by itself.
- does not replace any pillar-local derivation target by itself.

Canonical anchors:
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`

## Candidate action surface (working-form)

Let fields and objects be `g, psi, A, phi, rho` with seam constraints `C_k`.

```
S_ToE[g, psi, A, phi, rho]
= integral d^4x sqrt(-g) [
    (1/(16*pi*G)) * (R - 2*Lambda)
  + sum_a psi_bar_a * (i*gamma^mu*D_mu - m_a) * psi_a
  - (1/4) * F_{mu nu} * F^{mu nu}
  + (1/2) * sum_i nabla_mu(phi_i) * nabla^mu(phi_i)
  - V(phi)
  + lambda_stat * rho * (ln(rho) - 1)
  + sum_k lambda_k * C_k(g, psi, A, phi, rho)
]
```

Stationarity condition:

```
delta S_ToE = 0
```

This yields coupled equation families for geometry, matter, gauge, auxiliary/scalar, and statistical-state surfaces under explicit assumptions.

## Term map (v0 interpretation)

1. Gravity/geometry term:
- `(1/(16*pi*G)) * (R - 2*Lambda)`.
- intended as Einstein-Hilbert-type bounded surface.

2. Matter/fermion term:
- `sum_a psi_bar_a * (i*gamma^mu*D_mu - m_a) * psi_a`.
- intended as QFT/QM matter-evolution surface.

3. Gauge term:
- `-(1/4) * F_{mu nu} * F^{mu nu}`.
- intended as EM/gauge-field surface.

4. Scalar/structure term:
- `(1/2) * sum_i nabla_mu(phi_i) * nabla^mu(phi_i) - V(phi)`.
- intended as bounded structure and transition support surface.

5. Statistical/information term:
- `lambda_stat * rho * (ln(rho) - 1)`.
- explicitly speculative in v0.

6. Seam-constraint term:
- `sum_k lambda_k * C_k(...)`.
- encodes cross-pillar compatibility, bridge admissibility, and transport consistency constraints.

## Derivation-chain alignment

This candidate is aligned to the standardized chain:
- `ACTION`: this document's `S_ToE` surface.
- `VARIATION`: `delta S_ToE = 0` under frozen assumptions.
- `BRIDGE`: route-level witness constructors per pillar/lane.
- `OPERATOR`: operator equations produced from bridge-valid variation outputs.
- `TRANSPORT`: theorem transport from operator surfaces to residual forms.
- `RESIDUAL_LAW`: law-like residual equations in bounded scope.
- `REGIME_LIMIT`: weak-field / non-relativistic / classical / statistical regime projections.

## Sequencing posture (v0)

1. Mathematical consolidation:
- run now, continuously.
- maintain bounded scope and explicit assumptions.

2. Computational testing:
- run now in shadow/non-authoritative lanes.
- use for falsification pressure and stability diagnostics.

3. Prediction derivation:
- start as soon as residual-law surfaces stabilize enough to define discriminator outputs.

4. Empirical comparison:
- begin after initial stabilization, overlapping with M3 discriminator lanes.

## Promotion prerequisites (toward canonical action)

This working-form may be promoted only after all are explicit:
- cross-pillar seam constraints are theorem-linked and assumption-minimized.
- bridge-to-operator transport is closed for admitted pillars.
- regime-limit projections are synchronized with discriminator artifacts.
- anti-circularity and no-shortcut guards are discharged at bounded scope.

## Compact layered form (physics-facing working view)

Equivalent compact writing for discussion and derivation planning:

```
S_master = integral d^4x sqrt(-g) [
  L_geometry
  + L_field
  + L_interaction
  + L_transport
  + L_entropy
  + L_seam
]
```

with the v0 mapping:

- `L_geometry` -> Einstein-Hilbert-type geometry block.
- `L_field` -> matter and gauge kinetic blocks.
- `L_interaction` -> covariant couplings and potential terms.
- `L_transport` -> operator-to-residual transport-support structure.
- `L_entropy` -> bounded statistical term (`rho ln rho` family).
- `L_seam` -> explicit seam constraints `C_k` with multipliers `lambda_k`.

This compact form is interpretive and must remain algebraically tied to the explicit `S_ToE` surface above.

## Regime-reading guide (bounded, non-promotional)

Use the same parent action and emphasize different dominant blocks by regime:

1. Geometry-dominant regime:
- prioritize `L_geometry + L_seam` and weak-field residual projections.

2. Quantum/operator-dominant regime:
- prioritize `L_field + L_interaction + L_transport` and operator closure routes.

3. Thermodynamic/coarse-grained regime:
- prioritize `L_entropy + L_transport` with residual-law statistics checks.

4. Cosmology/background regime:
- prioritize `L_geometry + L_field + L_seam` under large-scale background assumptions.

Interpretation constraint:
- regime emphasis is a derivation lens, not a claim of independent underlying laws.
