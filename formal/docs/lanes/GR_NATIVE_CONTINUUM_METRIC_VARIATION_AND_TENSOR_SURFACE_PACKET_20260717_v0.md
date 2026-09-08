# GR Native Continuum Metric Variation and Tensor Surface Packet v0

Packet ID:

`GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0`

Status:

`PREPARED_PENDING_INDEPENDENT_REVIEW`

Consumed target:

`prepare_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0`

Next target:

`review_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0_result`

## 1. Exact scientific question

Does the project possess one sufficiently defined, project-authorized continuum
gravitational action whose genuine gravitational-variable variation can produce
a tensor field equation without importing the Einstein equation as an
assumption?

This packet specifies an existence-and-contract review. It does not execute a
metric or tetrad variation.

## 2. Sole action candidate under review

The only candidate action source admitted for the native route is:

`formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`

Exact source ID:

`TOE_CANDIDATE_MASTER_ACTION_v0`

Source classification:

`TOE_NATIVE_CANDIDATE / WORKING_FORM / NONCANONICAL / UNPROMOTED`

Variational-readiness classification before review:

`UNADJUDICATED_PENDING_INDEPENDENT_REVIEW`

The source must be reviewed byte-exactly. Terms may not be inserted, removed,
renormalized, or reclassified during review merely to make variation possible.

The following surfaces are comparison or structural authorities only and may
not be blended into the selected action:

| Surface | Frozen classification | Native-action use |
| --- | --- | --- |
| `ActionRep32` | `STRUCTURAL_SCAFFOLD` | Forbidden as continuum metric-action authority |
| `firstVariationRep32` | `DECLARED_COMPARISON_PAIRING` | Forbidden as analytic action variation |
| `DocumentMasterActionMapping` | `BOUNDED_FREE_SCALAR_TRANSLATION` | Forbidden as global metric variation |
| Provisional Einstein-scalar route | `PROVISIONAL_STANDARD_GR_SANDBOX` | Comparator only |
| Standalone Einstein-Hilbert action | `STANDARD_GR_SUPPLIED_SECTOR` | Comparator classification only unless independently selected later |

The fact that the selected working form contains an Einstein-Hilbert-shaped
term does not by itself classify the full candidate as a complete continuum
metric functional.

## 3. Gravitational variable and spinor gate

The full candidate includes Dirac spinors. Therefore a metric-symbol-only
variation is not accepted as a full-candidate variation.

The proposed full-candidate route for independent review selects the covariant
tetrad

`e^a_mu`

as the independent gravitational variable, with

`g_mu_nu = eta_ab e^a_mu e^b_nu`.

The proposed bounded formulation is second-order, torsion-free tetrad gravity:

- the tetrad is invertible and oriented;
- a spin structure and spinor bundle must be specified;
- curved gamma matrices obey `gamma^mu = e_a^mu gamma^a`;
- the spin connection is the metric-compatible torsion-free connection
  `omega_mu^{ab}(e)` and is not independently varied;
- local Lorentz covariance must be stated;
- spinor components, gauge covectors, scalars, and statistical variables held
  fixed during tetrad variation must be named exactly;
- the Dirac Lagrangian must be fixed as a real/Hermitian action density, with
  its relation to the source's unsymmetrized shorthand made explicit.

If those objects are not authorized by the bound source, the exact result is:

`BLOCKED_SPINOR_METRIC_VARIATION_SURFACE`

A metric-only variation may review an explicitly restricted bosonic subaction,
but it cannot be reported as variation of the full candidate.

## 4. Continuum domain and units gate

Before variation, review must bind:

- a four-dimensional oriented Lorentzian manifold `M`;
- signature `(+,-,-,-)` and retained `x^0=ct` convention;
- differentiability and nondegeneracy classes for the tetrad and metric;
- field bundles and admissible configurations for every retained sector;
- one action-unit convention in which all retained integrand terms have the
  same dimensions.

The selected source writes coefficients in a natural-unit-like shorthand while
the retained dimensionful target is SI. The review may not insert `c`, `hbar`,
`mu_0`, reference density scales, or sector rescalings without classifying them
as supplied structure. Failure to close the common action dimension produces:

`BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT`

## 5. Complete gravitational-dependence ledger

Every row is mandatory. An unlisted or hidden tetrad/metric dependence blocks
variation.

| Sector | Required dependence to expose | Preparation finding to review |
| --- | --- | --- |
| Geometry | `e=sqrt(-g)`, `R[e,omega(e)]`, `Lambda`, curvature regularity | Einstein-Hilbert-shaped term present; continuum/domain/unit contract incomplete |
| Dirac | `e`, `gamma^mu(e)`, `omega(e)`, spinor adjoint, covariant derivative, Hermitian density | tetrad/spin structure and exact real density not selected in the source |
| Gauge | `e`, inverse metrics in `F_mu_nu F^mu_nu`, orientation if duals appear | field contraction present; SI normalization and bundle/domain not fixed by source |
| Scalar | `e`, inverse metric, scalar covariant derivative, potential | field inventory, regularity, potential, and common units incomplete |
| Statistical | `e`, whether `rho` is scalar or density, dimensionless logarithm argument, reference measure | explicitly speculative and underdefined |
| Seam family `C_k` | no action dependence permitted under current policy | source displays multiplier embedding; conflicts with retained firewall |

No stress tensor may be imported to stand in for a missing dependence row.

## 6. Boundary contract

The only bounded boundary route proposed by this packet is a local bulk
variation with compactly supported tetrad variations:

`delta e^a_mu in C_c^infinity(interior(M))`.

This makes total-divergence terms vanish in the local field-equation test and
does not claim a globally well-posed finite-boundary variational principle.

The packet does not add a Gibbons-Hawking-York term. Any later finite-boundary
route must separately select a boundary action, fixed boundary data, corner
terms where required, and compatible matter boundary conditions.

Silently discarding curvature or spinor boundary terms is forbidden.

## 7. Matter source definition

For any independently authorized metric-only subroute, the required Hilbert
definition is

`T_mu_nu = -(2/sqrt(-g)) delta S_m / delta g^{mu nu}`.

For the selected covariant-tetrad route, the required source definition is

`tau_a^mu = (1/e) delta S_m / delta e^a_mu`

with the consistency target

`tau_a^mu = T^{mu nu} e_{a nu}`

after local-Lorentz and symmetry obligations are discharged.

Previously retained `T_A`, `T_psi`, or `T_total` objects are comparison policies
only. Their existing review explicitly does not derive them by metric or tetrad
variation. They cannot be inserted as if this derivation had occurred.

## 8. Mandatory C_k firewall

Current accepted policy is:

`C_k = ADMISSIBILITY / AUDIT ONLY`.

Therefore:

- no `C_k` functional is varied;
- no multiplier field is introduced or varied;
- no `C_k` term contributes to gravitational or matter sources;
- no penalty dynamics is inferred;
- no seam rule is promoted to a dynamical law.

The exact selected action source still displays

`sum_k lambda_k C_k(g,psi,A,phi,rho)`.

This is a registered source-policy conflict, not permission to delete the term.
Independent review must either classify the selected source as incomplete or
identify a pre-existing authoritative resolution. The packet itself performs
no action rewrite.

## 9. Rep32 relationship gate

The currently supported classification is:

`SEPARATE_STRUCTURAL_MODEL / CONTINUUM_RELATION_UNESTABLISHED`.

`ActionRep32` declares a structural action and assigned comparison operator;
`firstVariationRep32` is defined through a pairing. The source explicitly leaves
analytic derivation of that first variation from the action open.

No theorem currently establishes that Rep32 is a discretization, reduction, or
convergent approximation of the selected continuum candidate. The previous
GR master-action transport retry ended with

`GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT`.

Review must reject any continuum authority inferred from shared action
terminology alone.

## 10. Fail-fast independent-review order

Review must stop at the first failed gate:

1. `ACTION_SOURCE_IDENTITY_FAILURE`
2. `ACTION_SOURCE_BLENDING_FAILURE`
3. `CK_FIREWALL_ACTION_SOURCE_CONFLICT`
4. `ACTION_DIMENSION_AND_CONSTANT_CLOSURE_FAILURE`
5. `CONTINUUM_DOMAIN_AND_FIELD_BUNDLE_FAILURE`
6. `BLOCKED_SPINOR_METRIC_VARIATION_SURFACE`
7. `HIDDEN_METRIC_DEPENDENCE_FAILURE`
8. `BOUNDARY_VARIATION_CONTRACT_FAILURE`
9. `STRESS_ENERGY_VARIATIONAL_DEFINITION_FAILURE`
10. `REP32_CONTINUUM_RELATIONSHIP_FAILURE`
11. `EINSTEIN_EQUATION_IMPORT_OR_ORACLE_LEAKAGE`

Passing a later gate cannot repair an earlier failure.

## 11. Allowed review outcomes

Exactly one outcome is permitted:

1. `NATIVE_CONTINUUM_METRIC_VARIATION_CONTRACT_READY`
2. `BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT`
3. `NO_NATIVE_CONTINUUM_METRIC_ACTION_SURFACE`
4. `SUPPLIED_STANDARD_GR_VARIATIONAL_COMPARATOR_ONLY`
5. `BLOCKED_SPINOR_METRIC_VARIATION_SURFACE`

The first outcome authorizes only a separately reviewed variation attempt. It
does not assert a tensor equation or GR recovery.

## 12. Independent-review acceptance criteria

An accepted readiness result requires all of the following:

- the sole action source and every exclusion reproduce byte-exactly;
- no action-source blending occurs;
- the chosen covariant tetrad route is complete and authorized;
- every retained term has closed field, domain, unit, and tetrad dependence;
- the compact-support boundary contract is sufficient for the claimed local
  bulk result;
- stress energy is defined by the selected variational route;
- the `C_k` conflict is resolved by pre-existing authority, not packet editing;
- Rep32 is not used beyond its established structural authority;
- the Einstein equation and provisional sandbox never enter as native inputs;
- no actual variation or downstream gravitomagnetic work occurred.

## 13. Hard stop and nonclaims

This packet authorizes independent review only.

It performs no:

- metric or tetrad variation;
- stress-energy calculation;
- Einstein-equation import or derivation;
- standard-GR comparator activation;
- weak-field or `0i` reduction;
- frame-dragging calculation;
- `C_k` embedding or variation;
- action rewrite or promotion;
- repository migration;
- simulation, empirical analysis, or automation.

Maximum claim:

> One exact candidate action, a proposed tetrad-route contract, complete
> readiness gates, five terminal outcomes, and strict nonclaims have been
> prepared for independent review. No continuum tensor field surface has been
> established.
