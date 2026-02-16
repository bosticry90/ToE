# TOE-GR-01 Canonical Equivalence Theorem v0

Spec ID:
- `TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0`

Claim token:
- `TOE-GR01-EQUIV-01`

Classification:
- `T-CONDITIONAL`

Purpose:
- Pin the canonical-equivalence discharge surface for GR01 under the current discrete weak-field scope.
- Make the canonical equation form explicit as a theorem-level endpoint under stated assumptions.
- Prevent narrative-only "equivalence" wording from replacing auditable theorem tokens.

Canonical discrete equation string (frozen):
- `DiscreteLaplacian1D Φ i = κ * ρ i`

Theorem anchors:
- `PoissonEquation1D`
- `DiscreteLaplacian1D`
- `DiscretePoissonResidual1D`
- `poissonEquation1D_iff_discreteLaplacian1D_eq_kappa_rho`
- `PoissonEquation3D`
- `DiscreteLaplacian3D`
- `DiscretePoissonResidual3D`
- `poissonEquation3D_iff_discreteLaplacian3D_eq_kappa_rho`
- `gr01_end_to_end_poisson_equation_under_promoted_assumptions`

Discharge statement (v0 discrete canonical-equivalence layer):
- Under the promoted GR01 assumption bundle used by
  `gr01_end_to_end_poisson_equation_under_promoted_assumptions`,
  canonical discrete Poisson form is obtained by composing:
  - end-to-end Poisson residual closure (`PoissonEquation1D`), and
  - equivalence lemma `poissonEquation1D_iff_discreteLaplacian1D_eq_kappa_rho`.
- This discharges the v0 canonical-equivalence theorem layer for the discrete operator form.

Status:
- canonical-equivalence theorem status: `DISCHARGED` (discrete canonical form only).

Scope boundary:
- finite/discrete weak-field theorem surface only.
- no continuum-limit theorem is claimed.
- no infinite-domain Green-function inversion is claimed.
- no uniqueness/Sobolev-class PDE theorem is claimed.
- 3D equivalence token is discrete/operator-form only and does not by itself discharge mainstream-class 3D gate criteria.
- does not by itself close `TOE-GR-3D-03`.

Artifact pointers:
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
