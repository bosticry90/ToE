# Lean Axiom / Spec-Backed Ledger v0

Spec ID:
- `LEAN_AXIOM_SPEC_BACKED_LEDGER_v0`

Classification:
- `P-POLICY`

Purpose:
- Track real Lean `axiom`, `sorry`, and `admit` proof-debt surfaces while excluding comments.
- Distinguish spec-backed support assumptions from blockers against full pillar target mapping.
- Make green Lean builds readable as "build green with declared assumptions", not derivation completeness.

Non-claim boundary:
- This ledger does not discharge any axiom.
- This ledger does not upgrade any theorem claim.
- This ledger does not authorize Phase 2, seam closure, empirical claim, or master-action promotion.

Allowed statuses:

```text
live_blocking
live_nonblocking
retained_assumption
historical
quarantine
spec_backed
candidate_for_removal
```

Required fields:
- `declaration`
- `file`
- `status`
- `reason`
- `associated_pillar_or_seam`
- `blocks_full_pillar_target`
- `replacement_or_discharge_path`

Baseline:
- `real_axiom_count_v0: 60`
- `real_sorry_or_admit_count_v0: 0`
- `real_axiom_file_count_v0: 15`

## Ledger Rows

| declaration | file | status | reason | associated_pillar_or_seam | blocks_full_pillar_target | replacement_or_discharge_path |
| --- | --- | --- | --- | --- | --- | --- |
| `Dt_planeWave` | `formal/toe_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorAxioms.lean` | `spec_backed` | Plane-wave operator convention used by bounded CPNLSE numerics. | `SCALAR_QFT` | `no` | Replace with concrete differentiability and plane-wave evaluation theorem. |
| `Delta_planeWave` | `formal/toe_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorAxioms.lean` | `spec_backed` | Plane-wave Laplacian convention used by bounded CPNLSE numerics. | `SCALAR_QFT` | `no` | Replace with concrete Laplacian plane-wave theorem. |
| `DxxR_zero` | `formal/toe_formal/ToeFormal/CRFT/PhiChi1DExtended.lean` | `spec_backed` | CRFT derivative-zero simplification for a retained model surface. | `SCALAR_QFT` | `no` | Replace with concrete derivative calculation. |
| `DxxxxR_zero` | `formal/toe_formal/ToeFormal/CRFT/PhiChi1DExtended.lean` | `spec_backed` | CRFT higher-derivative simplification for a retained model surface. | `SCALAR_QFT` | `no` | Replace with concrete derivative calculation. |
| `DxxxxxxR_zero` | `formal/toe_formal/ToeFormal/CRFT/PhiChi1DExtended.lean` | `spec_backed` | CRFT sixth-derivative simplification for a retained model surface. | `SCALAR_QFT` | `no` | Replace with concrete derivative calculation. |
| `bogoliubov_linearization_from_P1_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B1_P1_to_UCFF_FirstOrderDispersion.lean` | `retained_assumption` | Bridge-level linearization spec, not a derived theorem. | `SCALAR_QFT` | `yes` | Prove bridge from explicit P1 parent dynamics and perturbation semantics. |
| `Dt_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B1_P1_to_UCFF_FirstOrderDispersion.lean` | `spec_backed` | Derivative-symbol agreement spec for B1 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `Dxx_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B1_P1_to_UCFF_FirstOrderDispersion.lean` | `spec_backed` | Second-derivative symbol agreement spec for B1 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `Dxxxx_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B1_P1_to_UCFF_FirstOrderDispersion.lean` | `spec_backed` | Fourth-derivative symbol agreement spec for B1 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `Dxxxxxx_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B1_P1_to_UCFF_FirstOrderDispersion.lean` | `spec_backed` | Sixth-derivative symbol agreement spec for B1 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `P1_eom_implies_P1Residual_as_UCFF_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B1_P1_to_UCFF_FirstOrderDispersion.lean` | `retained_assumption` | P1 equation-to-residual bridge remains spec-backed. | `SCALAR_QFT` | `yes` | Prove from parent equation semantics and residual definition. |
| `Dtt_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B2_P2_to_UCFF_SecondOrderTimeDomain.lean` | `spec_backed` | Second-time derivative agreement spec for B2 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `Dxx_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B2_P2_to_UCFF_SecondOrderTimeDomain.lean` | `spec_backed` | Second-space derivative agreement spec for B2 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `Dxxxx_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B2_P2_to_UCFF_SecondOrderTimeDomain.lean` | `spec_backed` | Fourth-derivative agreement spec for B2 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `Dxxxxxx_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B2_P2_to_UCFF_SecondOrderTimeDomain.lean` | `spec_backed` | Sixth-derivative agreement spec for B2 bridge. | `SCALAR_QFT` | `no` | Replace with imported Fourier-symbol theorem. |
| `cubicDensity_agrees_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B2_P2_to_UCFF_SecondOrderTimeDomain.lean` | `retained_assumption` | Cubic density agreement is bridge-spec-backed. | `SCALAR_QFT` | `yes` | Prove from concrete nonlinear density semantics. |
| `omega_sq_matches_P2_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B3_P2_to_UCFF_SecondOrderNumerics.lean` | `retained_assumption` | Numeric dispersion matching is spec-backed. | `SCALAR_QFT` | `yes` | Prove from P2 dispersion relation and numerical symbol definitions. |
| `B4_CRFT_to_AcousticMetric_spec` | `formal/toe_formal/ToeFormal/Derivation/Bridges/B4_CRFT_to_AcousticMetric.lean` | `retained_assumption` | CRFT-to-acoustic metric bridge is a spec statement. | `GR_QM` | `yes` | Prove from CRFT dynamics plus acoustic metric construction. |
| `Dx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Conventions/FourierSymbols.lean` | `spec_backed` | Fourier derivative convention. | `SCALAR_QFT` | `no` | Replace with concrete Fourier-symbol lemma. |
| `Dxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Conventions/FourierSymbols.lean` | `spec_backed` | Fourier second-derivative convention. | `SCALAR_QFT` | `no` | Replace with concrete Fourier-symbol lemma. |
| `Dxxxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Conventions/FourierSymbols.lean` | `spec_backed` | Fourier fourth-derivative convention. | `SCALAR_QFT` | `no` | Replace with concrete Fourier-symbol lemma. |
| `Dxxxxxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Conventions/FourierSymbols.lean` | `spec_backed` | Fourier sixth-derivative convention. | `SCALAR_QFT` | `no` | Replace with concrete Fourier-symbol lemma. |
| `Dt_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Conventions/FourierSymbols.lean` | `spec_backed` | Fourier time-derivative convention. | `SCALAR_QFT` | `no` | Replace with concrete Fourier-symbol lemma. |
| `Dtt_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Conventions/FourierSymbols.lean` | `spec_backed` | Fourier second-time-derivative convention. | `SCALAR_QFT` | `no` | Replace with concrete Fourier-symbol lemma. |
| `Dt_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P1_NLS_EFT.lean` | `spec_backed` | P1 parent time derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `Dxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P1_NLS_EFT.lean` | `spec_backed` | P1 parent spatial second derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `Dxxxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P1_NLS_EFT.lean` | `spec_backed` | P1 parent fourth derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `Dxxxxxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P1_NLS_EFT.lean` | `spec_backed` | P1 parent sixth derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `P1_rhs_matches_EFT` | `formal/toe_formal/ToeFormal/Derivation/Parents/P1_NLS_EFT.lean` | `retained_assumption` | Parent P1 RHS-to-EFT match remains supplied. | `SCALAR_QFT` | `yes` | Prove from explicit EFT parent action and residual definitions. |
| `Dtt_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P2_Wave_EFT.lean` | `spec_backed` | P2 parent second-time derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `Dxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P2_Wave_EFT.lean` | `spec_backed` | P2 parent second-space derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `Dxxxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P2_Wave_EFT.lean` | `spec_backed` | P2 parent fourth derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `Dxxxxxx_planeWave` | `formal/toe_formal/ToeFormal/Derivation/Parents/P2_Wave_EFT.lean` | `spec_backed` | P2 parent sixth derivative convention. | `SCALAR_QFT` | `no` | Replace by importing canonical Fourier convention theorem. |
| `P2_rhs_matches_EFT` | `formal/toe_formal/ToeFormal/Derivation/Parents/P2_Wave_EFT.lean` | `retained_assumption` | Parent P2 RHS-to-EFT match remains supplied. | `SCALAR_QFT` | `yes` | Prove from explicit EFT parent action and residual definitions. |
| `formalFirstVariationRep32_zero_variation_at` | `formal/toe_formal/ToeFormal/Variational/ActionToFirstVariationBridgeRep32.lean` | `retained_assumption` | First-variation bridge algebra is still axiomatized. | `SCALAR_QFT` | `yes` | Replace with theorem over concrete first-variation representation. |
| `formalFirstVariationRep32_add_variation_at` | `formal/toe_formal/ToeFormal/Variational/ActionToFirstVariationBridgeRep32.lean` | `retained_assumption` | Additivity of the first-variation bridge is axiomatized. | `SCALAR_QFT` | `yes` | Replace with theorem over concrete first-variation representation. |
| `formalFirstVariationRep32_smul_variation_at` | `formal/toe_formal/ToeFormal/Variational/ActionToFirstVariationBridgeRep32.lean` | `retained_assumption` | Scalar compatibility of the first-variation bridge is axiomatized. | `SCALAR_QFT` | `yes` | Replace with theorem over concrete first-variation representation. |
| `kinetic` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `spec_backed` | Declared action term placeholder. | `MASTER_ACTION` | `no` | Replace with concrete structured action term when promoted. |
| `dispersion` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `spec_backed` | Declared action term placeholder. | `MASTER_ACTION` | `no` | Replace with concrete structured action term when promoted. |
| `coherence` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `spec_backed` | Declared action term placeholder. | `MASTER_ACTION` | `no` | Replace with concrete structured action term when promoted. |
| `wK` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `spec_backed` | Declared coefficient placeholder. | `MASTER_ACTION` | `no` | Replace with concrete parameter source when promoted. |
| `wD` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `spec_backed` | Declared coefficient placeholder. | `MASTER_ACTION` | `no` | Replace with concrete parameter source when promoted. |
| `wC` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `spec_backed` | Declared coefficient placeholder. | `MASTER_ACTION` | `no` | Replace with concrete parameter source when promoted. |
| `declared_g` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `spec_backed` | Declared geometry object placeholder. | `MASTER_ACTION` | `no` | Replace with concrete geometry source when promoted. |
| `EL_toe` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Euler-Lagrange equation of the declared action is axiomatized. | `MASTER_ACTION` | `yes` | Derive from concrete action and variation theorem. |
| `firstVariation` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | First variation of the declared action is axiomatized. | `MASTER_ACTION` | `yes` | Replace with concrete first-variation construction. |
| `declaredELAssumptions` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | EL assumptions remain declared, not derived. | `MASTER_ACTION` | `yes` | Derive from regularity, boundary, and variation assumptions. |
| `declaredSymmetry` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Symmetry structure remains declared. | `MASTER_ACTION` | `yes` | Prove from action invariance. |
| `declaredSemigroupWithGenerator` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Semigroup/generator structure remains declared. | `MASTER_ACTION` | `yes` | Prove from explicit transformation group. |
| `declaredQuantity` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Conserved quantity remains declared. | `MASTER_ACTION` | `yes` | Derive through Noether-style theorem surface. |
| `declaredNoetherAssumptions` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Noether assumptions remain declared. | `MASTER_ACTION` | `yes` | Prove or discharge against concrete symmetry/action data. |
| `declaredKineticInvariant` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Kinetic invariance remains declared. | `MASTER_ACTION` | `yes` | Derive from transformation action on terms. |
| `declaredDispersionInvariant` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Dispersion invariance remains declared. | `MASTER_ACTION` | `yes` | Derive from transformation action on terms. |
| `declaredCoherenceInvariant` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Coherence invariance remains declared. | `MASTER_ACTION` | `yes` | Derive from transformation action on terms. |
| `declaredSymmetryMatchesPhase` | `formal/toe_formal/ToeFormal/Variational/DeclaredAction.lean` | `retained_assumption` | Symmetry-to-phase matching remains declared. | `MASTER_ACTION` | `yes` | Prove by concrete symmetry representation. |
| `Rep` | `formal/toe_formal/ToeFormal/Variational/FieldRepresentation.lean` | `spec_backed` | Abstract field representation universe. | `SCALAR_QFT` | `no` | Replace only if a concrete universal representation is selected. |
| `Rep_on_samples_delta_one` | `formal/toe_formal/ToeFormal/Variational/FieldRepresentationSample.lean` | `spec_backed` | Sample representation convention for delta-one. | `SCALAR_QFT` | `no` | Replace with concrete sample representation theorem. |
| `Rep_on_samples_delta_I` | `formal/toe_formal/ToeFormal/Variational/FieldRepresentationSample.lean` | `spec_backed` | Sample representation convention for delta-I. | `SCALAR_QFT` | `no` | Replace with concrete sample representation theorem. |
| `P_rep` | `formal/toe_formal/ToeFormal/Variational/FirstVariationRepDefFieldRep.lean` | `retained_assumption` | Field representation polynomial remains declared. | `SCALAR_QFT` | `yes` | Derive from concrete representation selection. |
| `sampleRep32` | `formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01.lean` | `spec_backed` | Sample representation witness for non-alias equivalence. | `SCALAR_QFT` | `no` | Replace with concrete sample representation theorem. |
