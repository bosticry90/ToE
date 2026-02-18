# Assumption Registry v1

Spec ID:
- `ASSUMPTION_REGISTRY_v1`

Classification:
- `P-POLICY`

Purpose:
- Provide one canonical assumption ledger for paper-facing theorem surfaces.
- Classify assumptions by role so theorem claims remain auditable and non-diffuse.
- Link each theorem surface to explicit assumption IDs.

Non-claim boundary:
- This registry is a bookkeeping/control artifact.
- This registry does not promote theorem status by itself.
- This registry does not substitute for derivations, proofs, or external validation.

## Taxonomy Classes

- `STRUCTURAL`: typed object/interface assumptions required to state the theorem.
- `REGIME`: domain/regime constraints (for example weak-field or low-amplitude scope).
- `APPROXIMATION`: truncation/order/scaling assumptions used for reduced forms.
- `SYMMETRY`: invariance and action-compatibility assumptions.
- `BOUNDARY`: boundary/extension/support conditions.
- `NORMALIZATION`: positivity, sum-to-one, or gauge/normalization conditions.
- `CALIBRATION`: parameter-fit and lock-pinned calibration assumptions.

## Canonical Assumption Table

| Assumption ID | Class | Status | Surface | Statement (short) | Canonical pointer |
|---|---|---|---|---|---|
| `ASM-QM-EVOL-STR-01` | `STRUCTURAL` | `T-CONDITIONAL` | `qm_evolution_under_contract_assumptions` | Typed evolution context `EvolutionContext Time State` is explicit in theorem signature. | `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` |
| `ASM-QM-EVOL-STR-02` | `STRUCTURAL` | `T-CONDITIONAL` | `qm_evolution_under_contract_assumptions` | Explicit time binder `t : Time` and typed states `QMState State` are explicit theorem inputs. | `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` |
| `ASM-QM-EVOL-APP-01` | `APPROXIMATION` | `P-POLICY` | `TOE-QM-01` | Contract theorem remains non-derivational (no Schrodinger derivation claim, no unitary recovery claim). | `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md` |
| `ASM-EM-U1-STR-01` | `STRUCTURAL` | `T-CONDITIONAL` | `em_u1_field_strength_invariance_under_contract_assumptions_v0` | Differential bundle uses explicit partial-vector additivity over componentwise sums in the Cycle-002 theorem route. | `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean` |
| `ASM-EM-U1-SYM-01` | `SYMMETRY` | `T-CONDITIONAL` | `em_u1_field_strength_invariance_under_contract_assumptions_v0` | Gauge-scalar second-partial commutativity is explicit for cancellation in the Cycle-002 invariance theorem route. | `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean` |
| `ASM-GR01-STR-01` | `STRUCTURAL` | `T-CONDITIONAL` | `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions` | Discrete/operator transport lemma `OperatorToDiscreteResidual` is theorem-level bookkeeping support. | `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean` |
| `ASM-GR01-REG-01` | `REGIME` | `T-CONDITIONAL` | `gr01_regime_predicate_under_uniform_bound` | Weak-field regime is theorem-conditional via explicit bound predicate (`WeakFieldRegimePredicate`). | `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean` |
| `ASM-GR01-REG-02` | `REGIME` | `P-POLICY` | `gr01_discrete_residual_from_bridge_promotion_chain` | Uniform weak-field bound for potential/source is explicit in bridge-promotion theorem assumptions. | `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean` |
| `ASM-GR01-APP-01` | `APPROXIMATION` | `T-CONDITIONAL` | `gr01_first_order_truncation_sound` | First-order weak-field scaling/truncation is theorem-conditional via explicit scaling and remainder bounds (`WeakFieldScalingHierarchy`, `HigherOrderTermsNegligible`). | `formal/toe_formal/ToeFormal/Variational/GR01ScalingPromotion.lean` |
| `ASM-GR01-APP-03` | `APPROXIMATION` | `P-POLICY` | `gr01_discrete_residual_from_bridge_promotion_chain` | First-order remainder suppression is explicit in bridge-promotion theorem assumptions. | `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean` |
| `ASM-GR01-SYM-01` | `SYMMETRY` | `T-CONDITIONAL` | `gr01_projection_map_well_formed` | Projection-map well-formedness is theorem-conditional via explicit carrier/regime predicate (`ProjectionMapWellFormedPredicate`). | `formal/toe_formal/ToeFormal/Variational/GR01SymmetryPromotion.lean` |
| `ASM-GR01-BND-01` | `BOUNDARY` | `P-POLICY` | `TOE-GR-01` | Periodic/discrete boundary and extension conventions are fixed for the GR01 derivation scaffold. | `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md` |
| `ASM-GR01-NRM-01` | `NORMALIZATION` | `P-POLICY` | `TOE-GR-01` | Potential/source identification conventions are explicit in scoped notes. | `formal/docs/paper/TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md` |
| `ASM-GR01-CAL-01` | `CALIBRATION` | `E-REPRO` | `TOE-GR-01` | Kappa calibration is deterministic, lock-pinned support evidence only. | `formal/docs/paper/TOE_GR01_KAPPA_CALIBRATION_v0.md` |
| `ASM-GR01-APP-02` | `APPROXIMATION` | `T-CONDITIONAL` | `gr01_discrete_residual_from_bridge_promotion_chain` | Modeling bridge is theorem-conditional under explicit strengthened assumptions (`WeakFieldUniformBound`, `FirstOrderRemainderSuppressed`, `ELImpliesOperatorResidualUnderBound`). | `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean` |
| `ASM-GR01-APP-04` | `APPROXIMATION` | `P-POLICY` | `gr01_discrete_residual_from_bridge_promotion_chain` | Operator-residual bridge under weak-field bound is explicit (`ELImpliesOperatorResidualUnderBound`). | `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean` |
| `ASM-GR01-CONS-01` | `STRUCTURAL` | `T-CONDITIONAL` | `gr01_conservation_compatibility_from_bridge_promotion_chain_v0` | Conservation compatibility uses an explicit bridge composition from GR01 discrete residual closure into flux/divergence/source compatibility. | `formal/toe_formal/ToeFormal/GR/ConservationContract.lean` |
| `ASM-GR01-CONS-02` | `REGIME` | `T-CONDITIONAL` | `gr01_conservation_compatibility_from_bridge_promotion_chain_v0` | Conservation compatibility inherits weak-field bridge assumptions (`WeakFieldUniformBound`, `FirstOrderRemainderSuppressed`, `ELImpliesOperatorResidualUnderBound`) without widening scope. | `formal/toe_formal/ToeFormal/GR/ConservationContract.lean` |

## GR01 Promotion Intent

Registry intent labels:
- `intended theorem-level`: targeted for future `T-CONDITIONAL` discharge.
- `intended policy-level permanent`: expected to remain explicit policy assumptions in v1 scope.
- `support-only permanent`: expected to remain `E-REPRO` support surfaces.

Intent map:
- `ASM-GR01-STR-01`: already theorem-level (`T-CONDITIONAL`).
- `ASM-GR01-REG-01`: promoted theorem-level (`T-CONDITIONAL`) via regime-promotion chain.
- `ASM-GR01-REG-02`: intended theorem-level.
- `ASM-GR01-APP-01`: promoted theorem-level (`T-CONDITIONAL`) via scaling-promotion chain.
- `ASM-GR01-APP-03`: intended theorem-level.
- `ASM-GR01-APP-04`: intended theorem-level.
- `ASM-GR01-SYM-01`: promoted theorem-level (`T-CONDITIONAL`) via symmetry-promotion chain.
- `ASM-GR01-APP-02`: promoted theorem-level (`T-CONDITIONAL`) via bridge-promotion chain.
- `ASM-GR01-CONS-01`: promoted theorem-level (`T-CONDITIONAL`) via conservation bridge-composition token.
- `ASM-GR01-CONS-02`: promoted theorem-level (`T-CONDITIONAL`) via conservation compatibility promotion token.
- `ASM-GR01-BND-01`: intended policy-level permanent.
- `ASM-GR01-NRM-01`: intended policy-level permanent.
- `ASM-GR01-CAL-01`: support-only permanent (`E-REPRO`).

Bridge promotion target pointer:
- `formal/docs/paper/DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md`

Regime promotion target pointer:
- `formal/docs/paper/DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md`

Scaling promotion target pointer:
- `formal/docs/paper/DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md`

Symmetry promotion target pointer:
- `formal/docs/paper/DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md`

End-to-end closure target pointer:
- `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`

## Theorem-Surface Assumption Index

- `qm_evolution_under_contract_assumptions`:
  - `ASM-QM-EVOL-STR-01`
  - `ASM-QM-EVOL-STR-02`
  - `ASM-QM-EVOL-APP-01`
- `em_u1_field_strength_invariance_under_contract_assumptions_v0`:
  - `ASM-EM-U1-STR-01`
  - `ASM-EM-U1-SYM-01`
- `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions`:
  - `ASM-GR01-STR-01`
  - `ASM-GR01-REG-01`
  - `ASM-GR01-APP-01`
  - `ASM-GR01-SYM-01`
  - `ASM-GR01-BND-01`
  - `ASM-GR01-NRM-01`
  - `ASM-GR01-CAL-01`
  - `ASM-GR01-APP-02`
- `gr01_discrete_residual_from_bridge_promotion_chain`:
  - `ASM-GR01-REG-02`
  - `ASM-GR01-APP-03`
  - `ASM-GR01-APP-04`
- `gr01_regime_predicate_under_uniform_bound`:
  - `ASM-GR01-REG-01`
  - `ASM-GR01-REG-02`
- `gr01_first_order_truncation_sound`:
  - `ASM-GR01-APP-01`
  - `ASM-GR01-APP-03`
- `gr01_projection_map_well_formed`:
  - `ASM-GR01-SYM-01`
- `gr01_end_to_end_chain_bundle_under_promoted_assumptions`:
  - `ASM-GR01-REG-01`
  - `ASM-GR01-APP-01`
  - `ASM-GR01-SYM-01`
  - `ASM-GR01-APP-02`
  - `ASM-GR01-REG-02`
  - `ASM-GR01-APP-03`
  - `ASM-GR01-APP-04`
- `gr01_end_to_end_poisson_equation_under_promoted_assumptions`:
  - `ASM-GR01-REG-01`
  - `ASM-GR01-APP-01`
  - `ASM-GR01-SYM-01`
  - `ASM-GR01-APP-02`
  - `ASM-GR01-REG-02`
  - `ASM-GR01-APP-03`
  - `ASM-GR01-APP-04`
- `gr01_conservation_compatibility_from_bridge_promotion_chain_v0`:
  - `ASM-GR01-CONS-01`
  - `ASM-GR01-CONS-02`
  - `ASM-GR01-APP-02`
  - `ASM-GR01-REG-02`
  - `ASM-GR01-APP-03`
  - `ASM-GR01-APP-04`

## Registry Discipline

- Every new paper-facing theorem surface must list at least one assumption ID here.
- Claim/paper/state surfaces must reference assumption IDs, not only prose assumptions.
- Promotion to `T-CONDITIONAL` requires explicit theorem-signature assumptions plus registry linkage.
