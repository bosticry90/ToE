# TOE Claim Surface v0

Spec ID:
- `TOE_CLAIM_SURFACE_v0`

Purpose:
- Freeze the exact claim surface for a future ToE-claim paper track.
- Prevent proxy/comparator surfaces from being mistaken for derivation-grade physics claims.
- Require a per-claim derivation plan before claim posture can be upgraded.
- Keep structural-coverage planning artifacts explicitly non-claim and non-promotional.

Claim posture policy:
- Every claim must declare a target equation/structure and a completion mode.
- Completion mode must be explicit for each claim:
  - theorem path (Lean)
  - analytic derivation
  - computational evidence
- Every claim must list which assumptions must be removed, promoted, or left as explicit postulates.
- No external truth claim is permitted on this surface.
- Planning-only coverage map:
  - `formal/docs/paper/STRUCTURAL_CLOSENESS_MAP_v0.md` (`P-POLICY`, non-claim, no status promotion).
- Authoritative physics-first roadmap (planning-only, no-deviation sequencing):
  - `formal/docs/paper/PHYSICS_ROADMAP_v0.md` (`P-POLICY`, non-claim, no status promotion).
- Assumption registry:
  - `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md` (`P-POLICY`, canonical taxonomy and assumption IDs).
- Frozen planning target (QM measurement semantics):
  - `formal/docs/paper/DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md` (`P-POLICY`, planning-only, no comparator-lane authorization).
- Frozen planning target (QM evolution object):
  - `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md` (`P-POLICY`, planning-only artifact retained after theorem-surface promotion checkpoint).
- Frozen planning target (QM symmetry object):
  - `formal/docs/paper/DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md` (`P-POLICY`, planning-only, no comparator-lane authorization).
- Frozen planning target (QFT evolution object):
  - `formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md` (`P-POLICY`, planning-only, no comparator-lane authorization).
- Frozen planning target (QFT gauge object):
  - `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md` (`P-POLICY`, planning-only, no comparator-lane authorization).
- Frozen planning target (GR geometry object):
  - `formal/docs/paper/DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md` (`P-POLICY`, planning-only, no comparator-lane authorization).
- Frozen planning target (GR conservation object):
  - `formal/docs/paper/DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md` (`P-POLICY`, planning-only, no comparator-lane authorization).
- Frozen planning target (GR01 bridge promotion):
  - `formal/docs/paper/DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md` (`P-POLICY`, blocker-focused planning-only target, no comparator-lane authorization).
- Frozen planning target (GR01 regime promotion):
  - `formal/docs/paper/DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md` (`P-POLICY`, blocker-focused planning-only target, no comparator-lane authorization).
- Frozen planning target (GR01 scaling promotion):
  - `formal/docs/paper/DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md` (`P-POLICY`, blocker-focused planning-only target, no comparator-lane authorization).
- Frozen planning target (GR01 symmetry promotion):
  - `formal/docs/paper/DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md` (`P-POLICY`, blocker-focused planning-only target, no comparator-lane authorization).
- Frozen planning target (GR01 end-to-end closure):
  - `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md` (`P-POLICY`, blocker-focused planning-only target, no comparator-lane authorization).

Selected first true derivation target:
- `TOE-GR-01` (Newtonian weak-field gravity limit).
- Target equation: `nabla^2 Phi = kappa * rho`.
- Upgrade intent: move from bounded correspondence to derivation-grade conditional theorem.

## Claim Surface Table

| Claim ID | Domain | Target Equation/Structure | Current posture | Core evidence pointer | Completion requirement |
|---|---|---|---|---|---|
| `TOE-QM-01` | Quantum sector | `i * d_t psi = H psi` (Schrodinger-form sector) | proxy/bounded lane + conditional contract theorem | `formal/docs/nonrelativistic_limit_nlse_lane_spec.md`; `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` | Promote theorem-surface assumptions with IDs and keep derivation/non-claim boundary explicit. |
| `TOE-SR-01` | Special relativity | Lorentz/Poincare invariance + transformation laws | proxy/bounded lanes | `formal/docs/rl12_lorentz_poincare_invariance_proxy_lane_spec.md` | Replace proxy-only checks with explicit invariance derivation path. |
| `TOE-GR-01` | Gravity (weak-field) | `nabla^2 Phi = kappa * rho` | bounded correspondence + theorem-surface scaffold | `formal/quarantine/physics_target/RL03_weak_field_poisson_v0_SPEC.md`; `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`; `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean` | First derivation target for promotion to derivation-grade conditional theorem. |
| `TOE-TH-01` | Thermodynamic balance | entropy production/balance structure | bounded correspondence | `formal/docs/rl10_entropy_balance_lane_spec.md` | Upgrade from bounded comparator semantics to derivation-grade statement with explicit regime limits. |

## Proof/Derivation Plan Per Claim

### TOE-QM-01
- theorem path (Lean): define a paper-facing theorem statement for the nonrelativistic sector under explicit assumptions.
- analytic derivation: state the approximation path from variational core to Schrodinger-form dynamics.
- computational evidence: retain existing bounded RL02 lane as reproducibility support only.
- assumptions to remove/promote: isolate which RAC/action-side assumptions are required for sector closure.
- promoted conditional theorem checkpoint:
  - `TOE-QM-THM-01` in `formal/docs/paper/RESULTS_TABLE_v0.md`
  - theorem surface: `qm_evolution_under_contract_assumptions`
  - assumption IDs: `ASM-QM-EVOL-STR-01`, `ASM-QM-EVOL-STR-02`, `ASM-QM-EVOL-APP-01`
  - registry pointer: `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- frozen evolution work-order target:
  - `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md`
  - contract-only Lean surface:
    `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
    (`qm_evolution_under_contract_assumptions`, `QMStateEvolvesUnderContract`;
    no Schrodinger derivation claim and no unitary dynamics recovery claim).
- frozen work-order target:
  - `formal/docs/paper/DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md`
  - contract-only Lean surface:
    `formal/toe_formal/ToeFormal/QM/MeasurementSemantics.lean`
    (`qm_measurement_weights_normalized_under_assumptions`, `Expectation`, `ExpectedObservable`,
    `expectation_add`, `expectation_smul`,
    `expectation_nonneg_of_nonneg_weights_and_observable`,
    `expected_observable_nonneg_of_support_nonneg`; no Born-rule claim).
- frozen symmetry work-order target:
  - `formal/docs/paper/DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md`
  - contract-only Lean surface:
    `formal/toe_formal/ToeFormal/QM/SymmetryContract.lean`
    (`qm_state_fixed_under_symmetry_contract_assumptions`, `StateFixedUnderSymmetryAction`;
    no QM interpretation claim).

### TOE-SR-01
- theorem path (Lean): encode invariance theorem surface with explicit transformation contracts.
- analytic derivation: provide derivation of transformation law and invariant interval/surrogate structure.
- computational evidence: retain RL12-RL16 as bounded stress tests only.
- assumptions to remove/promote: remove proxy-only reliance for core invariance claim.

### QFT planning-only work-order target
- frozen evolution work-order target:
  - `formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md`
  - contract-only Lean surface:
    `formal/toe_formal/ToeFormal/QFT/EvolutionContract.lean`
    (`qft_evolution_under_contract_assumptions`, `EvolvesUnderContract`;
    no Schrodinger/Dirac/Klein-Gordon derivation claim and no Standard Model dynamics claim).
- frozen work-order target:
  - `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md`
  - contract-only Lean surface:
    `formal/toe_formal/ToeFormal/QFT/GaugeContract.lean`
    (`qft_gauge_invariance_under_contract_assumptions`, `FieldFixedUnderGaugeAction`;
    no Standard Model claim).

### TOE-GR-01
- theorem path (Lean): derive a weak-field Poisson-form statement under explicit default-path assumptions.
- analytic derivation: map variational objects to potential/source structure in a constrained weak-field regime.
- computational evidence: RL03 lane remains bounded support evidence.
- assumptions to remove/promote: promote or explicitly classify action/RAC-side obligations used by this derivation.
- canonical assumption registry linkage:
  - `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- analytic discharge narrative:
  - `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- bridge promotion target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md`
  - bridge theorem surface:
    `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
    (`gr01_discrete_residual_from_bridge_promotion_chain`)
  - target ID: `TARGET-GR01-BRIDGE-PROMO-PLAN`
  - promoted bridge assumption ID: `ASM-GR01-APP-02` (`T-CONDITIONAL`)
- regime promotion target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md`
  - regime theorem surface:
    `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
    (`WeakFieldRegimePredicate`, `gr01_regime_predicate_under_uniform_bound`)
  - target ID: `TARGET-GR01-REG-PROMO-PLAN`
  - promoted regime assumption ID: `ASM-GR01-REG-01` (`T-CONDITIONAL`)
- scaling promotion target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md`
  - scaling theorem surface:
    `formal/toe_formal/ToeFormal/Variational/GR01ScalingPromotion.lean`
    (`WeakFieldScalingHierarchy`, `HigherOrderTermsNegligible`,
    `gr01_scaling_hierarchy_under_regime_predicate`,
    `gr01_first_order_truncation_sound`)
  - target ID: `TARGET-GR01-SCALING-PROMO-PLAN`
  - promoted approximation assumption ID: `ASM-GR01-APP-01` (`T-CONDITIONAL`)
- symmetry promotion target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md`
  - symmetry theorem surface:
    `formal/toe_formal/ToeFormal/Variational/GR01SymmetryPromotion.lean`
    (`ProjectionMapWellFormedPredicate`,
    `gr01_projection_map_well_formed_under_regime_predicate`,
    `gr01_projection_map_well_formed`)
  - target ID: `TARGET-GR01-SYM-PROMO-PLAN`
  - promoted symmetry assumption ID: `ASM-GR01-SYM-01` (`T-CONDITIONAL`)
- end-to-end closure target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`
  - chain-composition theorem surface:
    `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`
    (`GR01EndToEndClosureBundle`,
    `gr01_end_to_end_chain_bundle_under_promoted_assumptions`,
    `gr01_end_to_end_poisson_equation_under_promoted_assumptions`)
  - target ID: `TARGET-GR01-END2END-CLOSURE-PLAN`
- derivation-grade closure checklist target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
  - target ID: `TARGET-GR01-DERIV-CHECKLIST-PLAN`
  - scope: scaffold-to-discharge upgrades + action/RAC retirement alignment under unchanged freeze policy.
- current theorem-surface hygiene:
  - `PoissonEquation1D` is non-vacuous (discrete residual predicate),
  - theorem no longer accepts `hPoissonLimit`,
  - derivation surface now depends on explicit bridge components
    (`ProjectionMapWellFormed`, `WeakFieldTruncationSound`, `ELImpliesDiscretePoissonResidual`)
    and constructs `WeakFieldProjectionFromCore` via `mkWeakFieldProjectionFromCore`.
  - regime promotion theorem token:
    `gr01_regime_predicate_under_uniform_bound` (`WeakFieldRegimePredicate`)
    in `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`.
  - scaling promotion theorem token:
    `gr01_first_order_truncation_sound` (`WeakFieldScalingHierarchy`,
    `HigherOrderTermsNegligible`)
    in `formal/toe_formal/ToeFormal/Variational/GR01ScalingPromotion.lean`.
  - symmetry promotion theorem token:
    `gr01_projection_map_well_formed` (`ProjectionMapWellFormedPredicate`)
    in `formal/toe_formal/ToeFormal/Variational/GR01SymmetryPromotion.lean`.
- current scaffold artifacts:
  - `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
  - `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
  - `formal/docs/paper/TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md`
  - `formal/docs/paper/TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md`
  - `formal/docs/paper/TOE_GR01_LAPLACIAN_EXTRACTION_v0.md`
  - `formal/docs/paper/TOE_GR01_KAPPA_CALIBRATION_v0.md`
- frozen geometry work-order target:
  - `formal/docs/paper/DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md`
  - contract-only Lean surface:
    `formal/toe_formal/ToeFormal/GR/GeometryContract.lean`
    (`gr_metric_invariance_under_contract_assumptions`, `MetricInvarianceUnderAction`;
    no GR field-equation claim).
- frozen conservation work-order target:
  - `formal/docs/paper/DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md`
  - contract-only Lean surface:
    `formal/toe_formal/ToeFormal/GR/ConservationContract.lean`
    (`gr_conservation_under_contract_assumptions`, `ConservationLawUnderFlow`;
    no GR field-equation claim and no Noether theorem derivation claim).

### TOE-TH-01
- theorem path (Lean): add conditional entropy-balance theorem surface with explicit regime assumptions.
- analytic derivation: derive entropy-balance expression and admissibility constraints.
- computational evidence: RL10 lane remains bounded support evidence.
- assumptions to remove/promote: classify which dissipative/admissibility assumptions are policy-level vs theorem-level.

## Upgrade Rule

- No claim in this document can be upgraded from bounded/proxy posture until its proof/derivation plan has:
  - explicit theorem target (or explicit postulate declaration),
  - explicit assumption-surface classification,
  - deterministic evidence pointers and governance tests.
