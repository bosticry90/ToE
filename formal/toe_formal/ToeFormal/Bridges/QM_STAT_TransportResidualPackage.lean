/-
ToeFormal/Bridges/QM_STAT_TransportResidualPackage.lean

Bounded QM-STAT unified theorem transport residual package.

Scope:
- define the residual-package interface requested by the post-sweep queue
- connect the package to the existing finite-state QM-STAT transport theorems
- record that the current finite transport lemmas are sufficient only under
  supplied finite equivalence/alignment hypotheses
- make no QM-STAT seam closure, statistical mechanics derivation, master-action
  promotion, or empirical claim
-/

import ToeFormal.Bridges.QM_STAT_Transport
import ToeFormal.Derivation.CrossPillarDerivationProtocol

namespace ToeFormal
namespace Bridges
namespace QMSTATTransportResidualPackage

open QMSTATTransport
open ToeFormal.Derivation.CrossPillarDerivationProtocol

noncomputable section
open scoped BigOperators
set_option autoImplicit false

/-- Surface id for the QM-STAT unified transport residual package slice. -/
def qmStatUnifiedTransportResidualPackageSurfaceId : String :=
  "QM_STAT_UNIFIED_TRANSPORT_RESIDUAL_PACKAGE_v0"

/-- Prior blocker targeted by the post-sweep queue. -/
def noUnifiedTheoremTransportResidualPackageId : String :=
  "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"

/-- Retained blocker after the bounded residual-package slice. -/
def phase1BlockerQMSTATTransportResidualPackageRetainedId : String :=
  "PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED"

/-- Outcome id for this bounded QM-STAT transport residual slice. -/
def qmStatTransportResidualPackageRetainedOutcomeId : String :=
  "QM_STAT_TRANSPORT_RESIDUAL_PACKAGE_RETAINED"

/-- Fresh-delta id for the componentwise residual-evidence slice. -/
def qmStatTransportResidualComponentEvidenceFreshDeltaId : String :=
  "QM_STAT_TRANSPORT_RESIDUAL_COMPONENT_EVIDENCE_FRESH_DELTA_v0"

/-- Entropy residual: target entropy-like sum minus source entropy-like sum. -/
def entropyResidual {State : Type} [Fintype State]
    (weight : Real → Real)
    (sourceProbability targetProbability : State → Real) : Real :=
  EntropyLike weight targetProbability -
    EntropyLike weight sourceProbability

/-- Moment residual: target moment minus source moment. -/
def momentResidual {State : Type} [Fintype State]
    (sourceProbability targetProbability : State → Real)
    (sourceObservable targetObservable : State → Real) : Real :=
  Moment targetObservable targetProbability -
    Moment sourceObservable sourceProbability

/-- Variance residual: target variance minus source variance. -/
def varianceResidual
    (sourceMean targetMean sourceSecondMoment targetSecondMoment : Real) :
    Real :=
  Variance targetMean targetSecondMoment -
    Variance sourceMean sourceSecondMoment

/--
Unified finite residual controlled by the current finite transport lemmas.

This is deliberately finite and algebraic: it does not assert irreversibility,
coarse graining, entropy monotonicity, or a physical STAT derivation.
-/
def unifiedTransportResidual {State : Type} [Fintype State]
    (weight : Real → Real)
    (sourceProbability targetProbability : State → Real)
    (sourceMeanObservable targetMeanObservable : State → Real)
    (sourceSecondObservable targetSecondObservable : State → Real) :
    Real :=
  entropyResidual weight sourceProbability targetProbability +
    momentResidual sourceProbability targetProbability
      sourceMeanObservable targetMeanObservable +
    momentResidual sourceProbability targetProbability
      sourceSecondObservable targetSecondObservable +
    varianceResidual
      (Moment sourceMeanObservable sourceProbability)
      (Moment targetMeanObservable targetProbability)
      (Moment sourceSecondObservable sourceProbability)
      (Moment targetSecondObservable targetProbability)

/-- Preservation of entropy, mean, and second moment makes the unified residual zero. -/
theorem unified_transport_residual_zero_of_preservation
    {State : Type} [Fintype State]
    (weight : Real → Real)
    (sourceProbability targetProbability : State → Real)
    (sourceMeanObservable targetMeanObservable : State → Real)
    (sourceSecondObservable targetSecondObservable : State → Real)
    (hEntropy :
      EntropyLike weight targetProbability =
        EntropyLike weight sourceProbability)
    (hMean :
      Moment targetMeanObservable targetProbability =
        Moment sourceMeanObservable sourceProbability)
    (hSecond :
      Moment targetSecondObservable targetProbability =
        Moment sourceSecondObservable sourceProbability) :
    unifiedTransportResidual weight
        sourceProbability targetProbability
        sourceMeanObservable targetMeanObservable
        sourceSecondObservable targetSecondObservable = 0 := by
  simp [unifiedTransportResidual, entropyResidual, momentResidual,
    varianceResidual, hEntropy, hMean, hSecond]

/-- Source-side QM evolution interface for the bounded residual package. -/
structure SourceQMEvolutionStructure (State : Type) [Fintype State] where
  source_probability : State → Real
  evolved_probability : State → Real
  evolution_transport : State ≃ State
  evolution_probability_alignment :
    ∀ state : State,
      evolved_probability state =
        source_probability (evolution_transport state)
  qm_evolution_semantics : Prop
  qm_evolution_semantics_supplied : qm_evolution_semantics

/-- Target-side statistical/entropy interface for the bounded residual package. -/
structure TargetSTATEntropyStructure (State : Type) [Fintype State] where
  target_probability : State → Real
  entropy_weight : Real → Real
  mean_observable : State → Real
  second_moment_observable : State → Real
  stat_entropy_semantics : Prop
  stat_entropy_semantics_supplied : stat_entropy_semantics

/-- Transport map and quantity-alignment interface between the source and target structures. -/
structure QMSTATTransportMapStructure
    (State : Type) [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State) where
  transport : State ≃ State
  probability_alignment :
    ∀ state : State,
      target.target_probability state =
        source.source_probability (transport state)
  mean_observable_source : State → Real
  second_observable_source : State → Real
  mean_observable_alignment :
    ∀ state : State,
      target.mean_observable state =
        mean_observable_source (transport state)
  second_observable_alignment :
    ∀ state : State,
      target.second_moment_observable state =
        second_observable_source (transport state)
  transport_semantics : Prop
  transport_semantics_supplied : transport_semantics

/-- Preserved quantities extracted from the current finite-state transport theorems. -/
structure QMSTATPreservedQuantities
    (State : Type) [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State)
    (transportMap : QMSTATTransportMapStructure State source target) where
  entropy_preserved : Prop
  entropy_preserved_supplied : entropy_preserved
  mean_moment_preserved : Prop
  mean_moment_preserved_supplied : mean_moment_preserved
  second_moment_preserved : Prop
  second_moment_preserved_supplied : second_moment_preserved
  variance_preserved : Prop
  variance_preserved_supplied : variance_preserved

/-- Current finite-state residual package interface for QM-STAT. -/
structure QMSTATUnifiedTransportResidualPackage
    (State : Type) [Fintype State] where
  source_qm_evolution :
    SourceQMEvolutionStructure State
  target_stat_entropy :
    TargetSTATEntropyStructure State
  transport_map :
    QMSTATTransportMapStructure State source_qm_evolution target_stat_entropy
  preserved_quantities :
    QMSTATPreservedQuantities State source_qm_evolution target_stat_entropy
      transport_map
  residual_error_object : Real
  residual_error_object_is_unified :
    residual_error_object =
      unifiedTransportResidual
        target_stat_entropy.entropy_weight
        source_qm_evolution.source_probability
        target_stat_entropy.target_probability
        transport_map.mean_observable_source
        target_stat_entropy.mean_observable
        transport_map.second_observable_source
        target_stat_entropy.second_moment_observable
  residual_vanishes : residual_error_object = 0

/--
Componentwise residual evidence for the current finite QM-STAT transport slice.

The fields expose the entropy, mean, second-moment, variance, and unified
residual zeros separately. They still depend on supplied source/target/transport
semantics and do not close the QM-STAT seam.
-/
structure QMSTATComponentResidualEvidence
    (State : Type) [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State)
    (transportMap : QMSTATTransportMapStructure State source target) where
  entropy_residual_zero :
    entropyResidual
      target.entropy_weight
      source.source_probability
      target.target_probability = 0
  mean_residual_zero :
    momentResidual
      source.source_probability
      target.target_probability
      transportMap.mean_observable_source
      target.mean_observable = 0
  second_moment_residual_zero :
    momentResidual
      source.source_probability
      target.target_probability
      transportMap.second_observable_source
      target.second_moment_observable = 0
  variance_residual_zero :
    varianceResidual
      (Moment transportMap.mean_observable_source source.source_probability)
      (Moment target.mean_observable target.target_probability)
      (Moment transportMap.second_observable_source source.source_probability)
      (Moment target.second_moment_observable target.target_probability) = 0
  unified_residual_zero :
    unifiedTransportResidual
      target.entropy_weight
      source.source_probability
      target.target_probability
      transportMap.mean_observable_source
      target.mean_observable
      transportMap.second_observable_source
      target.second_moment_observable = 0
  source_semantics_supplied : source.qm_evolution_semantics
  target_semantics_supplied : target.stat_entropy_semantics
  transport_semantics_supplied : transportMap.transport_semantics

/--
The existing finite equivalence transport lemmas preserve entropy, mean moment,
second moment, and variance for the supplied finite alignment data.
-/
def preservedQuantitiesOfFiniteEquiv
    {State : Type} [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State)
    (transportMap : QMSTATTransportMapStructure State source target) :
    QMSTATPreservedQuantities State source target transportMap where
  entropy_preserved :=
    EntropyLike target.entropy_weight target.target_probability =
      EntropyLike target.entropy_weight source.source_probability
  entropy_preserved_supplied :=
    entropyLike_preserved_under_equiv
      target.entropy_weight
      transportMap.transport
      source.source_probability
      target.target_probability
      transportMap.probability_alignment
  mean_moment_preserved :=
    Moment target.mean_observable target.target_probability =
      Moment transportMap.mean_observable_source source.source_probability
  mean_moment_preserved_supplied :=
    moment_preserved_under_equiv
      transportMap.transport
      source.source_probability
      target.target_probability
      transportMap.mean_observable_source
      target.mean_observable
      transportMap.probability_alignment
      transportMap.mean_observable_alignment
  second_moment_preserved :=
    Moment target.second_moment_observable target.target_probability =
      Moment transportMap.second_observable_source source.source_probability
  second_moment_preserved_supplied :=
    moment_preserved_under_equiv
      transportMap.transport
      source.source_probability
      target.target_probability
      transportMap.second_observable_source
      target.second_moment_observable
      transportMap.probability_alignment
      transportMap.second_observable_alignment
  variance_preserved :=
    Variance
      (Moment target.mean_observable target.target_probability)
      (Moment target.second_moment_observable target.target_probability) =
    Variance
      (Moment transportMap.mean_observable_source source.source_probability)
      (Moment transportMap.second_observable_source source.source_probability)
  variance_preserved_supplied :=
    variance_preserved_from_moment_transport
      (Moment transportMap.mean_observable_source source.source_probability)
      (Moment target.mean_observable target.target_probability)
      (Moment transportMap.second_observable_source source.source_probability)
      (Moment target.second_moment_observable target.target_probability)
      (moment_preserved_under_equiv
        transportMap.transport
        source.source_probability
        target.target_probability
        transportMap.mean_observable_source
        target.mean_observable
        transportMap.probability_alignment
        transportMap.mean_observable_alignment)
      (moment_preserved_under_equiv
        transportMap.transport
        source.source_probability
        target.target_probability
        transportMap.second_observable_source
        target.second_moment_observable
        transportMap.probability_alignment
        transportMap.second_observable_alignment)

/-- The finite equivalence transport hypotheses produce a zero-residual package. -/
def unifiedTransportResidualPackageOfFiniteEquiv
    {State : Type} [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State)
    (transportMap : QMSTATTransportMapStructure State source target) :
    QMSTATUnifiedTransportResidualPackage State where
  source_qm_evolution := source
  target_stat_entropy := target
  transport_map := transportMap
  preserved_quantities :=
    preservedQuantitiesOfFiniteEquiv source target transportMap
  residual_error_object :=
    unifiedTransportResidual
      target.entropy_weight
      source.source_probability
      target.target_probability
      transportMap.mean_observable_source
      target.mean_observable
      transportMap.second_observable_source
      target.second_moment_observable
  residual_error_object_is_unified := rfl
  residual_vanishes :=
    unified_transport_residual_zero_of_preservation
      target.entropy_weight
      source.source_probability
      target.target_probability
      transportMap.mean_observable_source
      target.mean_observable
      transportMap.second_observable_source
      target.second_moment_observable
      (preservedQuantitiesOfFiniteEquiv source target transportMap
        |>.entropy_preserved_supplied)
      (preservedQuantitiesOfFiniteEquiv source target transportMap
        |>.mean_moment_preserved_supplied)
      (preservedQuantitiesOfFiniteEquiv source target transportMap
        |>.second_moment_preserved_supplied)

/--
Conditional connection theorem: current finite transport theorems build the
bounded residual package when the source, target, and transport structures are
all supplied.
-/
theorem finite_transport_theorems_construct_residual_package_v0
    {State : Type} [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State)
    (transportMap : QMSTATTransportMapStructure State source target) :
    Nonempty (QMSTATUnifiedTransportResidualPackage State) := by
  exact ⟨unifiedTransportResidualPackageOfFiniteEquiv source target transportMap⟩

/--
The finite transport theorems separately zero each component residual under the
same supplied finite equivalence/alignment hypotheses.
-/
def componentResidualEvidenceOfFiniteEquiv
    {State : Type} [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State)
    (transportMap : QMSTATTransportMapStructure State source target) :
    QMSTATComponentResidualEvidence State source target transportMap where
  entropy_residual_zero := by
    simpa [entropyResidual] using
      sub_eq_zero.mpr
        (preservedQuantitiesOfFiniteEquiv source target transportMap
          |>.entropy_preserved_supplied)
  mean_residual_zero := by
    simpa [momentResidual] using
      sub_eq_zero.mpr
        (preservedQuantitiesOfFiniteEquiv source target transportMap
          |>.mean_moment_preserved_supplied)
  second_moment_residual_zero := by
    simpa [momentResidual] using
      sub_eq_zero.mpr
        (preservedQuantitiesOfFiniteEquiv source target transportMap
          |>.second_moment_preserved_supplied)
  variance_residual_zero := by
    simpa [varianceResidual] using
      sub_eq_zero.mpr
        (preservedQuantitiesOfFiniteEquiv source target transportMap
          |>.variance_preserved_supplied)
  unified_residual_zero :=
    unified_transport_residual_zero_of_preservation
      target.entropy_weight
      source.source_probability
      target.target_probability
      transportMap.mean_observable_source
      target.mean_observable
      transportMap.second_observable_source
      target.second_moment_observable
      (preservedQuantitiesOfFiniteEquiv source target transportMap
        |>.entropy_preserved_supplied)
      (preservedQuantitiesOfFiniteEquiv source target transportMap
        |>.mean_moment_preserved_supplied)
      (preservedQuantitiesOfFiniteEquiv source target transportMap
        |>.second_moment_preserved_supplied)
  source_semantics_supplied := source.qm_evolution_semantics_supplied
  target_semantics_supplied := target.stat_entropy_semantics_supplied
  transport_semantics_supplied := transportMap.transport_semantics_supplied

/--
Fresh-delta theorem: current finite transport results construct componentwise
QM-STAT residual evidence, while the seam semantics remain retained.
-/
theorem finite_transport_theorems_construct_component_residual_evidence_v0
    {State : Type} [Fintype State]
    (source : SourceQMEvolutionStructure State)
    (target : TargetSTATEntropyStructure State)
    (transportMap : QMSTATTransportMapStructure State source target) :
    Nonempty
      (QMSTATComponentResidualEvidence State source target transportMap) := by
  exact ⟨componentResidualEvidenceOfFiniteEquiv source target transportMap⟩

/-- Remaining obstructions after the bounded QM-STAT residual package slice. -/
inductive QMSTATTransportResidualObstruction where
  | noDerivedQMEvolutionToProbabilitySource
  | noDerivedSTATEntropyTarget
  | noDerivedTransportFromQMEvolutionToSTAT
  | noCoarseGrainingOrIrreversibilityLaw
  | noSeamClosureOrMasterActionPromotion
deriving DecidableEq, Repr

/-- Stable string ids for retained QM-STAT residual obstructions. -/
def qmStatTransportResidualObstructionId :
    QMSTATTransportResidualObstruction -> String
  | .noDerivedQMEvolutionToProbabilitySource =>
      "NO_DERIVED_QM_EVOLUTION_TO_PROBABILITY_SOURCE"
  | .noDerivedSTATEntropyTarget =>
      "NO_DERIVED_STAT_ENTROPY_TARGET"
  | .noDerivedTransportFromQMEvolutionToSTAT =>
      "NO_DERIVED_TRANSPORT_FROM_QM_EVOLUTION_TO_STAT"
  | .noCoarseGrainingOrIrreversibilityLaw =>
      "NO_COARSE_GRAINING_OR_IRREVERSIBILITY_LAW"
  | .noSeamClosureOrMasterActionPromotion =>
      "NO_SEAM_CLOSURE_OR_MASTER_ACTION_PROMOTION"

/-- The retained obstruction inventory after this bounded slice. -/
def qmStatTransportResidualObstructionsV0 :
    List QMSTATTransportResidualObstruction :=
  [ .noDerivedQMEvolutionToProbabilitySource
  , .noDerivedSTATEntropyTarget
  , .noDerivedTransportFromQMEvolutionToSTAT
  , .noCoarseGrainingOrIrreversibilityLaw
  , .noSeamClosureOrMasterActionPromotion
  ]

/-- The obstruction inventory is stable. -/
theorem qm_stat_transport_residual_obstructions_v0_expected :
    qmStatTransportResidualObstructionsV0 =
      [ .noDerivedQMEvolutionToProbabilitySource
      , .noDerivedSTATEntropyTarget
      , .noDerivedTransportFromQMEvolutionToSTAT
      , .noCoarseGrainingOrIrreversibilityLaw
      , .noSeamClosureOrMasterActionPromotion
      ] := by
  rfl

/-- Status readout for the QM-STAT residual package slice. -/
structure QMSTATTransportResidualPackageStatus where
  residual_interface_defined : Prop
  residual_interface_defined_supplied : residual_interface_defined
  finite_transport_theorems_connect : Prop
  finite_transport_theorems_connect_supplied :
    finite_transport_theorems_connect
  component_residual_evidence_defined : Prop
  component_residual_evidence_defined_supplied :
    component_residual_evidence_defined
  component_residual_evidence_connects : Prop
  component_residual_evidence_connects_supplied :
    component_residual_evidence_connects
  full_qm_stat_seam_closure_supplied : Prop
  full_qm_stat_seam_closure_not_supplied :
    Not full_qm_stat_seam_closure_supplied
  statistical_mechanics_derivation_claim : Prop
  statistical_mechanics_derivation_not_claimed :
    Not statistical_mechanics_derivation_claim
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  empirical_claim : Prop
  empirical_claim_not_supplied : Not empirical_claim
  prior_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  fresh_delta_kind : String
  fresh_delta_id : String
  status : DerivationStatus
  surface_id : String
  obstruction_ids : List String

/-- Current bounded result: package interface and conditional theorem, retained seam blocker. -/
def qmStatTransportResidualPackageStatusV0 :
    QMSTATTransportResidualPackageStatus where
  residual_interface_defined := True
  residual_interface_defined_supplied := True.intro
  finite_transport_theorems_connect := True
  finite_transport_theorems_connect_supplied := True.intro
  component_residual_evidence_defined := True
  component_residual_evidence_defined_supplied := True.intro
  component_residual_evidence_connects := True
  component_residual_evidence_connects_supplied := True.intro
  full_qm_stat_seam_closure_supplied := False
  full_qm_stat_seam_closure_not_supplied := by
    intro h
    exact h
  statistical_mechanics_derivation_claim := False
  statistical_mechanics_derivation_not_claimed := by
    intro h
    exact h
  master_action_promoted := False
  master_action_not_promoted := by
    intro h
    exact h
  empirical_claim := False
  empirical_claim_not_supplied := by
    intro h
    exact h
  prior_blocker_id := noUnifiedTheoremTransportResidualPackageId
  retained_blocker_id := phase1BlockerQMSTATTransportResidualPackageRetainedId
  outcome_id := qmStatTransportResidualPackageRetainedOutcomeId
  fresh_delta_kind := "stronger_evidence_object_plus_new_theorem"
  fresh_delta_id := qmStatTransportResidualComponentEvidenceFreshDeltaId
  status := .retained
  surface_id := qmStatUnifiedTransportResidualPackageSurfaceId
  obstruction_ids :=
    qmStatTransportResidualObstructionsV0.map
      qmStatTransportResidualObstructionId

/-- Short proof-facing status alias. -/
def qmStatTransportResidualPackageStatusReadoutV0 :
    QMSTATTransportResidualPackageStatus :=
  qmStatTransportResidualPackageStatusV0

/-- The residual package interface is defined. -/
theorem qm_stat_transport_residual_interface_defined_v0 :
    qmStatTransportResidualPackageStatusReadoutV0
      |>.residual_interface_defined := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.residual_interface_defined_supplied

/-- The finite transport theorems connect to the bounded residual package. -/
theorem qm_stat_finite_transport_theorems_connect_v0 :
    qmStatTransportResidualPackageStatusReadoutV0
      |>.finite_transport_theorems_connect := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.finite_transport_theorems_connect_supplied

/-- The component residual evidence object is defined. -/
theorem qm_stat_component_residual_evidence_defined_v0 :
    qmStatTransportResidualPackageStatusReadoutV0
      |>.component_residual_evidence_defined := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.component_residual_evidence_defined_supplied

/-- The finite transport theorems connect to componentwise residual evidence. -/
theorem qm_stat_component_residual_evidence_connects_v0 :
    qmStatTransportResidualPackageStatusReadoutV0
      |>.component_residual_evidence_connects := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.component_residual_evidence_connects_supplied

/-- The fresh-delta id remains explicit for loop-control accounting. -/
theorem qm_stat_transport_residual_fresh_delta_id_v0 :
    (qmStatTransportResidualPackageStatusReadoutV0
      |>.fresh_delta_id) =
      qmStatTransportResidualComponentEvidenceFreshDeltaId := by
  rfl

/-- The current bounded package does not close the QM-STAT seam. -/
theorem qm_stat_transport_residual_no_seam_closure_v0 :
    Not
      (qmStatTransportResidualPackageStatusReadoutV0
        |>.full_qm_stat_seam_closure_supplied) := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.full_qm_stat_seam_closure_not_supplied

/-- The current bounded package does not claim a statistical mechanics derivation. -/
theorem qm_stat_transport_residual_no_stat_mechanics_derivation_claim_v0 :
    Not
      (qmStatTransportResidualPackageStatusReadoutV0
        |>.statistical_mechanics_derivation_claim) := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.statistical_mechanics_derivation_not_claimed

/-- The current bounded package does not promote the master action. -/
theorem qm_stat_transport_residual_master_action_not_promoted_v0 :
    Not
      (qmStatTransportResidualPackageStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.master_action_not_promoted

/-- The current bounded package does not supply an empirical claim. -/
theorem qm_stat_transport_residual_no_empirical_claim_v0 :
    Not
      (qmStatTransportResidualPackageStatusReadoutV0
        |>.empirical_claim) := by
  exact
    qmStatTransportResidualPackageStatusReadoutV0
      |>.empirical_claim_not_supplied

/-- The new retained blocker id is exposed. -/
theorem qm_stat_transport_residual_retained_blocker_id_v0 :
    (qmStatTransportResidualPackageStatusReadoutV0
      |>.retained_blocker_id) =
      phase1BlockerQMSTATTransportResidualPackageRetainedId := by
  rfl

end
end QMSTATTransportResidualPackage
end Bridges
end ToeFormal
