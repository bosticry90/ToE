/-
ToeFormal/Bridges/QFT_GR_PoissonRecoveryObligationSemantics.lean

Bounded QFT-GR Poisson-recovery obligation semantics slice.

Scope:
- consume `prepare_qft_gr_poisson_recovery_obligation_semantics_bounded_attack`
- define a supplied Poisson-recovery obligation surface over weak-curvature
  source-candidate and Poisson-recovery candidate semantics
- separate "has a Poisson-recovery obligation" from "has a Poisson-recovery
  witness" and from "satisfies Poisson recovery"
- refute weak-curvature-source-identification-obligation-only evidence as
  sufficient to derive a Poisson-recovery witness, actual Poisson recovery,
  Newtonian-limit recovery, weak-field recovery proof, or source-map closure
- retain the Poisson-recovery obligation as supplied semantic structure only,
  not as weak-field recovery, Newtonian recovery, or a GR source map
- preserve previous nonclaim boundaries for renormalization-scheme validity,
  finite stress-energy tensor proof, Hadamard-state adequacy,
  operator-self-adjointness, dense-domain proof, conservation witness, actual
  covariant conservation, Bianchi witness, actual Bianchi compatibility,
  Einstein-coupling witness, actual Einstein-equation coupling,
  weak-curvature source-identification witness, and actual weak-curvature
  source identification
- make no QFT-GR seam closure, semiclassical-gravity, Einstein-equation
  derivation, Phase 2, empirical, master-action promotion, or
  governance-manifest claim
- rotate only to a Poisson-recovery obligation result review
- do not assert Poisson recovery, Newtonian recovery, weak-field recovery, or
  `G_mu_nu = kappa <T_mu_nu>_ren`
-/

import ToeFormal.Bridges.QFT_GR_WeakCurvatureSourceIdentificationObligationSemanticsResultReview

namespace ToeFormal
namespace Bridges
namespace QFTGRPoissonRecoveryObligationSemantics

open QFTGRWeakCurvatureSourceIdentificationObligationSemantics
open QFTGRWeakCurvatureSourceIdentificationObligationSemanticsResultReview
open ToeFormal.Derivation.CrossPillarDerivationProtocol

noncomputable section
set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the Poisson-recovery obligation semantics slice. -/
def qftGRPoissonRecoveryObligationSemanticsSurfaceId : String :=
  "QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_v0"

/-- Target emitted by the weak-curvature source-identification result review. -/
def qftGRPoissonRecoveryObligationSemanticsTargetId : String :=
  qftGRPoissonRecoveryObligationSemanticsPreparationTargetId

/-- Live target consumed by this bounded slice. -/
def qftGRPoissonRecoveryObligationSemanticsConsumedTargetId : String :=
  qftGRPoissonRecoveryObligationSemanticsTargetId

/-- Retained blocker exposed by the missing Poisson-recovery witness. -/
def qftGRPoissonRecoveryWitnessRetainedBlockerId : String :=
  "PHASE1-BLOCKER-QFTGR-POISSON-RECOVERY-WITNESS-RETAINED"

/-- Fresh-delta id for the weak-curvature-obligation-only counterexample. -/
def qftGRPoissonRecoveryObligationCounterexampleFreshDeltaId : String :=
  "QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_COUNTEREXAMPLE_FRESH_DELTA_v0"

/-- Registry fresh-delta kind supplied by this slice. -/
def qftGRPoissonRecoveryObligationFreshDeltaKind : String :=
  "counterexample"

/-- Next strict target after this bounded obligation slice. -/
def qftGRPoissonRecoveryObligationResultReviewTargetId : String :=
  "review_qft_gr_poisson_recovery_obligation_semantics_result"

/-- Selected theorem obligation for this bounded QFT-GR slice. -/
def qftGRPoissonRecoveryObligationSelectedObligationId : String :=
  "QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_DERIVATION_OBLIGATION_v0"

/-- Minimum closure condition retained for Poisson recovery. -/
def qftGRPoissonRecoveryObligationMinimumClosureConditionId : String :=
  "theorem_linked_poisson_recovery_witness_or_refutation"

/-- Result token for this supplied-only semantic availability result. -/
def qftGRPoissonRecoveryObligationSuppliedOnlyResultToken : String :=
  "QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_SUPPLIED_ONLY"

/--
Narrow supplied semantic package for Poisson-recovery obligations. It provides
an obligation predicate and a satisfaction relation, but no witness and no proof
that any candidate satisfies the obligation.
-/
structure QFTGRPoissonRecoveryObligationSemanticPackage (Point : Type) where
  weak_curvature_source_identification_obligation_package :
    QFTGRWeakCurvatureSourceIdentificationObligationSemanticPackage Point
  PoissonRecoveryCandidate : Type
  PoissonRecoveryWitness : Type
  hasPoissonRecoveryObligation :
    weak_curvature_source_identification_obligation_package
      |>.WeakCurvatureSourceCandidate ->
      PoissonRecoveryCandidate ->
      Prop
  poissonRecoverySatisfied :
    weak_curvature_source_identification_obligation_package
      |>.WeakCurvatureSourceCandidate ->
      PoissonRecoveryCandidate ->
      PoissonRecoveryWitness ->
      Prop
  poisson_recovery_obligation_semantics : Prop
  poisson_recovery_obligation_semantics_supplied :
    poisson_recovery_obligation_semantics
  supplied_only_obligation_surface : Prop
  supplied_only_obligation_surface_supplied :
    supplied_only_obligation_surface

/-- Supplied semantic data for constructing the Poisson-recovery obligation interface. -/
structure QFTGRPoissonRecoveryObligationSemanticData (Point : Type) where
  weak_curvature_source_identification_obligation_package :
    QFTGRWeakCurvatureSourceIdentificationObligationSemanticPackage Point
  PoissonRecoveryCandidate : Type
  PoissonRecoveryWitness : Type
  hasPoissonRecoveryObligation :
    weak_curvature_source_identification_obligation_package
      |>.WeakCurvatureSourceCandidate ->
      PoissonRecoveryCandidate ->
      Prop
  poissonRecoverySatisfied :
    weak_curvature_source_identification_obligation_package
      |>.WeakCurvatureSourceCandidate ->
      PoissonRecoveryCandidate ->
      PoissonRecoveryWitness ->
      Prop
  poisson_recovery_obligation_semantics : Prop
  poisson_recovery_obligation_semantics_supplied :
    poisson_recovery_obligation_semantics
  supplied_only_obligation_surface : Prop
  supplied_only_obligation_surface_supplied :
    supplied_only_obligation_surface

/-- Poisson-recovery package induced by supplied semantics. -/
def poissonRecoveryObligationPackageOfSuppliedSemantics
    {Point : Type}
    (data : QFTGRPoissonRecoveryObligationSemanticData Point) :
    QFTGRPoissonRecoveryObligationSemanticPackage Point where
  weak_curvature_source_identification_obligation_package :=
    data.weak_curvature_source_identification_obligation_package
  PoissonRecoveryCandidate := data.PoissonRecoveryCandidate
  PoissonRecoveryWitness := data.PoissonRecoveryWitness
  hasPoissonRecoveryObligation := data.hasPoissonRecoveryObligation
  poissonRecoverySatisfied := data.poissonRecoverySatisfied
  poisson_recovery_obligation_semantics :=
    data.poisson_recovery_obligation_semantics
  poisson_recovery_obligation_semantics_supplied :=
    data.poisson_recovery_obligation_semantics_supplied
  supplied_only_obligation_surface := data.supplied_only_obligation_surface
  supplied_only_obligation_surface_supplied :=
    data.supplied_only_obligation_surface_supplied

/--
Supplied Poisson-recovery obligation semantics construct the narrow obligation
surface over the supplied weak-curvature source-identification obligation
package.
-/
theorem supplied_poisson_recovery_obligation_semantics_constructs_package_v0
    {Point : Type}
    (data : QFTGRPoissonRecoveryObligationSemanticData Point) :
    Nonempty (QFTGRPoissonRecoveryObligationSemanticPackage Point) := by
  exact ⟨poissonRecoveryObligationPackageOfSuppliedSemantics data⟩

/-- A concrete unit weak-curvature obligation package for finite counterexample use. -/
def unitWeakCurvatureSourceIdentificationObligationPackageWithSuppliedSemantics :
    QFTGRWeakCurvatureSourceIdentificationObligationSemanticPackage Unit where
  einstein_coupling_obligation_package :=
    unitEinsteinCouplingObligationPackageWithSuppliedSemantics
  WeakCurvatureSourceCandidate := Unit
  SourceIdentificationWitness := Unit
  hasWeakCurvatureSourceIdentificationObligation := fun _ _ => True
  weakCurvatureSourceIdentificationSatisfied := fun _ _ _ => True
  weak_curvature_source_identification_obligation_semantics := True
  weak_curvature_source_identification_obligation_semantics_supplied :=
    True.intro
  supplied_only_obligation_surface := True
  supplied_only_obligation_surface_supplied := True.intro

/-- Requirements for deriving actual Poisson-recovery closure. -/
structure QFTGRPoissonRecoveryObligationSemanticRequirements where
  poisson_recovery_witness_derived : Prop
  actual_poisson_recovery_derived : Prop
  newtonian_limit_recovery_derived : Prop
  weak_field_recovery_proof_derived : Prop

/-- Poisson-recovery interface demanded by stronger closure. -/
structure QFTGRPoissonRecoveryObligationSemanticInterface
    (requirements : QFTGRPoissonRecoveryObligationSemanticRequirements)
    (Point : Type)
    (package :
      QFTGRWeakCurvatureSourceIdentificationObligationSemanticPackage Point) :
    Prop where
  weak_curvature_source_identification_obligation_package_available : True
  poisson_recovery_witness_closed :
    requirements.poisson_recovery_witness_derived
  actual_poisson_recovery_closed :
    requirements.actual_poisson_recovery_derived
  newtonian_limit_recovery_closed :
    requirements.newtonian_limit_recovery_derived
  weak_field_recovery_proof_closed :
    requirements.weak_field_recovery_proof_derived

/-- False requirements used to refute weak-curvature-obligation-only closure. -/
def falsePoissonRecoveryObligationSemanticRequirements :
    QFTGRPoissonRecoveryObligationSemanticRequirements where
  poisson_recovery_witness_derived := False
  actual_poisson_recovery_derived := False
  newtonian_limit_recovery_derived := False
  weak_field_recovery_proof_derived := False

/--
Counterexample: a supplied weak-curvature source-identification obligation
package alone does not force a Poisson-recovery witness.
-/
theorem
    qft_gr_weak_curvature_source_identification_obligation_semantics_does_not_force_poisson_recovery_witness_v0 :
    Not
      (forall
          package :
            QFTGRWeakCurvatureSourceIdentificationObligationSemanticPackage
              Unit,
        QFTGRPoissonRecoveryObligationSemanticInterface
          falsePoissonRecoveryObligationSemanticRequirements
          Unit
          package) := by
  intro h
  have hClosed :=
    h unitWeakCurvatureSourceIdentificationObligationPackageWithSuppliedSemantics
  exact hClosed.poisson_recovery_witness_closed

/-- Status readout for the bounded Poisson-recovery obligation slice. -/
structure QFTGRPoissonRecoveryObligationSemanticsStatus where
  supplied_poisson_recovery_obligation_route_available : Prop
  supplied_poisson_recovery_obligation_route_available_supplied :
    supplied_poisson_recovery_obligation_route_available
  weak_curvature_obligation_only_poisson_recovery_witness_refuted : Prop
  weak_curvature_obligation_only_poisson_recovery_witness_refuted_supplied :
    weak_curvature_obligation_only_poisson_recovery_witness_refuted
  poisson_recovery_witness_derived_from_weak_curvature_obligation_alone :
    Prop
  poisson_recovery_witness_not_derived_from_weak_curvature_obligation_alone :
    Not poisson_recovery_witness_derived_from_weak_curvature_obligation_alone
  poisson_recovery_obligation_retained_as_supplied : Prop
  poisson_recovery_obligation_retained_as_supplied_evidence :
    poisson_recovery_obligation_retained_as_supplied
  renormalization_scheme_validity_authorized : Prop
  renormalization_scheme_validity_not_authorized :
    Not renormalization_scheme_validity_authorized
  finite_stress_energy_tensor_proof_authorized : Prop
  finite_stress_energy_tensor_proof_not_authorized :
    Not finite_stress_energy_tensor_proof_authorized
  hadamard_state_adequacy_authorized : Prop
  hadamard_state_adequacy_not_authorized :
    Not hadamard_state_adequacy_authorized
  operator_self_adjointness_authorized : Prop
  operator_self_adjointness_not_authorized :
    Not operator_self_adjointness_authorized
  domain_density_proof_authorized : Prop
  domain_density_proof_not_authorized :
    Not domain_density_proof_authorized
  conservation_witness_authorized : Prop
  conservation_witness_not_authorized :
    Not conservation_witness_authorized
  actual_covariant_conservation_authorized : Prop
  actual_covariant_conservation_not_authorized :
    Not actual_covariant_conservation_authorized
  bianchi_compatibility_witness_authorized : Prop
  bianchi_compatibility_witness_not_authorized :
    Not bianchi_compatibility_witness_authorized
  actual_bianchi_compatibility_authorized : Prop
  actual_bianchi_compatibility_not_authorized :
    Not actual_bianchi_compatibility_authorized
  einstein_coupling_witness_authorized : Prop
  einstein_coupling_witness_not_authorized :
    Not einstein_coupling_witness_authorized
  actual_einstein_equation_coupling_authorized : Prop
  actual_einstein_equation_coupling_not_authorized :
    Not actual_einstein_equation_coupling_authorized
  weak_curvature_source_identification_witness_authorized : Prop
  weak_curvature_source_identification_witness_not_authorized :
    Not weak_curvature_source_identification_witness_authorized
  actual_weak_curvature_source_identification_authorized : Prop
  actual_weak_curvature_source_identification_not_authorized :
    Not actual_weak_curvature_source_identification_authorized
  poisson_recovery_witness_authorized : Prop
  poisson_recovery_witness_not_authorized :
    Not poisson_recovery_witness_authorized
  actual_poisson_recovery_authorized : Prop
  actual_poisson_recovery_not_authorized :
    Not actual_poisson_recovery_authorized
  newtonian_limit_recovery_authorized : Prop
  newtonian_limit_recovery_not_authorized :
    Not newtonian_limit_recovery_authorized
  weak_field_recovery_proof_authorized : Prop
  weak_field_recovery_proof_not_authorized :
    Not weak_field_recovery_proof_authorized
  semiclassical_einstein_equation_authorized : Prop
  semiclassical_einstein_equation_not_authorized :
    Not semiclassical_einstein_equation_authorized
  full_source_map_semantic_closure_authorized : Prop
  full_source_map_semantic_closure_not_authorized :
    Not full_source_map_semantic_closure_authorized
  qft_gr_seam_closed : Prop
  qft_gr_seam_not_closed : Not qft_gr_seam_closed
  semiclassical_gravity_claim : Prop
  no_semiclassical_gravity_claim : Not semiclassical_gravity_claim
  einstein_equation_derivation_claim : Prop
  no_einstein_equation_derivation_claim :
    Not einstein_equation_derivation_claim
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  empirical_claim : Prop
  no_empirical_claim : Not empirical_claim
  governance_manifest_enrollment_authorized : Prop
  governance_manifest_enrollment_not_authorized :
    Not governance_manifest_enrollment_authorized
  consumed_target : String
  selected_next_strict_target : String
  surface_id : String
  retained_blocker_id : String
  fresh_delta_id : String
  fresh_delta_kind : String
  result_token : String
  selected_obligation_id : String
  minimum_closure_condition_id : String
  consumed_result_review_token : String
  status : DerivationStatus

/--
Current result: supplied obligation semantics define the Poisson-recovery
obligation surface, but weak-curvature-source-identification-obligation-only
derivation of a Poisson-recovery witness is refuted.
-/
def qftGRPoissonRecoveryObligationSemanticsStatusV0 :
    QFTGRPoissonRecoveryObligationSemanticsStatus where
  supplied_poisson_recovery_obligation_route_available := True
  supplied_poisson_recovery_obligation_route_available_supplied := True.intro
  weak_curvature_obligation_only_poisson_recovery_witness_refuted := True
  weak_curvature_obligation_only_poisson_recovery_witness_refuted_supplied :=
    True.intro
  poisson_recovery_witness_derived_from_weak_curvature_obligation_alone :=
    False
  poisson_recovery_witness_not_derived_from_weak_curvature_obligation_alone :=
    by
      intro h
      exact h
  poisson_recovery_obligation_retained_as_supplied := True
  poisson_recovery_obligation_retained_as_supplied_evidence := True.intro
  renormalization_scheme_validity_authorized := False
  renormalization_scheme_validity_not_authorized := by
    intro h
    exact h
  finite_stress_energy_tensor_proof_authorized := False
  finite_stress_energy_tensor_proof_not_authorized := by
    intro h
    exact h
  hadamard_state_adequacy_authorized := False
  hadamard_state_adequacy_not_authorized := by
    intro h
    exact h
  operator_self_adjointness_authorized := False
  operator_self_adjointness_not_authorized := by
    intro h
    exact h
  domain_density_proof_authorized := False
  domain_density_proof_not_authorized := by
    intro h
    exact h
  conservation_witness_authorized := False
  conservation_witness_not_authorized := by
    intro h
    exact h
  actual_covariant_conservation_authorized := False
  actual_covariant_conservation_not_authorized := by
    intro h
    exact h
  bianchi_compatibility_witness_authorized := False
  bianchi_compatibility_witness_not_authorized := by
    intro h
    exact h
  actual_bianchi_compatibility_authorized := False
  actual_bianchi_compatibility_not_authorized := by
    intro h
    exact h
  einstein_coupling_witness_authorized := False
  einstein_coupling_witness_not_authorized := by
    intro h
    exact h
  actual_einstein_equation_coupling_authorized := False
  actual_einstein_equation_coupling_not_authorized := by
    intro h
    exact h
  weak_curvature_source_identification_witness_authorized := False
  weak_curvature_source_identification_witness_not_authorized := by
    intro h
    exact h
  actual_weak_curvature_source_identification_authorized := False
  actual_weak_curvature_source_identification_not_authorized := by
    intro h
    exact h
  poisson_recovery_witness_authorized := False
  poisson_recovery_witness_not_authorized := by
    intro h
    exact h
  actual_poisson_recovery_authorized := False
  actual_poisson_recovery_not_authorized := by
    intro h
    exact h
  newtonian_limit_recovery_authorized := False
  newtonian_limit_recovery_not_authorized := by
    intro h
    exact h
  weak_field_recovery_proof_authorized := False
  weak_field_recovery_proof_not_authorized := by
    intro h
    exact h
  semiclassical_einstein_equation_authorized := False
  semiclassical_einstein_equation_not_authorized := by
    intro h
    exact h
  full_source_map_semantic_closure_authorized := False
  full_source_map_semantic_closure_not_authorized := by
    intro h
    exact h
  qft_gr_seam_closed := False
  qft_gr_seam_not_closed := by
    intro h
    exact h
  semiclassical_gravity_claim := False
  no_semiclassical_gravity_claim := by
    intro h
    exact h
  einstein_equation_derivation_claim := False
  no_einstein_equation_derivation_claim := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  master_action_promoted := False
  master_action_not_promoted := by
    intro h
    exact h
  empirical_claim := False
  no_empirical_claim := by
    intro h
    exact h
  governance_manifest_enrollment_authorized := False
  governance_manifest_enrollment_not_authorized := by
    intro h
    exact h
  consumed_target := qftGRPoissonRecoveryObligationSemanticsConsumedTargetId
  selected_next_strict_target :=
    qftGRPoissonRecoveryObligationResultReviewTargetId
  surface_id := qftGRPoissonRecoveryObligationSemanticsSurfaceId
  retained_blocker_id := qftGRPoissonRecoveryWitnessRetainedBlockerId
  fresh_delta_id := qftGRPoissonRecoveryObligationCounterexampleFreshDeltaId
  fresh_delta_kind := qftGRPoissonRecoveryObligationFreshDeltaKind
  result_token := qftGRPoissonRecoveryObligationSuppliedOnlyResultToken
  selected_obligation_id := qftGRPoissonRecoveryObligationSelectedObligationId
  minimum_closure_condition_id :=
    qftGRPoissonRecoveryObligationMinimumClosureConditionId
  consumed_result_review_token :=
    qftGRWeakCurvatureSourceIdentificationObligationResultReviewTokenId
  status := .retained

/-- Short proof-facing status alias. -/
def qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0 :
    QFTGRPoissonRecoveryObligationSemanticsStatus :=
  qftGRPoissonRecoveryObligationSemanticsStatusV0

/-- The slice consumes the selected Poisson-recovery obligation target. -/
theorem qft_gr_poisson_recovery_obligation_semantics_consumes_live_target_v0 :
    (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.consumed_target) =
      qftGRPoissonRecoveryObligationSemanticsTargetId := by
  rfl

/-- The supplied Poisson-recovery obligation route is available. -/
theorem qft_gr_poisson_recovery_obligation_semantics_supplied_route_available_v0 :
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.supplied_poisson_recovery_obligation_route_available := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.supplied_poisson_recovery_obligation_route_available_supplied

/-- Weak-curvature-obligation-only derivation of a Poisson witness is refuted. -/
theorem qft_gr_poisson_recovery_obligation_semantics_weak_curvature_obligation_only_refuted_v0 :
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.weak_curvature_obligation_only_poisson_recovery_witness_refuted := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.weak_curvature_obligation_only_poisson_recovery_witness_refuted_supplied

/-- The Poisson-recovery obligation remains retained as supplied. -/
theorem qft_gr_poisson_recovery_obligation_semantics_retained_as_supplied_v0 :
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.poisson_recovery_obligation_retained_as_supplied := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.poisson_recovery_obligation_retained_as_supplied_evidence

/-- The result token records supplied-only Poisson-recovery obligation semantics. -/
theorem qft_gr_poisson_recovery_obligation_semantics_result_token_v0 :
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0.result_token =
      qftGRPoissonRecoveryObligationSuppliedOnlyResultToken := by
  rfl

/-- The next target is the Poisson-recovery obligation result review. -/
theorem qft_gr_poisson_recovery_obligation_semantics_selected_next_target_v0 :
    (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.selected_next_strict_target) =
      qftGRPoissonRecoveryObligationResultReviewTargetId := by
  rfl

/-- Renormalization-scheme validity remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_scheme_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.renormalization_scheme_validity_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.renormalization_scheme_validity_not_authorized

/-- Finite stress-energy tensor proof remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_finite_tensor_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.finite_stress_energy_tensor_proof_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.finite_stress_energy_tensor_proof_not_authorized

/-- Hadamard-state adequacy remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_hadamard_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.hadamard_state_adequacy_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.hadamard_state_adequacy_not_authorized

/-- Operator self-adjointness remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_self_adjoint_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.operator_self_adjointness_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.operator_self_adjointness_not_authorized

/-- Domain-density proof remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_domain_density_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.domain_density_proof_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.domain_density_proof_not_authorized

/-- A conservation witness remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_conservation_witness_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.conservation_witness_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.conservation_witness_not_authorized

/-- Actual covariant conservation remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_actual_conservation_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.actual_covariant_conservation_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.actual_covariant_conservation_not_authorized

/-- A Bianchi-compatibility witness remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_bianchi_witness_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.bianchi_compatibility_witness_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.bianchi_compatibility_witness_not_authorized

/-- Actual Bianchi compatibility remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_actual_bianchi_compatibility_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.actual_bianchi_compatibility_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.actual_bianchi_compatibility_not_authorized

/-- An Einstein-coupling witness remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_einstein_witness_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.einstein_coupling_witness_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.einstein_coupling_witness_not_authorized

/-- Actual Einstein-equation coupling remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_actual_coupling_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.actual_einstein_equation_coupling_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.actual_einstein_equation_coupling_not_authorized

/-- A weak-curvature source-identification witness remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_source_witness_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.weak_curvature_source_identification_witness_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.weak_curvature_source_identification_witness_not_authorized

/-- Actual weak-curvature source identification remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_actual_source_identification_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.actual_weak_curvature_source_identification_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.actual_weak_curvature_source_identification_not_authorized

/-- A Poisson-recovery witness remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_poisson_witness_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.poisson_recovery_witness_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.poisson_recovery_witness_not_authorized

/-- Actual Poisson recovery remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_actual_poisson_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.actual_poisson_recovery_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.actual_poisson_recovery_not_authorized

/-- Newtonian-limit recovery remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_newtonian_limit_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.newtonian_limit_recovery_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.newtonian_limit_recovery_not_authorized

/-- Weak-field recovery proof remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_weak_field_proof_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.weak_field_recovery_proof_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.weak_field_recovery_proof_not_authorized

/-- The semiclassical Einstein equation remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_semiclassical_eq_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.semiclassical_einstein_equation_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.semiclassical_einstein_equation_not_authorized

/-- Full source-map semantic closure remains unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_source_map_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.full_source_map_semantic_closure_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.full_source_map_semantic_closure_not_authorized

/-- This slice does not close the QFT-GR seam. -/
theorem qft_gr_poisson_recovery_obligation_semantics_no_seam_closure_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.qft_gr_seam_closed) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.qft_gr_seam_not_closed

/-- This slice makes no semiclassical-gravity claim. -/
theorem qft_gr_poisson_recovery_obligation_semantics_no_semiclassical_gravity_claim_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.semiclassical_gravity_claim) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.no_semiclassical_gravity_claim

/-- This slice makes no Einstein-equation derivation claim. -/
theorem qft_gr_poisson_recovery_obligation_semantics_no_einstein_claim_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.einstein_equation_derivation_claim) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.no_einstein_equation_derivation_claim

/-- This slice keeps Phase 2 unauthorized. -/
theorem qft_gr_poisson_recovery_obligation_semantics_phase2_not_authorized_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.phase2_not_authorized

/-- This slice does not promote the master action. -/
theorem qft_gr_poisson_recovery_obligation_semantics_master_action_not_promoted_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.master_action_not_promoted

/-- This slice makes no empirical claim. -/
theorem qft_gr_poisson_recovery_obligation_semantics_no_empirical_claim_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.empirical_claim) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.no_empirical_claim

/-- This slice is not enrolled in the governance manifest. -/
theorem qft_gr_poisson_recovery_obligation_semantics_manifest_not_enrolled_v0 :
    Not
      (qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact
    qftGRPoissonRecoveryObligationSemanticsStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized

end
end QFTGRPoissonRecoveryObligationSemantics
end Bridges
end ToeFormal
