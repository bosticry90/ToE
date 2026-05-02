/-
ToeFormal/Derivation/MasterActionDependencyFrontier.lean

Master-action dependency frontier after the cross-pillar sweep.

Scope:
- classify retained assumptions the master action may cite without overclaim
- distinguish coherence, closure, publication-grade, and local proof-debt
  dependencies
- record dependency information only; do not promote the master action
-/

import ToeFormal.Derivation.CrossPillarClosureFrontier

namespace ToeFormal
namespace Derivation
namespace MasterActionDependencyFrontier

open CrossPillarDerivationProtocol
open CrossPillarClosureFrontier

set_option autoImplicit false

/-- Surface id for the master-action dependency frontier. -/
def masterActionDependencyFrontierSurfaceId : String :=
  "master_action_dependency_frontier_v0"

/-- Citation boundary for a retained assumption used by the master action. -/
structure MasterActionCitationBoundary where
  retained_assumption_id : String
  dependency_kind : MasterActionDependencyKind
  allowed_citation_scope : String
  forbidden_promotion_scope : String
  status : DerivationStatus

/--
Retained assumptions the master action may cite without becoming overclaimed.

Every entry is citation-only: it records what may be referenced and the
boundary that prevents the reference from becoming a promotion.
-/
def masterActionCitationBoundariesV0 :
    List MasterActionCitationBoundary :=
  [ { retained_assumption_id :=
        "PHASE1-BLOCKER-003A2A15A1A31_RAW_IBP_TO_GREEN_CONVERGENCE_PACKAGE_RETAINED"
      dependency_kind := .local_proof_debt
      allowed_citation_scope :=
        "scalar_graph_channel_refined_endpoint_source_and_raw_ibp_green_conditional_bridge_as_retained_evidence"
      forbidden_promotion_scope :=
        "no_a2a15a1_witness_or_phase2_progression_from_scalar_alone"
      status := .retained }
  , { retained_assumption_id :=
        "PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED"
      dependency_kind := .required_for_coherence
      allowed_citation_scope :=
        "qm_stat_finite_zero_residual_package_and_component_evidence_under_supplied_alignment"
      forbidden_promotion_scope :=
        "no_qm_stat_seam_closure_or_stat_mechanics_derivation_from_finite_transport_alone"
      status := .retained }
  , { retained_assumption_id :=
        "PHASE1-BLOCKER-QMSTAT-EVOLUTION-MAP-TO-TRANSPORT-HYPOTHESES-RETAINED"
      dependency_kind := .required_for_coherence
      allowed_citation_scope :=
        "qm_evolution_contract_only_plus_evolution_to_transport_hypotheses_obstruction"
      forbidden_promotion_scope :=
        "no_qm_stat_transport_hypotheses_or_qm_stat_seam_closure_from_qm_evolution_contract_alone"
      status := .retained }
  , { retained_assumption_id :=
        "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED"
      dependency_kind := .required_for_coherence
      allowed_citation_scope :=
        "qft_gr_zero_residual_source_map_and_residual_only_semantic_obstruction"
      forbidden_promotion_scope :=
        "no_semiclassical_gr_source_theorem_or_qft_gr_seam_promotion"
      status := .retained }
  , { retained_assumption_id :=
        "PHASE1-BLOCKER-SR-COSMO-GLOBAL-BRIDGE-SEMANTIC-MAP-RETAINED"
      dependency_kind := .required_for_coherence
      allowed_citation_scope :=
        "bounded_sr_cosmo_transport_zero_residual_package_global_semantic_map_obstruction_and_post_budget_review"
      forbidden_promotion_scope :=
        "no_global_sr_cosmo_bridge_without_additional_global_alignment_semantic_map"
      status := .retained }
  , { retained_assumption_id :=
        "gr01_continuum_limit_source_identification_retained"
      dependency_kind := .publication_grade_only
      allowed_citation_scope :=
        "gr01_discrete_weak_field_package_under_explicit_assumptions"
      forbidden_promotion_scope :=
        "no_all_regime_or_continuum_einstein_class_claim"
      status := .conditional }
  , { retained_assumption_id :=
        "cosmo_background_reduction_and_expansion_observable_retained"
      dependency_kind := .required_for_closure
      allowed_citation_scope :=
        "bounded_cosmology_background_object_and_regime_surface"
      forbidden_promotion_scope :=
        "no_universal_expansion_law_or_empirical_cosmology_claim"
      status := .retained }
  , { retained_assumption_id := "SEAM_EM_QFT_PHYSICS_COMPLETE_v0:NO"
      dependency_kind := .required_for_coherence
      allowed_citation_scope :=
        "em_qft_governance_surface_with_physics_blocker_retained"
      forbidden_promotion_scope :=
        "no_em_qft_physics_completion_or_master_action_support"
      status := .retained }
  , { retained_assumption_id :=
        "gr_qm_master_action_citation_scope_boundary_retained"
      dependency_kind := .publication_grade_only
      allowed_citation_scope :=
        "gr_qm_scoped_package_only_under_its recorded boundaries"
      forbidden_promotion_scope :=
        "no_transfer_of_legacy_scope_into_new_master_action_closure"
      status := .conditional }
  ]

/-- The master-action citation-boundary list is stable. -/
theorem master_action_citation_boundaries_length_v0 :
    masterActionCitationBoundariesV0.length = 9 := by
  rfl

/-- Status readout for the master-action dependency frontier. -/
structure MasterActionDependencyFrontierStatus where
  dependency_classes_defined : Prop
  dependency_classes_defined_supplied : dependency_classes_defined
  citation_boundaries_recorded : Prop
  citation_boundaries_recorded_supplied : citation_boundaries_recorded
  may_cite_retained_assumptions_only : Prop
  may_cite_retained_assumptions_only_supplied :
    may_cite_retained_assumptions_only
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  surface_id : String
  dependency_kind_ids : List String
  retained_assumption_ids : List String

/-- Current dependency result: citation boundaries only, no promotion. -/
def masterActionDependencyFrontierStatusV0 :
    MasterActionDependencyFrontierStatus where
  dependency_classes_defined := True
  dependency_classes_defined_supplied := True.intro
  citation_boundaries_recorded := True
  citation_boundaries_recorded_supplied := True.intro
  may_cite_retained_assumptions_only := True
  may_cite_retained_assumptions_only_supplied := True.intro
  master_action_promoted := False
  master_action_not_promoted := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  surface_id := masterActionDependencyFrontierSurfaceId
  dependency_kind_ids :=
    [ .required_for_coherence
    , .required_for_closure
    , .publication_grade_only
    , .local_proof_debt
    ].map masterActionDependencyKindId
  retained_assumption_ids :=
    masterActionCitationBoundariesV0.map
      (fun boundary => boundary.retained_assumption_id)

/-- Short proof-facing status alias. -/
def masterActionDependencyFrontierStatusReadoutV0 :
    MasterActionDependencyFrontierStatus :=
  masterActionDependencyFrontierStatusV0

/-- Dependency classes are defined. -/
theorem master_action_dependency_classes_defined_v0 :
    masterActionDependencyFrontierStatusReadoutV0
      |>.dependency_classes_defined := by
  exact
    masterActionDependencyFrontierStatusReadoutV0
      |>.dependency_classes_defined_supplied

/-- Citation boundaries are recorded. -/
theorem master_action_citation_boundaries_recorded_v0 :
    masterActionDependencyFrontierStatusReadoutV0
      |>.citation_boundaries_recorded := by
  exact
    masterActionDependencyFrontierStatusReadoutV0
      |>.citation_boundaries_recorded_supplied

/-- The master action may cite only retained/bounded assumptions here. -/
theorem master_action_may_cite_retained_only_v0 :
    masterActionDependencyFrontierStatusReadoutV0
      |>.may_cite_retained_assumptions_only := by
  exact
    masterActionDependencyFrontierStatusReadoutV0
      |>.may_cite_retained_assumptions_only_supplied

/-- The dependency frontier does not promote the master action. -/
theorem master_action_dependency_frontier_not_promoted_v0 :
    Not
      (masterActionDependencyFrontierStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    masterActionDependencyFrontierStatusReadoutV0
      |>.master_action_not_promoted

/-- Phase 2 is not authorized by the dependency frontier. -/
theorem master_action_dependency_frontier_phase2_not_authorized_v0 :
    Not
      (masterActionDependencyFrontierStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    masterActionDependencyFrontierStatusReadoutV0
      |>.phase2_not_authorized

end MasterActionDependencyFrontier
end Derivation
end ToeFormal
