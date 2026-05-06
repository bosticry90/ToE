/-
ToeFormal/Derivation/FullPillarTargetMapRebase.lean

Full pillar target-map rebase surface.

Scope:
- consume `prepare_full_pillar_target_map_rebase`
- define the row schema for full mathematical target mapping
- distinguish current local results from full pillar, seam, and master-action
  targets
- record route source, completion scale, claim posture, retained blockers, and
  semantic status for each admitted target row
- make no full-pillar completion, seam closure, Phase 2, empirical,
  master-action promotion, or theorem-work authorization claim
-/

import ToeFormal.Derivation.CrossPillarDerivationProtocol
import ToeFormal.Derivation.QFTGRStressEnergyOperatorDomainResultReview

namespace ToeFormal
namespace Derivation
namespace FullPillarTargetMapRebase

open CrossPillarDerivationProtocol
open QFTGRStressEnergyOperatorDomainResultReview

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the full-pillar target map rebase. -/
def fullPillarTargetMapRebaseSurfaceId : String :=
  "FULL_PILLAR_TARGET_MAP_REBASE_v0"

/-- Target consumed by this map. -/
def fullPillarTargetMapRebaseConsumedTargetId : String :=
  fullPillarTargetMapRebasePreparationTargetId

/-- Canonical paper-facing map path. -/
def fullPillarTargetMapRebaseDocumentPath : String :=
  "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md"

/-- Focused validation target for this map. -/
def fullPillarTargetMapRebaseValidationTarget : String :=
  "python -m pytest formal/python/tests/test_full_pillar_target_map_rebase_gate.py -q"

/-- Next strict target after the target-map rebase surface is prepared. -/
def fullPillarTargetMapRebaseResultReviewTargetId : String :=
  "review_full_pillar_target_map_rebase_result"

/-- Domains admitted to the full-target map. -/
inductive FullPillarTargetDomain where
  | gr
  | qm
  | em
  | sr
  | scalarQFT
  | stat
  | cosmo
  | qftGR
  | qmSTAT
  | emQFT
  | srCOSMO
  | grQM
  | masterAction
deriving DecidableEq, Repr

/-- Stable string rendering for target-map domains. -/
def fullPillarTargetDomainId : FullPillarTargetDomain -> String
  | .gr => "GR"
  | .qm => "QM"
  | .em => "EM"
  | .sr => "SR"
  | .scalarQFT => "SCALAR_QFT"
  | .stat => "STAT"
  | .cosmo => "COSMO"
  | .qftGR => "QFT_GR"
  | .qmSTAT => "QM_STAT"
  | .emQFT => "EM_QFT"
  | .srCOSMO => "SR_COSMO"
  | .grQM => "GR_QM"
  | .masterAction => "MASTER_ACTION"

/-- Row type: pillar, seam, or master-action target. -/
inductive TargetType where
  | pillar
  | seam
  | masterAction
deriving DecidableEq, Repr

/-- Stable string rendering for target type. -/
def targetTypeId : TargetType -> String
  | .pillar => "pillar"
  | .seam => "seam"
  | .masterAction => "master_action"

/-- Where the current route comes from. -/
inductive RouteSource where
  | derived
  | conditional
  | supplied
  | residualOnly
  | refuted
  | retained
  | notAuthorized
deriving DecidableEq, Repr

/-- Stable string rendering for route source. -/
def routeSourceId : RouteSource -> String
  | .derived => "derived"
  | .conditional => "conditional"
  | .supplied => "supplied"
  | .residualOnly => "residual_only"
  | .refuted => "refuted"
  | .retained => "retained"
  | .notAuthorized => "not_authorized"

/-- Scale of completion represented by a row. -/
inductive CompletionScale where
  | localResult
  | pillar
  | seam
  | masterAction
deriving DecidableEq, Repr

/-- Stable string rendering for completion scale. -/
def completionScaleId : CompletionScale -> String
  | .localResult => "local"
  | .pillar => "pillar"
  | .seam => "seam"
  | .masterAction => "master_action"

/-- Claim posture vocabulary bound to the existing claim taxonomy. -/
inductive ClaimPosture where
  | tProved
  | tConditional
  | eRepro
  | pPolicyNonclaim
  | pPolicyPlanningOnly
  | pPolicySpeculative
  | bBlockedNotAuthorized
deriving DecidableEq, Repr

/-- Stable string rendering for claim posture. -/
def claimPostureId : ClaimPosture -> String
  | .tProved => "T-PROVED"
  | .tConditional => "T-CONDITIONAL"
  | .eRepro => "E-REPRO"
  | .pPolicyNonclaim => "P-POLICY/nonclaim"
  | .pPolicyPlanningOnly => "P-POLICY/planning_only"
  | .pPolicySpeculative => "P-POLICY/speculative"
  | .bBlockedNotAuthorized => "B-BLOCKED/not_authorized"

/-- Semantic state of the row target. -/
inductive SemanticStatus where
  | localAdvancedPillarTargetOpen
  | localDonePillarTargetOpen
  | placeholderSurfacePinnedPillarTargetOpen
  | suppliedSemanticAssumptionRetained
  | residualOnlySemanticOpen
  | packageOnlyRefutedSemanticOpen
  | boundedSeamDone
  | seamTargetOpen
  | masterActionCitationBound
deriving DecidableEq, Repr

/-- Stable string rendering for semantic status. -/
def semanticStatusId : SemanticStatus -> String
  | .localAdvancedPillarTargetOpen =>
      "LOCAL_ADVANCED_PILLAR_TARGET_OPEN"
  | .localDonePillarTargetOpen =>
      "LOCAL_DONE_PILLAR_TARGET_OPEN"
  | .placeholderSurfacePinnedPillarTargetOpen =>
      "PLACEHOLDER_SURFACE_PINNED_PILLAR_TARGET_OPEN"
  | .suppliedSemanticAssumptionRetained =>
      "SUPPLIED_SEMANTIC_ASSUMPTION_RETAINED"
  | .residualOnlySemanticOpen =>
      "RESIDUAL_ONLY_SEMANTIC_OPEN"
  | .packageOnlyRefutedSemanticOpen =>
      "PACKAGE_ONLY_REFUTED_SEMANTIC_OPEN"
  | .boundedSeamDone =>
      "BOUNDED_SEAM_DONE"
  | .seamTargetOpen =>
      "SEAM_TARGET_OPEN"
  | .masterActionCitationBound =>
      "MASTER_ACTION_CITATION_BOUND"

/-- One full-pillar target-map row. -/
structure FullPillarTargetMapRow where
  row_id : String
  domain : FullPillarTargetDomain
  target_type : TargetType
  current_local_result : String
  full_target : String
  route_source : RouteSource
  completion_scale : CompletionScale
  claim_posture : ClaimPosture
  retained_blocker : String
  semantic_status : SemanticStatus
  next_admissible_action : String
  not_authorized : String

/-- Canonical full target-map rows. -/
def fullPillarTargetMapRowsV0 : List FullPillarTargetMapRow :=
  [ { row_id := "FULL_GR_TARGET_MAP_v0"
      domain := .gr
      target_type := .pillar
      current_local_result :=
        "GR01 weak-field / Poisson target under explicit assumptions"
      full_target :=
        "Einstein-equation derivation from action variation with stress-energy source, conservation compatibility, boundary terms, and weak-field recovery"
      route_source := .conditional
      completion_scale := .localResult
      claim_posture := .tConditional
      retained_blocker :=
        "gr01_continuum_limit_source_identification_retained"
      semantic_status := .localDonePillarTargetOpen
      next_admissible_action :=
        "map_full_einstein_equation_derivation_obligations"
      not_authorized :=
        "no_full_GR_claim_no_Einstein_equation_derivation_claim_no_strong_gravity_claim" }
  , { row_id := "FULL_QM_TARGET_MAP_v0"
      domain := .qm
      target_type := .pillar
      current_local_result :=
        "QM evolution contract plus supplied evolution-to-transport semantic bridge"
      full_target :=
        "State space, observables, Schrodinger evolution, Born/probability semantics, expectation rule, measurement semantics, and classical/statistical limits"
      route_source := .retained
      completion_scale := .localResult
      claim_posture := .tConditional
      retained_blocker :=
        "PHASE1-BLOCKER-QMSTAT-EVOLUTION-TO-TRANSPORT-SEMANTIC-BRIDGE-RETAINED"
      semantic_status := .localAdvancedPillarTargetOpen
      next_admissible_action :=
        "map_full_qm_probability_measurement_semantics_obligations"
      not_authorized :=
        "no_Born_rule_derivation_no_measurement_closure_no_full_QM_pillar_claim" }
  , { row_id := "FULL_EM_TARGET_MAP_v0"
      domain := .em
      target_type := .pillar
      current_local_result :=
        "Maxwell/U(1) equation surfaces and compatibility maps pinned"
      full_target :=
        "Gauge-potential to field-strength construction, gauge invariance, action derivation, source-current semantics, current conservation, and tensor/form compatibility"
      route_source := .retained
      completion_scale := .localResult
      claim_posture := .pPolicyNonclaim
      retained_blocker :=
        "PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED"
      semantic_status := .localAdvancedPillarTargetOpen
      next_admissible_action :=
        "map_full_em_gauge_action_and_source_current_obligations"
      not_authorized :=
        "no_nonabelian_claim_no_EM_QFT_closure_no_full_EM_pillar_claim" }
  , { row_id := "FULL_SR_TARGET_MAP_v0"
      domain := .sr
      target_type := .pillar
      current_local_result :=
        "local covariance / transform structure plus SR-COSMO transport package"
      full_target :=
        "Lorentz and Poincare structure, invariant interval, velocity addition, and covariance of admitted field laws"
      route_source := .retained
      completion_scale := .localResult
      claim_posture := .tConditional
      retained_blocker :=
        "PHASE1-BLOCKER-SR-COSMO-GLOBAL-BRIDGE-SEMANTIC-MAP-RETAINED"
      semantic_status := .localAdvancedPillarTargetOpen
      next_admissible_action :=
        "map_full_sr_covariance_and_field_law_obligations"
      not_authorized :=
        "no_global_cosmology_bridge_closure_no_full_SR_pillar_promotion" }
  , { row_id := "FULL_SCALAR_QFT_TARGET_MAP_v0"
      domain := .scalarQFT
      target_type := .pillar
      current_local_result :=
        "scalar route advanced retained handoff ready through A1A31 raw-IBP-to-Green conditional package"
      full_target :=
        "Complete scalar QFT derivation with scalar action, variation, Klein-Gordon equation, canonical momentum, Hamiltonian, quantization, commutators, mode expansion, vacuum, particles, propagator/two-point package, normalization, and nonrelativistic limit"
      route_source := .retained
      completion_scale := .localResult
      claim_posture := .tConditional
      retained_blocker :=
        "PHASE1-BLOCKER-003A2A15A1A31_RAW_IBP_TO_GREEN_CONVERGENCE_PACKAGE_RETAINED"
      semantic_status := .localAdvancedPillarTargetOpen
      next_admissible_action :=
        "map_scalar_qft_quantization_and_full_scalar_target_obligations"
      not_authorized :=
        "no_interacting_QFT_claim_no_Standard_Model_QFT_claim_no_scalar_only_drilling_without_dependency_graph_change" }
  , { row_id := "FULL_STAT_TARGET_MAP_v0"
      domain := .stat
      target_type := .pillar
      current_local_result :=
        "entropy/probability scaffold plus supplied QM-STAT transport residuals"
      full_target :=
        "Probability/density structure, entropy definition, transport law, equilibrium/nonequilibrium structure, entropy production, microscopic link, irreversibility/coarse-graining, and QM-STAT seam alignment"
      route_source := .supplied
      completion_scale := .localResult
      claim_posture := .pPolicySpeculative
      retained_blocker :=
        "PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED"
      semantic_status := .localAdvancedPillarTargetOpen
      next_admissible_action :=
        "map_full_stat_entropy_transport_and_irreversibility_obligations"
      not_authorized :=
        "no_statistical_mechanics_derivation_no_irreversibility_closure_no_full_STAT_pillar_claim" }
  , { row_id := "FULL_COSMO_TARGET_MAP_v0"
      domain := .cosmo
      target_type := .pillar
      current_local_result :=
        "COSMO expansion and equation-of-state placeholder target surface"
      full_target :=
        "Friedmann-like equations, equation-of-state structure, local-to-global bridge, expansion observables, curvature/topology assumptions, and dark-sector assumptions"
      route_source := .notAuthorized
      completion_scale := .localResult
      claim_posture := .pPolicyPlanningOnly
      retained_blocker :=
        "cosmo_background_reduction_and_expansion_observable_retained"
      semantic_status := .placeholderSurfacePinnedPillarTargetOpen
      next_admissible_action :=
        "map_friedmann_equation_and_local_global_cosmology_obligations"
      not_authorized :=
        "no_Friedmann_derivation_no_cosmology_pillar_closure_no_dark_sector_claim" }
  , { row_id := "FULL_SEAM_QFT_GR_TARGET_MAP_v0"
      domain := .qftGR
      target_type := .seam
      current_local_result :=
        "supplied operator-domain semantics construct stress-energy object; package-only derivation refuted"
      full_target :=
        "QFT stress-energy operator domain, state expectation functional, renormalized expectation, weak-curvature source identification, covariance/conservation, and full source-map semantic closure"
      route_source := .supplied
      completion_scale := .seam
      claim_posture := .tConditional
      retained_blocker :=
        "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-OPERATOR-DOMAIN-SEMANTICS-RETAINED"
      semantic_status := .suppliedSemanticAssumptionRetained
      next_admissible_action :=
        "prepare_full_pillar_target_map_rebase"
      not_authorized :=
        "no_QFT_GR_seam_closure_no_semiclassical_gravity_claim_no_Einstein_equation_derivation_claim" }
  , { row_id := "FULL_SEAM_QM_STAT_TARGET_MAP_v0"
      domain := .qmSTAT
      target_type := .seam
      current_local_result :=
        "finite transport residual package works under supplied transport; contract-only probability extraction refuted"
      full_target :=
        "source probability extraction, target entropy semantics, transport-map semantics, observable transport, coarse-graining/irreversibility, and residual-package semantic closure"
      route_source := .supplied
      completion_scale := .seam
      claim_posture := .tConditional
      retained_blocker :=
        "PHASE1-BLOCKER-QMSTAT-SOURCE-PROBABILITY-EXTRACTION-SEMANTICS-RETAINED"
      semantic_status := .suppliedSemanticAssumptionRetained
      next_admissible_action :=
        "map_qm_stat_full_probability_entropy_transport_obligations"
      not_authorized :=
        "no_QM_STAT_seam_closure_no_statistical_mechanics_derivation_claim" }
  , { row_id := "FULL_SEAM_EM_QFT_TARGET_MAP_v0"
      domain := .emQFT
      target_type := .seam
      current_local_result :=
        "shared-dynamics and interface-alignment supplied routes exist; governance/zero-residual/interface-only closure routes refuted"
      full_target :=
        "shared dynamics, residual unification semantics, source-current semantics, gauge/quantization semantics, and EM-QFT bridge closure"
      route_source := .supplied
      completion_scale := .seam
      claim_posture := .tConditional
      retained_blocker :=
        "PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED"
      semantic_status := .seamTargetOpen
      next_admissible_action :=
        "map_em_qft_shared_dynamics_source_current_and_gauge_quantization_obligations"
      not_authorized :=
        "no_EM_QFT_seam_closure_no_source_current_bridge_slice_no_gauge_quantization_bridge_slice" }
  , { row_id := "FULL_SEAM_SR_COSMO_TARGET_MAP_v0"
      domain := .srCOSMO
      target_type := .seam
      current_local_result :=
        "local SR covariance through cosmology regime transport residual package; global semantic-map closure refuted"
      full_target :=
        "local SR covariance, cosmology background/regime alignment, global semantic map, local-to-global transport, and expansion observable semantics"
      route_source := .residualOnly
      completion_scale := .seam
      claim_posture := .tConditional
      retained_blocker :=
        "PHASE1-BLOCKER-SR-COSMO-GLOBAL-BRIDGE-SEMANTIC-MAP-RETAINED"
      semantic_status := .residualOnlySemanticOpen
      next_admissible_action :=
        "map_sr_cosmo_global_bridge_semantic_obligations"
      not_authorized :=
        "no_global_SR_COSMO_bridge_closure_no_cosmology_pillar_closure" }
  , { row_id := "FULL_SEAM_GR_QM_TARGET_MAP_v0"
      domain := .grQM
      target_type := .seam
      current_local_result :=
        "GR-QM scoped seam package with legacy transition boundary"
      full_target :=
        "bounded GR-QM bridge classification distinct from QFT-GR source-map semantics and full quantum gravity"
      route_source := .conditional
      completion_scale := .seam
      claim_posture := .pPolicyNonclaim
      retained_blocker :=
        "gr_qm_master_action_citation_scope_boundary_retained"
      semantic_status := .boundedSeamDone
      next_admissible_action :=
        "map_gr_qm_scope_boundary_against_full_quantum_gravity_target"
      not_authorized :=
        "no_quantum_gravity_claim_no_QFT_GR_source_map_closure_claim" }
  , { row_id := "MASTER_ACTION_FULL_DEPENDENCY_MAP_v0"
      domain := .masterAction
      target_type := .masterAction
      current_local_result :=
        "candidate master action remains citation-bound and non-promoted"
      full_target :=
        "Every term mapped to pillar or seam function with derived/supplied/speculative/placeholder status and dependency gaps listed"
      route_source := .notAuthorized
      completion_scale := .masterAction
      claim_posture := .pPolicyNonclaim
      retained_blocker :=
        "master_action_dependency_frontier_retained_no_promotion"
      semantic_status := .masterActionCitationBound
      next_admissible_action :=
        "retain_master_action_as_dependency_map_during_target_rebase"
      not_authorized :=
        "MASTER_ACTION_CITATION_BOUND_no_canonical_promotion_no_Phase2_no_empirical_claim_no_global_seam_closure" }
  ]

/-- The full target-map rebase records thirteen canonical rows. -/
theorem full_pillar_target_map_row_count_v0 :
    fullPillarTargetMapRowsV0.length = 13 := by
  rfl

/-- Stable row lookup for target-map consumers. -/
def fullPillarTargetMapRowById? (rowId : String) :
    Option FullPillarTargetMapRow :=
  fullPillarTargetMapRowsV0.find? (fun row => row.row_id == rowId)

/-- Current status for the full target-map rebase. -/
structure FullPillarTargetMapRebaseStatus where
  target_map_recorded : Prop
  target_map_recorded_supplied : target_map_recorded
  consumed_target : String
  surface_id : String
  document_path : String
  validation_target : String
  row_count : Nat
  row_schema : List String
  route_source_values : List String
  completion_scale_values : List String
  claim_posture_values : List String
  selected_next_strict_target : String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  seam_closure_claim : Prop
  seam_closure_not_claimed : Not seam_closure_claim
  full_pillar_completion_claim : Prop
  full_pillar_completion_not_claimed : Not full_pillar_completion_claim
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  empirical_claim : Prop
  no_empirical_claim : Not empirical_claim
  status : DerivationStatus

/-- Current result: target maps are recorded; no completion is claimed. -/
def fullPillarTargetMapRebaseStatusV0 :
    FullPillarTargetMapRebaseStatus where
  target_map_recorded := True
  target_map_recorded_supplied := True.intro
  consumed_target := fullPillarTargetMapRebaseConsumedTargetId
  surface_id := fullPillarTargetMapRebaseSurfaceId
  document_path := fullPillarTargetMapRebaseDocumentPath
  validation_target := fullPillarTargetMapRebaseValidationTarget
  row_count := fullPillarTargetMapRowsV0.length
  row_schema :=
    [ "row_id", "domain", "target_type", "current_local_result",
      "full_target", "route_source", "completion_scale", "claim_posture",
      "retained_blocker", "semantic_status", "next_admissible_action",
      "not_authorized" ]
  route_source_values :=
    [ "derived", "conditional", "supplied", "residual_only", "refuted",
      "retained", "not_authorized" ]
  completion_scale_values := [ "local", "pillar", "seam", "master_action" ]
  claim_posture_values :=
    [ "T-PROVED", "T-CONDITIONAL", "E-REPRO", "P-POLICY/nonclaim",
      "P-POLICY/planning_only", "P-POLICY/speculative",
      "B-BLOCKED/not_authorized" ]
  selected_next_strict_target := fullPillarTargetMapRebaseResultReviewTargetId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  seam_closure_claim := False
  seam_closure_not_claimed := by
    intro h
    exact h
  full_pillar_completion_claim := False
  full_pillar_completion_not_claimed := by
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
  status := .retained

/-- Short proof-facing status alias. -/
def fullPillarTargetMapRebaseStatusReadoutV0 :
    FullPillarTargetMapRebaseStatus :=
  fullPillarTargetMapRebaseStatusV0

/-- The map consumes the target selected by the QFT-GR result review. -/
theorem full_pillar_target_map_rebase_consumes_selected_target_v0 :
    (fullPillarTargetMapRebaseStatusReadoutV0 |>.consumed_target) =
      fullPillarTargetMapRebasePreparationTargetId := by
  rfl

/-- The map records the expected number of rows. -/
theorem full_pillar_target_map_rebase_row_count_readout_v0 :
    (fullPillarTargetMapRebaseStatusReadoutV0 |>.row_count) = 13 := by
  rfl

/-- The map selects a result-review target before any physics attack can reopen. -/
theorem full_pillar_target_map_rebase_selected_next_target_v0 :
    (fullPillarTargetMapRebaseStatusReadoutV0 |>.selected_next_strict_target) =
      fullPillarTargetMapRebaseResultReviewTargetId := by
  rfl

/-- The master-action row remains citation-bound. -/
theorem full_pillar_target_map_rebase_master_action_citation_bound_v0 :
    Option.map (fun row => semanticStatusId row.semantic_status)
      (fullPillarTargetMapRowById? "MASTER_ACTION_FULL_DEPENDENCY_MAP_v0") =
      some "MASTER_ACTION_CITATION_BOUND" := by
  decide

/-- The master-action row is master-action scale, not pillar scale. -/
theorem full_pillar_target_map_rebase_master_action_scale_v0 :
    Option.map (fun row => completionScaleId row.completion_scale)
      (fullPillarTargetMapRowById? "MASTER_ACTION_FULL_DEPENDENCY_MAP_v0") =
      some "master_action" := by
  decide

/-- The GR row keeps weak-field work local while opening the full pillar target. -/
theorem full_pillar_target_map_rebase_gr_is_local_not_pillar_done_v0 :
    Option.map (fun row => completionScaleId row.completion_scale)
      (fullPillarTargetMapRowById? "FULL_GR_TARGET_MAP_v0") =
      some "local" := by
  decide

/-- The QFT-GR seam row records a supplied route source. -/
theorem full_pillar_target_map_rebase_qft_gr_route_source_supplied_v0 :
    Option.map (fun row => routeSourceId row.route_source)
      (fullPillarTargetMapRowById? "FULL_SEAM_QFT_GR_TARGET_MAP_v0") =
      some "supplied" := by
  decide

/-- The target-map rebase does not authorize Phase 2. -/
theorem full_pillar_target_map_rebase_phase2_not_authorized_v0 :
    Not (fullPillarTargetMapRebaseStatusReadoutV0 |>.phase2Authorized) := by
  exact fullPillarTargetMapRebaseStatusReadoutV0 |>.phase2_not_authorized

/-- The target-map rebase claims no seam closure. -/
theorem full_pillar_target_map_rebase_no_seam_closure_claim_v0 :
    Not (fullPillarTargetMapRebaseStatusReadoutV0 |>.seam_closure_claim) := by
  exact fullPillarTargetMapRebaseStatusReadoutV0 |>.seam_closure_not_claimed

/-- The target-map rebase claims no full pillar completion. -/
theorem full_pillar_target_map_rebase_no_full_pillar_completion_claim_v0 :
    Not
      (fullPillarTargetMapRebaseStatusReadoutV0
        |>.full_pillar_completion_claim) := by
  exact
    fullPillarTargetMapRebaseStatusReadoutV0
      |>.full_pillar_completion_not_claimed

/-- The target-map rebase does not promote the master action. -/
theorem full_pillar_target_map_rebase_master_action_not_promoted_v0 :
    Not (fullPillarTargetMapRebaseStatusReadoutV0 |>.master_action_promoted) := by
  exact fullPillarTargetMapRebaseStatusReadoutV0 |>.master_action_not_promoted

/-- The target-map rebase makes no empirical claim. -/
theorem full_pillar_target_map_rebase_no_empirical_claim_v0 :
    Not (fullPillarTargetMapRebaseStatusReadoutV0 |>.empirical_claim) := by
  exact fullPillarTargetMapRebaseStatusReadoutV0 |>.no_empirical_claim

end FullPillarTargetMapRebase
end Derivation
end ToeFormal
