/-
ToeFormal/Derivation/QMStatEntropySemanticsSupportingAssumptionMap.lean

Supporting-assumption map for the supplied-only QM-STAT target STAT entropy
semantics gap.

Scope:
- consume `prepare_qm_stat_entropy_semantics_supporting_assumption_map`
- consume `FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP`
- map the minimum supporting assumptions required before the target entropy
  semantics gap could move beyond supplied-only authority
- classify each assumption as Lean-backed, spec-backed, supplied-only, blocked,
  or not yet represented
- preserve that no entropy-semantics theorem has been discharged
- rotate only to `review_qm_stat_entropy_semantics_supporting_assumption_map_result`
- do not infer QM-STAT pillar completion, seam closure, Phase 2 readiness,
  empirical adequacy, canonical ToE status, master-action promotion, QFT-GR
  source-map closure, or governance-manifest enrollment
- do not enroll this focused packet gate in the governance manifest
- remain an assumption map, not an attempted theorem discharge
-/

import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap

namespace ToeFormal
namespace Derivation
namespace QMStatEntropySemanticsSupportingAssumptionMap

open CrossPillarClosureFrontier
open CrossPillarDerivationProtocol
open FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the QM-STAT entropy-semantics supporting-assumption map. -/
def qmStatEntropySemanticsSupportingAssumptionMapSurfaceId : String :=
  "qm_stat_entropy_semantics_supporting_assumption_map_v0"

/-- Live target consumed by this assumption-map packet. -/
def qmStatEntropySemanticsSupportingAssumptionMapConsumedTargetId : String :=
  selectedFullPillarTargetMapNextTargetAfterQMStatEntropySemanticsGapV0

/-- Full-pillar selector token consumed by this assumption-map packet. -/
def qmStatEntropySemanticsSupportingAssumptionMapConsumedSelectorTokenId :
    String :=
  fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapResultTokenId

/-- Result token emitted by the supporting-assumption map. -/
def qmStatEntropySemanticsSupportingAssumptionMapResultTokenId : String :=
  "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_PREPARED"

/-- Next strict target after preparing the supporting-assumption map. -/
def qmStatEntropySemanticsSupportingAssumptionMapResultReviewTargetId :
    String :=
  "review_qm_stat_entropy_semantics_supporting_assumption_map_result"

/-- Canonical release report for this assumption-map packet. -/
def qmStatEntropySemanticsSupportingAssumptionMapReportPath : String :=
  "formal/docs/release/QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_20260510_v0.json"

/-- Focused validation target for this assumption-map packet. -/
def qmStatEntropySemanticsSupportingAssumptionMapValidationTarget : String :=
  "python -m pytest \
  formal/python/tests/test_qm_stat_entropy_semantics_supporting_assumption_map_gate.py -q"

/-- Allowed authority classifications for each supporting assumption row. -/
inductive QMStatEntropySemanticsAssumptionAuthority where
  | leanBacked
  | specBacked
  | suppliedOnly
  | blocked
  | notYetRepresented
deriving DecidableEq, Repr

/-- Stable external rendering for assumption authority classifications. -/
def qmStatEntropySemanticsAssumptionAuthorityId :
    QMStatEntropySemanticsAssumptionAuthority -> String
  | .leanBacked => "Lean-backed"
  | .specBacked => "spec-backed"
  | .suppliedOnly => "supplied-only"
  | .blocked => "blocked"
  | .notYetRepresented => "not yet represented"

/-- Minimum supporting-assumption classes for the target entropy semantics gap. -/
inductive QMStatEntropySemanticsSupportingAssumptionClass where
  | targetEntropyFunctionalDefinitionRequired
  | statisticalStateDomainSemanticsRequired
  | normalizationOrProbabilityMassConditionRequired
  | finiteSupportOrSummabilityConditionRequired
  | logDomainZeroHandlingConventionRequired
  | transportAlignmentRelationRequired
  | residualZeroBridgeConditionRequired
  | comparisonTargetSemanticsRequired
deriving DecidableEq, Repr

/-- Stable ids for supporting-assumption classes. -/
def qmStatEntropySemanticsSupportingAssumptionClassId :
    QMStatEntropySemanticsSupportingAssumptionClass -> String
  | .targetEntropyFunctionalDefinitionRequired =>
      "target_entropy_functional_definition_required"
  | .statisticalStateDomainSemanticsRequired =>
      "statistical_state_domain_semantics_required"
  | .normalizationOrProbabilityMassConditionRequired =>
      "normalization_or_probability_mass_condition_required"
  | .finiteSupportOrSummabilityConditionRequired =>
      "finite_support_or_summability_condition_required"
  | .logDomainZeroHandlingConventionRequired =>
      "log_domain_zero_handling_convention_required"
  | .transportAlignmentRelationRequired =>
      "transport_alignment_relation_required"
  | .residualZeroBridgeConditionRequired =>
      "residual_zero_bridge_condition_required"
  | .comparisonTargetSemanticsRequired =>
      "comparison_target_semantics_required"

/-- Human-readable labels for supporting-assumption classes. -/
def qmStatEntropySemanticsSupportingAssumptionClassLabel :
    QMStatEntropySemanticsSupportingAssumptionClass -> String
  | .targetEntropyFunctionalDefinitionRequired =>
      "target entropy functional definition required"
  | .statisticalStateDomainSemanticsRequired =>
      "statistical state/domain semantics required"
  | .normalizationOrProbabilityMassConditionRequired =>
      "normalization or probability-mass condition required"
  | .finiteSupportOrSummabilityConditionRequired =>
      "finite-support or summability condition required"
  | .logDomainZeroHandlingConventionRequired =>
      "log-domain / zero-handling convention required"
  | .transportAlignmentRelationRequired =>
      "transport/alignment relation required"
  | .residualZeroBridgeConditionRequired =>
      "residual-zero bridge condition required"
  | .comparisonTargetSemanticsRequired =>
      "comparison target semantics required"

/-- One row in the supporting-assumption map. -/
structure QMStatEntropySemanticsSupportingAssumptionRow where
  assumption_class : QMStatEntropySemanticsSupportingAssumptionClass
  class_id : String
  class_label : String
  authority : QMStatEntropySemanticsAssumptionAuthority
  authority_id : String
  existing_surface : String
  closure_requirement : String
  note : String

/-- `EntropyLike` and `TargetSTATEntropyStructure.entropy_weight` are present. -/
def targetEntropyFunctionalDefinitionAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .leanBacked

/-- Target/source semantics are currently supplied fields, not derived semantics. -/
def statisticalStateDomainSemanticsAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .suppliedOnly

/-- No normalized-probability or probability-mass condition is represented yet. -/
def normalizationOrProbabilityMassConditionAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .notYetRepresented

/-- The current transport/residual theorems are finite-state theorems. -/
def finiteSupportOrSummabilityConditionAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .leanBacked

/-- No log-domain or zero-handling convention is represented for target entropy. -/
def logDomainZeroHandlingConventionAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .notYetRepresented

/-- Transport/alignment is available as Lean-checked conditional structure. -/
def transportAlignmentRelationAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .leanBacked

/-- Residual-zero bridge lemmas are Lean-backed under finite supplied alignments. -/
def residualZeroBridgeConditionAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .leanBacked

/-- The comparison target semantics slot remains supplied-only. -/
def comparisonTargetSemanticsAuthorityV0 :
    QMStatEntropySemanticsAssumptionAuthority :=
  .suppliedOnly

/-- Minimum assumption rows required before stronger entropy-semantics authority. -/
def qmStatEntropySemanticsSupportingAssumptionRowsV0 :
    List QMStatEntropySemanticsSupportingAssumptionRow :=
  [ { assumption_class := .targetEntropyFunctionalDefinitionRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .targetEntropyFunctionalDefinitionRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .targetEntropyFunctionalDefinitionRequired
      authority := targetEntropyFunctionalDefinitionAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          targetEntropyFunctionalDefinitionAuthorityV0
      existing_surface :=
        "ToeFormal.Bridges.QMSTATTransport.EntropyLike; TargetSTATEntropyStructure.entropy_weight"
      closure_requirement :=
        "Fix the target entropy functional whose semantics are to be compared."
      note :=
        "A finite entropy-like functional is present; it is not yet a full target STAT semantics theorem." }
  , { assumption_class := .statisticalStateDomainSemanticsRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .statisticalStateDomainSemanticsRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .statisticalStateDomainSemanticsRequired
      authority := statisticalStateDomainSemanticsAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          statisticalStateDomainSemanticsAuthorityV0
      existing_surface :=
        "SourceQMEvolutionStructure.qm_evolution_semantics; TargetSTATEntropyStructure.stat_entropy_semantics"
      closure_requirement :=
        "Derive or explicitly justify the source and target state/domain semantics."
      note :=
        "The current state/domain semantics are supplied fields in the residual package." }
  , { assumption_class := .normalizationOrProbabilityMassConditionRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .normalizationOrProbabilityMassConditionRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .normalizationOrProbabilityMassConditionRequired
      authority := normalizationOrProbabilityMassConditionAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          normalizationOrProbabilityMassConditionAuthorityV0
      existing_surface :=
        "not represented in TargetSTATEntropyStructure"
      closure_requirement :=
        "Represent nonnegativity and total probability mass, or a documented alternate mass convention."
      note :=
        "The current target probability is a Real-valued function with no mass constraint." }
  , { assumption_class := .finiteSupportOrSummabilityConditionRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .finiteSupportOrSummabilityConditionRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .finiteSupportOrSummabilityConditionRequired
      authority := finiteSupportOrSummabilityConditionAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          finiteSupportOrSummabilityConditionAuthorityV0
      existing_surface :=
        "Fintype State requirements on EntropyLike, Moment, and residual-package theorems"
      closure_requirement :=
        "Stay finite-support or add an explicit summability/general-domain replacement."
      note :=
        "The current path is Lean-backed for finite state spaces only." }
  , { assumption_class := .logDomainZeroHandlingConventionRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .logDomainZeroHandlingConventionRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .logDomainZeroHandlingConventionRequired
      authority := logDomainZeroHandlingConventionAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          logDomainZeroHandlingConventionAuthorityV0
      existing_surface :=
        "not represented by EntropyLike's arbitrary weight"
      closure_requirement :=
        "Specify the logarithm domain and zero-probability convention for Shannon-style entropy."
      note :=
        "No log or zero-handling convention is currently encoded." }
  , { assumption_class := .transportAlignmentRelationRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .transportAlignmentRelationRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .transportAlignmentRelationRequired
      authority := transportAlignmentRelationAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          transportAlignmentRelationAuthorityV0
      existing_surface :=
        "QMSTATTransportMapStructure and finite equivalence transport lemmas"
      closure_requirement :=
        "Provide the actual transport/alignment instance for the selected QM-STAT target."
      note :=
        "The conditional transport machinery is Lean-backed; concrete target alignment remains an input." }
  , { assumption_class := .residualZeroBridgeConditionRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .residualZeroBridgeConditionRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .residualZeroBridgeConditionRequired
      authority := residualZeroBridgeConditionAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          residualZeroBridgeConditionAuthorityV0
      existing_surface :=
        "unified_transport_residual_zero_of_preservation; componentResidualEvidenceOfFiniteEquiv"
      closure_requirement :=
        "Bridge zero residual evidence to the target entropy semantics claim."
      note :=
        "Residual-zero evidence is Lean-backed conditionally, but the semantics bridge itself is not discharged." }
  , { assumption_class := .comparisonTargetSemanticsRequired
      class_id :=
        qmStatEntropySemanticsSupportingAssumptionClassId
          .comparisonTargetSemanticsRequired
      class_label :=
        qmStatEntropySemanticsSupportingAssumptionClassLabel
          .comparisonTargetSemanticsRequired
      authority := comparisonTargetSemanticsAuthorityV0
      authority_id :=
        qmStatEntropySemanticsAssumptionAuthorityId
          comparisonTargetSemanticsAuthorityV0
      existing_surface :=
        "TargetSTATEntropyStructure.stat_entropy_semantics_supplied"
      closure_requirement :=
        "Replace the supplied comparison target semantics with derived or otherwise stronger authority."
      note :=
        "This is the retained supplied-only gap mapped by this packet." }
  ]

/-- Allowed authority classification ids for release and gate parity. -/
def qmStatEntropySemanticsAllowedAuthorityClassificationsV0 : List String :=
  [ "Lean-backed"
  , "spec-backed"
  , "supplied-only"
  , "blocked"
  , "not yet represented"
  ]

/-- Status readout for the supporting-assumption map packet. -/
structure QMStatEntropySemanticsSupportingAssumptionMapStatus where
  map_consumes_live_target : Prop
  map_consumes_live_target_evidence : map_consumes_live_target
  selector_result_consumed : Prop
  selector_result_consumed_evidence : selector_result_consumed
  supplied_only_entropy_semantics_boundary_preserved : Prop
  supplied_only_entropy_semantics_boundary_preserved_evidence :
    supplied_only_entropy_semantics_boundary_preserved
  supporting_assumption_classes_mapped : Prop
  supporting_assumption_classes_mapped_evidence :
    supporting_assumption_classes_mapped
  allowed_authority_classifications_recorded : Prop
  allowed_authority_classifications_recorded_evidence :
    allowed_authority_classifications_recorded
  assumption_rows : List QMStatEntropySemanticsSupportingAssumptionRow
  assumption_class_count : Nat
  allowed_authority_classification_count : Nat
  result_token : String
  selected_next_target : String
  consumed_target : String
  consumed_selector_token : String
  selected_lane : String
  selected_gap_id : String
  source_selector_surface_id : String
  surface_id : String
  report_path : String
  validation_target : String
  map_attempts_theorem_discharge : Prop
  map_does_not_attempt_theorem_discharge :
    Not map_attempts_theorem_discharge
  target_entropy_semantics_lean_backed : Prop
  target_entropy_semantics_not_lean_backed :
    Not target_entropy_semantics_lean_backed
  target_entropy_semantics_supplied_only : Prop
  target_entropy_semantics_supplied_only_evidence :
    target_entropy_semantics_supplied_only
  theorem_gap_discharged : Prop
  theorem_gap_not_discharged : Not theorem_gap_discharged
  qm_stat_pillar_completion_inferred : Prop
  qm_stat_pillar_completion_not_inferred :
    Not qm_stat_pillar_completion_inferred
  seam_closure_inferred : Prop
  seam_closure_not_inferred : Not seam_closure_inferred
  phase2_readiness_claim : Prop
  phase2_readiness_not_claimed : Not phase2_readiness_claim
  empirical_adequacy_claim : Prop
  empirical_adequacy_not_claimed : Not empirical_adequacy_claim
  canonical_toe_claim : Prop
  canonical_toe_not_claimed : Not canonical_toe_claim
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  qft_gr_source_map_closure_authorized : Prop
  qft_gr_source_map_closure_not_authorized :
    Not qft_gr_source_map_closure_authorized
  governance_manifest_enrollment_authorized : Prop
  governance_manifest_enrollment_not_authorized :
    Not governance_manifest_enrollment_authorized
  status : DerivationStatus

/--
Current map: enumerate the supporting assumptions required for the supplied-only
target STAT entropy semantics gap without attempting to close the theorem.
-/
def qmStatEntropySemanticsSupportingAssumptionMapStatusV0 :
    QMStatEntropySemanticsSupportingAssumptionMapStatus where
  map_consumes_live_target := True
  map_consumes_live_target_evidence := True.intro
  selector_result_consumed :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.exactly_one_next_bounded_lane_selected
  selector_result_consumed_evidence :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.exactly_one_next_bounded_lane_selected_evidence
  supplied_only_entropy_semantics_boundary_preserved :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.target_entropy_semantics_supplied_only
  supplied_only_entropy_semantics_boundary_preserved_evidence :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence
  supporting_assumption_classes_mapped := True
  supporting_assumption_classes_mapped_evidence := True.intro
  allowed_authority_classifications_recorded := True
  allowed_authority_classifications_recorded_evidence := True.intro
  assumption_rows := qmStatEntropySemanticsSupportingAssumptionRowsV0
  assumption_class_count :=
    qmStatEntropySemanticsSupportingAssumptionRowsV0.length
  allowed_authority_classification_count :=
    qmStatEntropySemanticsAllowedAuthorityClassificationsV0.length
  result_token := qmStatEntropySemanticsSupportingAssumptionMapResultTokenId
  selected_next_target :=
    qmStatEntropySemanticsSupportingAssumptionMapResultReviewTargetId
  consumed_target := qmStatEntropySemanticsSupportingAssumptionMapConsumedTargetId
  consumed_selector_token :=
    qmStatEntropySemanticsSupportingAssumptionMapConsumedSelectorTokenId
  selected_lane :=
    selectedFullPillarTargetMapNextLaneAfterQMStatEntropySemanticsGapV0
  selected_gap_id :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.selected_gap_id
  source_selector_surface_id :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapSurfaceId
  surface_id := qmStatEntropySemanticsSupportingAssumptionMapSurfaceId
  report_path := qmStatEntropySemanticsSupportingAssumptionMapReportPath
  validation_target := qmStatEntropySemanticsSupportingAssumptionMapValidationTarget
  map_attempts_theorem_discharge := False
  map_does_not_attempt_theorem_discharge := by
    intro h
    exact h
  target_entropy_semantics_lean_backed :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.target_entropy_semantics_lean_backed
  target_entropy_semantics_not_lean_backed :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed
  target_entropy_semantics_supplied_only :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.target_entropy_semantics_supplied_only
  target_entropy_semantics_supplied_only_evidence :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence
  theorem_gap_discharged :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.theorem_gap_discharged
  theorem_gap_not_discharged :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.theorem_gap_not_discharged
  qm_stat_pillar_completion_inferred :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.qm_stat_pillar_completion_inferred
  qm_stat_pillar_completion_not_inferred :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred
  seam_closure_inferred :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.seam_closure_inferred
  seam_closure_not_inferred :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.seam_closure_not_inferred
  phase2_readiness_claim :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.phase2_readiness_claim
  phase2_readiness_not_claimed :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.phase2_readiness_not_claimed
  empirical_adequacy_claim :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.empirical_adequacy_claim
  empirical_adequacy_not_claimed :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.empirical_adequacy_not_claimed
  canonical_toe_claim :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.canonical_toe_claim
  canonical_toe_not_claimed :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.canonical_toe_not_claimed
  master_action_promoted :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.master_action_promoted
  master_action_not_promoted :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.master_action_not_promoted
  qft_gr_source_map_closure_authorized :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.qft_gr_source_map_closure_authorized
  qft_gr_source_map_closure_not_authorized :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized
  governance_manifest_enrollment_authorized :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.governance_manifest_enrollment_authorized
  governance_manifest_enrollment_not_authorized :=
    fullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized
  status := .retained

/-- Public readout for the assumption-map packet. -/
def qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0 :
    QMStatEntropySemanticsSupportingAssumptionMapStatus :=
  qmStatEntropySemanticsSupportingAssumptionMapStatusV0

theorem qm_stat_entropy_semantics_supporting_assumption_map_consumes_live_target_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.consumed_target) =
      "prepare_qm_stat_entropy_semantics_supporting_assumption_map" := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_consumes_selector_token_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.consumed_selector_token) =
      "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP" := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_result_token_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.result_token) =
      "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_PREPARED" := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_next_target_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.selected_next_target) =
      "review_qm_stat_entropy_semantics_supporting_assumption_map_result" := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_selected_lane_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.selected_lane) =
      "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP" := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_selected_gap_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.selected_gap_id) =
      "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0" := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_row_count_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.assumption_class_count) =
      8 := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_authority_class_count_v0 :
    (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.allowed_authority_classification_count) =
      5 := by
  rfl

theorem target_entropy_functional_definition_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      targetEntropyFunctionalDefinitionAuthorityV0 =
      "Lean-backed" := by
  rfl

theorem statistical_state_domain_semantics_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      statisticalStateDomainSemanticsAuthorityV0 =
      "supplied-only" := by
  rfl

theorem normalization_or_probability_mass_condition_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      normalizationOrProbabilityMassConditionAuthorityV0 =
      "not yet represented" := by
  rfl

theorem finite_support_or_summability_condition_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      finiteSupportOrSummabilityConditionAuthorityV0 =
      "Lean-backed" := by
  rfl

theorem log_domain_zero_handling_convention_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      logDomainZeroHandlingConventionAuthorityV0 =
      "not yet represented" := by
  rfl

theorem transport_alignment_relation_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      transportAlignmentRelationAuthorityV0 =
      "Lean-backed" := by
  rfl

theorem residual_zero_bridge_condition_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      residualZeroBridgeConditionAuthorityV0 =
      "Lean-backed" := by
  rfl

theorem comparison_target_semantics_authority_v0 :
    qmStatEntropySemanticsAssumptionAuthorityId
      comparisonTargetSemanticsAuthorityV0 =
      "supplied-only" := by
  rfl

theorem qm_stat_entropy_semantics_supporting_assumption_map_supplied_only_preserved_v0 :
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.target_entropy_semantics_supplied_only := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence

theorem qm_stat_entropy_semantics_supporting_assumption_map_does_not_attempt_discharge_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.map_attempts_theorem_discharge) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.map_does_not_attempt_theorem_discharge

theorem qm_stat_entropy_semantics_supporting_assumption_map_no_lean_backed_discharge_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.target_entropy_semantics_lean_backed) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed

theorem qm_stat_entropy_semantics_supporting_assumption_map_no_gap_closure_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.theorem_gap_discharged) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.theorem_gap_not_discharged

theorem qm_stat_entropy_semantics_supporting_assumption_map_no_qm_stat_completion_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.qm_stat_pillar_completion_inferred) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred

theorem qm_stat_entropy_semantics_supporting_assumption_map_no_seam_closure_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.seam_closure_inferred) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.seam_closure_not_inferred

theorem qm_stat_entropy_semantics_supporting_assumption_map_no_phase2_readiness_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.phase2_readiness_claim) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.phase2_readiness_not_claimed

theorem qm_stat_entropy_semantics_supporting_assumption_map_no_empirical_adequacy_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.empirical_adequacy_claim) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.empirical_adequacy_not_claimed

theorem qm_stat_entropy_semantics_supporting_assumption_map_no_canonical_toe_claim_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.canonical_toe_claim) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.canonical_toe_not_claimed

theorem qm_stat_entropy_semantics_supporting_assumption_map_master_action_not_promoted_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.master_action_not_promoted

theorem qm_stat_entropy_semantics_supporting_assumption_map_qft_gr_not_authorized_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.qft_gr_source_map_closure_authorized) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized

theorem qm_stat_entropy_semantics_supporting_assumption_map_manifest_not_enrolled_v0 :
    Not
      (qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact
    qmStatEntropySemanticsSupportingAssumptionMapStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized

end QMStatEntropySemanticsSupportingAssumptionMap
end Derivation
end ToeFormal
