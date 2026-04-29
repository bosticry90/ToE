/-
ToeFormal/QFT/ContinuumSpatialAnalyticIntervalLiftAssembly.lean

A2A15A1 analytic interval-lift assembly/readout surface for
ANALYTIC_INTERVAL_LIFT_CHANNELS_SPLIT_COMPLETE_BUT_RETAINED.

Scope:
- confirm that the three A2A15A1 convergence channels have been structurally
  represented by named retained surfaces
- record that A1A, A1B, A1C, A2A15A1, and A2A15 all remain retained
- record the anti-loop successor rule: no more child splits under A2A15A1
  unless a successor proves a channel, falsifies a channel, or records a
  concrete obstruction
- name A1A graph-Laplacian to continuum Laplacian as the next
  theorem-producing target
- keep analytic convergence, continuum Green identity closure, Phase 2
  authorization, seam closure, empirical validation, and master-action
  promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialRawIBPToGreenIdentityConvergence

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialAnalyticIntervalLiftAssembly

open ContinuumAnalyticBlocker003
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialEndpointFluxConvergence
open ContinuumSpatialRawIBPToGreenIdentityConvergence
set_option autoImplicit false

noncomputable section

/-- Machine-facing readout id for the completed A2A15A1 channel split. -/
def analyticIntervalLiftChannelsSplitCompleteButRetainedId : String :=
  "ANALYTIC_INTERVAL_LIFT_CHANNELS_SPLIT_COMPLETE_BUT_RETAINED"

/-- Anti-loop rule id for post-capstone A2A15A1 successors. -/
def analyticIntervalLiftNoMoreChildSplitsRuleId : String :=
  "A2A15A1_NO_MORE_CHILD_SPLITS_WITHOUT_PROOF_FALSIFICATION_" ++
    "OR_CONCRETE_OBSTRUCTION"

/-- Parent retained A2A15A1 blocker id. -/
def phase1Blocker003A2A15A1AssemblyRetainedId : String :=
  phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId

/-- Parent retained A2A15 boundary-flux blocker id. -/
def phase1Blocker003A2A15AssemblyParentRetainedId : String :=
  phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId

/-- The three convergence channels under A2A15A1. -/
inductive AnalyticIntervalLiftChannel where
  | graphLaplacianToContinuumLaplacian
  | finiteEndpointFluxToContinuumBoundaryFlux
  | finiteRawIBPToContinuumGreenIdentity
deriving DecidableEq, Repr

/-- Retained blocker ids for the three already-split A2A15A1 channels. -/
def analyticIntervalLiftChannelRetainedId :
    AnalyticIntervalLiftChannel -> String
  | .graphLaplacianToContinuumLaplacian =>
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  | .finiteEndpointFluxToContinuumBoundaryFlux =>
      phase1Blocker003A2A15A1BFiniteEndpointFluxToContinuumBoundaryFluxRetainedId
  | .finiteRawIBPToContinuumGreenIdentity =>
      phase1Blocker003A2A15A1CFiniteRawIBPToContinuumGreenIdentityRetainedId

/-- Exact A2A15A1 channel inventory. -/
def analyticIntervalLiftChannelsV0 :
    List AnalyticIntervalLiftChannel :=
  [ .graphLaplacianToContinuumLaplacian
  , .finiteEndpointFluxToContinuumBoundaryFlux
  , .finiteRawIBPToContinuumGreenIdentity
  ]

/-- The A2A15A1 channel inventory contains exactly A1A, A1B, and A1C. -/
theorem analytic_interval_lift_channels_v0_expected :
    analyticIntervalLiftChannelsV0 =
      [ .graphLaplacianToContinuumLaplacian
      , .finiteEndpointFluxToContinuumBoundaryFlux
      , .finiteRawIBPToContinuumGreenIdentity
      ] := by
  rfl

/-- The retained channel ids match the three A2A15A1 retained blockers. -/
theorem analytic_interval_lift_channel_retained_ids_v0_expected :
    analyticIntervalLiftChannelsV0.map
        analyticIntervalLiftChannelRetainedId =
      [ phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
      , phase1Blocker003A2A15A1BFiniteEndpointFluxToContinuumBoundaryFluxRetainedId
      , phase1Blocker003A2A15A1CFiniteRawIBPToContinuumGreenIdentityRetainedId
      ] := by
  rfl

/-- Allowed post-capstone successor kinds under the A2A15A1 anti-loop rule. -/
inductive A2A15A1SuccessorKind where
  | provesChannel
  | falsifiesChannel
  | recordsConcreteObstruction
deriving DecidableEq, Repr

/-- Exact anti-loop successor allowance. -/
def allowedA2A15A1SuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel
  , .falsifiesChannel
  , .recordsConcreteObstruction
  ]

/-- The post-capstone rule allows only proof, falsification, or obstruction. -/
theorem allowed_a2a15a1_successor_kinds_v0_expected :
    allowedA2A15A1SuccessorKindsV0 =
      [ .provesChannel
      , .falsifiesChannel
      , .recordsConcreteObstruction
      ] := by
  rfl

/-- The recommended next theorem-producing target after the capstone readout. -/
inductive A2A15A1NextTheoremTarget where
  | graphLaplacianToContinuumLaplacian
deriving DecidableEq, Repr

/-- A1A is the next target because it is upstream of flux and Green identity. -/
def a2a15a1RecommendedNextTheoremTargetV0 :
    A2A15A1NextTheoremTarget :=
  .graphLaplacianToContinuumLaplacian

/--
Assembly/readout for the A2A15A1 analytic interval-lift channel split.

This readout is intentionally weaker than an analytic interval-lift theorem:
it says the three transfer channels are represented and retained, not that
analytic evidence has been supplied.
-/
structure AnalyticIntervalLiftChannelsAssemblyReadout where
  graph_laplacian_channel_status :
    GraphLaplacianToContinuumLaplacianChannelStatus
  endpoint_flux_channel_status :
    FiniteEndpointFluxToContinuumBoundaryFluxChannelStatus
  raw_ibp_green_channel_status :
    FiniteRawIBPToContinuumGreenIdentityChannelStatus
  all_three_channels_structurally_represented : Prop
  all_three_channels_structurally_represented_supplied :
    all_three_channels_structurally_represented
  all_three_channels_retained : Prop
  all_three_channels_retained_supplied : all_three_channels_retained
  analytic_interval_lift_closed : Prop
  analytic_interval_lift_not_closed :
    Not analytic_interval_lift_closed
  a2a15_boundary_flux_parent_closed : Prop
  a2a15_boundary_flux_parent_not_closed :
    Not a2a15_boundary_flux_parent_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  retained_a2a15a1_blocker_id : String
  retained_a2a15_blocker_id : String
  readout_id : String
  anti_loop_rule_id : String
  allowed_successor_kinds : List A2A15A1SuccessorKind
  recommended_next_theorem_target : A2A15A1NextTheoremTarget

/--
Current readout: A1A/A1B/A1C are represented, all three remain retained, the
parent analytic interval lift remains retained, and Phase 2 remains
unauthorized.
-/
def analyticIntervalLiftChannelsAssemblyReadoutV0 :
    AnalyticIntervalLiftChannelsAssemblyReadout where
  graph_laplacian_channel_status := graphLaplacianChannelStatusV0
  endpoint_flux_channel_status := endpointFluxChannelStatusV0
  raw_ibp_green_channel_status := rawIBPGreenChannelStatusV0
  all_three_channels_structurally_represented := True
  all_three_channels_structurally_represented_supplied := True.intro
  all_three_channels_retained := True
  all_three_channels_retained_supplied := True.intro
  analytic_interval_lift_closed := False
  analytic_interval_lift_not_closed := by
    intro h
    exact h
  a2a15_boundary_flux_parent_closed := False
  a2a15_boundary_flux_parent_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  retained_a2a15a1_blocker_id :=
    phase1Blocker003A2A15A1AssemblyRetainedId
  retained_a2a15_blocker_id :=
    phase1Blocker003A2A15AssemblyParentRetainedId
  readout_id :=
    analyticIntervalLiftChannelsSplitCompleteButRetainedId
  anti_loop_rule_id :=
    analyticIntervalLiftNoMoreChildSplitsRuleId
  allowed_successor_kinds := allowedA2A15A1SuccessorKindsV0
  recommended_next_theorem_target := a2a15a1RecommendedNextTheoremTargetV0

/-- Short proof-facing status alias. -/
def analyticIntervalLiftChannelsReadoutV0 :
    AnalyticIntervalLiftChannelsAssemblyReadout :=
  analyticIntervalLiftChannelsAssemblyReadoutV0

/-- The readout confirms that all three A2A15A1 channels are represented. -/
theorem analytic_interval_lift_channels_split_complete_v0 :
    analyticIntervalLiftChannelsReadoutV0.all_three_channels_structurally_represented := by
  exact
    analyticIntervalLiftChannelsReadoutV0.all_three_channels_structurally_represented_supplied

/-- The readout records that all three A2A15A1 channels remain retained. -/
theorem analytic_interval_lift_channels_split_retained_v0 :
    analyticIntervalLiftChannelsReadoutV0.all_three_channels_retained := by
  exact analyticIntervalLiftChannelsReadoutV0.all_three_channels_retained_supplied

/-- The imported A1A/A1B/A1C statuses all keep their channel theorems open. -/
theorem analytic_interval_lift_channel_statuses_not_closed_v0 :
    Not graphLaplacianChannelStatusV0.graph_laplacian_convergence_closed /\
    Not endpointFluxChannelStatusV0.endpoint_flux_convergence_closed /\
    Not rawIBPGreenChannelStatusV0.raw_ibp_green_identity_convergence_closed := by
  exact
    ⟨ graphLaplacianChannelStatusV0.graph_laplacian_convergence_not_closed
    , endpointFluxChannelStatusV0.endpoint_flux_convergence_not_closed
    , rawIBPGreenChannelStatusV0.raw_ibp_green_identity_convergence_not_closed
    ⟩

/-- The parent analytic interval lift remains retained. -/
theorem analytic_interval_lift_assembly_parent_lift_not_closed_v0 :
    Not analyticIntervalLiftChannelsReadoutV0.analytic_interval_lift_closed := by
  exact analyticIntervalLiftChannelsReadoutV0.analytic_interval_lift_not_closed

/-- The A2A15 boundary-flux parent remains retained. -/
theorem analytic_interval_lift_assembly_a2a15_parent_not_closed_v0 :
    Not analyticIntervalLiftChannelsReadoutV0.a2a15_boundary_flux_parent_closed := by
  exact
    analyticIntervalLiftChannelsReadoutV0.a2a15_boundary_flux_parent_not_closed

/-- The assembly readout exposes the expected machine-facing id. -/
theorem analytic_interval_lift_assembly_readout_id_v0 :
    analyticIntervalLiftChannelsReadoutV0.readout_id =
      analyticIntervalLiftChannelsSplitCompleteButRetainedId := by
  rfl

/-- The assembly readout keeps A2A15A1 retained. -/
theorem analytic_interval_lift_assembly_a2a15a1_still_retained_v0 :
    analyticIntervalLiftChannelsReadoutV0.retained_a2a15a1_blocker_id =
      phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId := by
  rfl

/-- The assembly readout keeps A2A15 retained. -/
theorem analytic_interval_lift_assembly_a2a15_still_retained_v0 :
    analyticIntervalLiftChannelsReadoutV0.retained_a2a15_blocker_id =
      phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId := by
  rfl

/-- The assembly readout pins the post-capstone anti-loop rule. -/
theorem analytic_interval_lift_assembly_anti_loop_rule_id_v0 :
    analyticIntervalLiftChannelsReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- Post-capstone successors are limited to proof, falsification, obstruction. -/
theorem analytic_interval_lift_assembly_allowed_successors_v0 :
    analyticIntervalLiftChannelsReadoutV0.allowed_successor_kinds =
      allowedA2A15A1SuccessorKindsV0 := by
  rfl

/-- The assembly readout points next to A1A theorem-producing work. -/
theorem analytic_interval_lift_assembly_next_target_a1a_v0 :
    analyticIntervalLiftChannelsReadoutV0.recommended_next_theorem_target =
      A2A15A1NextTheoremTarget.graphLaplacianToContinuumLaplacian := by
  rfl

/-- Phase 2 remains unauthorized after the A2A15A1 assembly readout. -/
theorem analytic_interval_lift_assembly_phase2_not_authorized_v0 :
    Not analyticIntervalLiftChannelsReadoutV0.phase2Authorized := by
  exact analyticIntervalLiftChannelsReadoutV0.phase2_not_authorized

/--
003A2A15A1 assembly readout.  The analytic interval-lift channel split is
complete as inventory, but all analytic closure obligations remain retained.
-/
def phase1Blocker003A2A15A1ChannelsAssemblyReadoutV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- The parent blocker readout also records that Phase 2 is unauthorized. -/
theorem phase1_blocker003a2a15a1_channels_assembly_phase2_not_authorized :
    Not phase1Blocker003A2A15A1ChannelsAssemblyReadoutV0.phase2Authorized := by
  intro h
  exact h

end

end ContinuumSpatialAnalyticIntervalLiftAssembly
end QFT
end ToeFormal
