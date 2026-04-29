/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianConcreteTaylorRemainder.lean

Concrete Taylor-remainder theorem-facing slice for the A1A graph-Laplacian
channel after the local/polynomial capstone.

Scope:
- expose the available mathlib one-dimensional Taylor remainder bound at
  order three
- prove the algebraic bridge from a centered-numerator residual estimate to
  the scaled stencil bound already used by the A1A remainder route
- record that the missing work is the symmetric two-sided Taylor-to-centered
  stencil bridge, not another polynomial/local subclass
- keep full A1A closure, A2A15A1 closure, Phase 2 authorization, continuum
  closure, seam closure, empirical validation, and master-action promotion out
  of scope
-/

import Mathlib.Analysis.Calculus.Taylor
import ToeFormal.QFT.ContinuumSpatialGraphLaplacianChannelCapstone

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianConcreteTaylorRemainder

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl
open ContinuumSpatialGraphLaplacianFourthDerivativeRemainder
open ContinuumSpatialGraphLaplacianChannelCapstone

set_option autoImplicit false

noncomputable section

/-- Retained blocker for the concrete Taylor-to-symmetric-stencil bridge. -/
def phase1Blocker003A2A15A1A7ConcreteTaylorRemainderRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A7_CONCRETE_TAYLOR_REMAINDER_" ++
    "TO_SYMMETRIC_STENCIL_BRIDGE_RETAINED"

/-- Outcome id for this theorem-facing Taylor remainder slice. -/
def graphLaplacianConcreteTaylorRemainderOutcomeId : String :=
  "CONCRETE_TAYLOR_ORDER3_REMAINDER_BOUND_AVAILABLE_" ++
    "SYMMETRIC_STENCIL_BRIDGE_RETAINED"

/--
Mathlib's one-dimensional Taylor theorem gives the order-three remainder
bound on a closed interval from a fourth-derivative bound.
-/
theorem concrete_taylor_order_three_remainder_bound
    {f : Real -> Real}
    {a b C x : Real}
    (hab : a ≤ b)
    (hf : ContDiffOn Real (3 + 1) f (Set.Icc a b))
    (hx : x ∈ Set.Icc a b)
    (hC :
      ∀ y ∈ Set.Icc a b,
        ‖iteratedDerivWithin (3 + 1) f (Set.Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f 3 (Set.Icc a b) a x‖ ≤
      C * (x - a) ^ (3 + 1) / (Nat.factorial 3 : Real) := by
  exact taylor_mean_remainder_bound (n := 3) hab hf hx hC

/--
If Taylor analysis supplies a bound on the centered residual numerator at
scale `|h*h|`, then the existing scaled-stencil remainder condition follows.
-/
theorem scaled_stencil_bound_of_centered_numerator_abs_bound
    (h epsilon : Real)
    (remainder : ContinuumField ThreePointStencil)
    (h_nonzero : h * h ≠ 0)
    (hbound :
      |centeredGraphLaplacianNumerator remainder| ≤
        epsilon * |h * h|) :
    scaledStencilRemainderErrorBound h remainder epsilon := by
  unfold scaledStencilRemainderErrorBound
  have hden_pos : 0 < |h * h| := abs_pos.mpr h_nonzero
  calc
    |centeredGraphLaplacianNumerator remainder / (h * h)| =
        |centeredGraphLaplacianNumerator remainder| / |h * h| := by
          exact abs_div _ _
    _ ≤ (epsilon * |h * h|) / |h * h| := by
          exact div_le_div_of_nonneg_right hbound (le_of_lt hden_pos)
    _ = epsilon := by
          have hden_ne : |h ^ 2| ≠ 0 := by
            simpa [pow_two] using (ne_of_gt hden_pos)
          field_simp [hden_ne]

/--
Bridge data still needed to turn the concrete order-three Taylor bound into
the exact three-point stencil remainder bound required by A1A.
-/
structure ConcreteTaylorRemainderStencilBridge
    (h epsilon : Real)
    (remainder : ContinuumField ThreePointStencil) where
  order_three_taylor_remainder_bound_available : Prop
  order_three_taylor_remainder_bound_available_supplied :
    order_three_taylor_remainder_bound_available
  two_sided_basepoint_alignment : Prop
  two_sided_basepoint_alignment_supplied :
    two_sided_basepoint_alignment
  sample_reconstruction_matches_taylor_polynomial : Prop
  sample_reconstruction_matches_taylor_polynomial_supplied :
    sample_reconstruction_matches_taylor_polynomial
  symmetric_endpoint_remainder_estimates : Prop
  symmetric_endpoint_remainder_estimates_supplied :
    symmetric_endpoint_remainder_estimates
  centered_numerator_bound_from_taylor_remainders :
    |centeredGraphLaplacianNumerator remainder| ≤
      epsilon * |h * h|

/--
Once the symmetric-stencil Taylor bridge data is supplied, it gives the prior
scale-normalized stencil bound.
-/
theorem concrete_taylor_stencil_bridge_supplies_scaled_bound
    (h epsilon : Real)
    (remainder : ContinuumField ThreePointStencil)
    (h_nonzero : h * h ≠ 0)
    (bridge :
      ConcreteTaylorRemainderStencilBridge h epsilon remainder) :
    scaledStencilRemainderErrorBound h remainder epsilon := by
  exact scaled_stencil_bound_of_centered_numerator_abs_bound
    h epsilon remainder h_nonzero
    bridge.centered_numerator_bound_from_taylor_remainders

/-- The bridge data can feed the prior TaylorRemainderControl object. -/
def taylorRemainderControlOfConcreteTaylorStencilBridge
    (h epsilon : Real)
    (remainder : ContinuumField ThreePointStencil)
    (h_nonzero : h * h ≠ 0)
    (fourthDerivativeBound : Real)
    (fourthDerivativeBoundNonnegative : 0 ≤ fourthDerivativeBound)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (bridge :
      ConcreteTaylorRemainderStencilBridge h epsilon remainder) :
    TaylorRemainderControl h remainder epsilon where
  differentiability_order := 4
  differentiability_order_at_least_four := by norm_num
  bounded_fourth_derivative_or_equiv_smoothness :=
    bridge.order_three_taylor_remainder_bound_available
  bounded_fourth_derivative_or_equiv_smoothness_supplied :=
    bridge.order_three_taylor_remainder_bound_available_supplied
  fourth_derivative_bound := fourthDerivativeBound
  fourth_derivative_bound_nonnegative := fourthDerivativeBoundNonnegative
  local_interval_model := bridge.two_sided_basepoint_alignment
  local_interval_model_supplied := bridge.two_sided_basepoint_alignment_supplied
  mesh_scale := |h|
  mesh_scale_matches_spacing := rfl
  refinement_parameter := refinementParameter
  refinement_parameter_positive := refinementParameterPositive
  refinement_scale_compatible :=
    bridge.sample_reconstruction_matches_taylor_polynomial
  refinement_scale_compatible_supplied :=
    bridge.sample_reconstruction_matches_taylor_polynomial_supplied
  scale_normalized_remainder_bound :=
    concrete_taylor_stencil_bridge_supplies_scaled_bound
      h epsilon remainder h_nonzero bridge

/-- Remaining obstructions after importing the concrete Taylor bound. -/
inductive ConcreteTaylorRemainderObstruction where
  | noTwoSidedBasepointAlignment
  | noSampleTaylorPolynomialCompatibility
  | noSymmetricEndpointRemainderEstimate
  | noUniformMeshConvergence
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the concrete Taylor obstruction list. -/
def concreteTaylorRemainderObstructionId :
    ConcreteTaylorRemainderObstruction -> String
  | .noTwoSidedBasepointAlignment =>
      "A2A15A1A7_OBSTRUCTION_NO_TWO_SIDED_BASEPOINT_ALIGNMENT"
  | .noSampleTaylorPolynomialCompatibility =>
      "A2A15A1A7_OBSTRUCTION_NO_SAMPLE_TAYLOR_POLYNOMIAL_COMPATIBILITY"
  | .noSymmetricEndpointRemainderEstimate =>
      "A2A15A1A7_OBSTRUCTION_NO_SYMMETRIC_ENDPOINT_REMAINDER_ESTIMATE"
  | .noUniformMeshConvergence =>
      "A2A15A1A7_OBSTRUCTION_NO_UNIFORM_MESH_CONVERGENCE"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A7_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A7_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A7_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction inventory for the concrete Taylor remainder slice. -/
def concreteTaylorRemainderObstructionsV0 :
    List ConcreteTaylorRemainderObstruction :=
  [ .noTwoSidedBasepointAlignment
  , .noSampleTaylorPolynomialCompatibility
  , .noSymmetricEndpointRemainderEstimate
  , .noUniformMeshConvergence
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The concrete Taylor obstruction inventory is stable and explicit. -/
theorem concrete_taylor_remainder_obstructions_v0_expected :
    concreteTaylorRemainderObstructionsV0 =
      [ .noTwoSidedBasepointAlignment
      , .noSampleTaylorPolynomialCompatibility
      , .noSymmetricEndpointRemainderEstimate
      , .noUniformMeshConvergence
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This theorem-facing slice records a concrete obstruction. -/
def concreteTaylorRemainderSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with theorem imports above. -/
theorem concrete_taylor_remainder_successor_kinds_v0_expected :
    concreteTaylorRemainderSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the concrete Taylor remainder slice. -/
structure ConcreteTaylorRemainderStatus where
  order_three_taylor_bound_available : Prop
  order_three_taylor_bound_available_supplied :
    order_three_taylor_bound_available
  centered_numerator_to_scaled_bound_proved : Prop
  centered_numerator_to_scaled_bound_proved_supplied :
    centered_numerator_to_scaled_bound_proved
  symmetric_stencil_taylor_bridge_proved : Prop
  symmetric_stencil_taylor_bridge_not_proved :
    Not symmetric_stencil_taylor_bridge_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_a1a_capstone_outcome_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the order-three Taylor bound and numerator-to-scaled-bound
algebra are available, while the symmetric-stencil Taylor bridge remains open.
-/
def concreteTaylorRemainderStatusV0 :
    ConcreteTaylorRemainderStatus where
  order_three_taylor_bound_available := True
  order_three_taylor_bound_available_supplied := True.intro
  centered_numerator_to_scaled_bound_proved := True
  centered_numerator_to_scaled_bound_proved_supplied := True.intro
  symmetric_stencil_taylor_bridge_proved := False
  symmetric_stencil_taylor_bridge_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_a1a_capstone_outcome_id :=
    graphLaplacianChannelCapstoneOutcomeId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A7ConcreteTaylorRemainderRetainedId
  outcome_id := graphLaplacianConcreteTaylorRemainderOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := concreteTaylorRemainderSuccessorKindsV0
  obstruction_ids :=
    concreteTaylorRemainderObstructionsV0.map
      concreteTaylorRemainderObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def concreteTaylorRemainderStatusReadoutV0 :
    ConcreteTaylorRemainderStatus :=
  concreteTaylorRemainderStatusV0

/-- The concrete order-three Taylor remainder bound is available. -/
theorem concrete_taylor_remainder_order_three_bound_available_v0 :
    ConcreteTaylorRemainderStatus.order_three_taylor_bound_available
      concreteTaylorRemainderStatusReadoutV0 := by
  exact
    ConcreteTaylorRemainderStatus.order_three_taylor_bound_available_supplied
      concreteTaylorRemainderStatusReadoutV0

/-- The centered-numerator-to-scaled-bound algebra is proved. -/
theorem concrete_taylor_remainder_centered_to_scaled_proved_v0 :
    ConcreteTaylorRemainderStatus.centered_numerator_to_scaled_bound_proved
      concreteTaylorRemainderStatusReadoutV0 := by
  exact
    ConcreteTaylorRemainderStatus.centered_numerator_to_scaled_bound_proved_supplied
      concreteTaylorRemainderStatusReadoutV0

/-- The symmetric-stencil Taylor bridge remains retained. -/
theorem concrete_taylor_remainder_symmetric_bridge_not_proved_v0 :
    Not
      (ConcreteTaylorRemainderStatus.symmetric_stencil_taylor_bridge_proved
        concreteTaylorRemainderStatusReadoutV0) := by
  exact
    ConcreteTaylorRemainderStatus.symmetric_stencil_taylor_bridge_not_proved
      concreteTaylorRemainderStatusReadoutV0

/-- The concrete Taylor slice does not close full A1A. -/
theorem concrete_taylor_remainder_full_a1a_not_closed_v0 :
    Not
      (ConcreteTaylorRemainderStatus.full_a1a_channel_closed
        concreteTaylorRemainderStatusReadoutV0) := by
  exact
    ConcreteTaylorRemainderStatus.full_a1a_channel_not_closed
      concreteTaylorRemainderStatusReadoutV0

/-- The parent A1A retained blocker remains exposed. -/
theorem concrete_taylor_remainder_parent_retained_id_v0 :
    concreteTaylorRemainderStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior A1A capstone outcome remains exposed. -/
theorem concrete_taylor_remainder_prior_capstone_outcome_id_v0 :
    concreteTaylorRemainderStatusReadoutV0.prior_a1a_capstone_outcome_id =
      graphLaplacianChannelCapstoneOutcomeId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem concrete_taylor_remainder_retained_id_v0 :
    concreteTaylorRemainderStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A7ConcreteTaylorRemainderRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem concrete_taylor_remainder_outcome_id_v0 :
    concreteTaylorRemainderStatusReadoutV0.outcome_id =
      graphLaplacianConcreteTaylorRemainderOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem concrete_taylor_remainder_anti_loop_rule_id_v0 :
    concreteTaylorRemainderStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem concrete_taylor_remainder_successor_kinds_v0 :
    concreteTaylorRemainderStatusReadoutV0.successor_kinds =
      concreteTaylorRemainderSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A slice. -/
theorem concrete_taylor_remainder_phase2_not_authorized_v0 :
    Not concreteTaylorRemainderStatusReadoutV0.phase2Authorized := by
  exact concreteTaylorRemainderStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianConcreteTaylorRemainder
end QFT
end ToeFormal
