/-
ToeFormal/QFT/ContinuumAnalyticBlocker003.lean

Bounded split of PHASE1-BLOCKER-003: retained continuum analytic obligations.

Scope:
- name the retained continuum analytic sub-obligations
- expose which sub-obligations are consumed by the landed continuum
  first-variation route
- prove the small bookkeeping bridge from the split bundle back to
  `ContinuumFirstVariationObligations`
- prove that the boundary-term sub-obligation is exactly sufficient for the
  already-landed integration-by-parts identity
- no claim that boundary vanishing, operator-domain closure, residual
  separation, or smoothness/admissibility has been analytically discharged
- no Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumFirstVariation

namespace ToeFormal
namespace QFT
namespace ContinuumAnalyticBlocker003

open ContinuumFirstVariation
set_option autoImplicit false

noncomputable section

/-- Named sub-obligations for PHASE1-BLOCKER-003. -/
inductive ContinuumAnalyticSubObligation where
  | boundaryTermVanishing
  | operatorDomainClosure
  | residualSeparation
  | smoothnessAdmissibleVariation
  | integrationLinearity
deriving DecidableEq, Repr

/-- Status labels used for the bounded Blocker 003 split. -/
inductive ContinuumAnalyticSubObligationStatus where
  | retained
  | dischargedConditional
  | open
deriving DecidableEq, Repr

/--
Phase 1 Blocker 003 split readout.

The `integrationLinearity` entry is included because the current continuum
first-variation theorem needs it alongside the four user-facing analytic
obligations.
-/
structure Phase1Blocker003Split where
  boundaryTermVanishingStatus : ContinuumAnalyticSubObligationStatus
  operatorDomainClosureStatus : ContinuumAnalyticSubObligationStatus
  residualSeparationStatus : ContinuumAnalyticSubObligationStatus
  smoothnessAdmissibleVariationStatus : ContinuumAnalyticSubObligationStatus
  integrationLinearityStatus : ContinuumAnalyticSubObligationStatus
  phase2Authorized : Prop

/-- Current bounded adjudication: split landed, analytic assumptions retained, Phase 2 held. -/
def phase1Blocker003SplitV0 : Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the Blocker 003 split readout. -/
theorem phase1_blocker003_phase2_not_authorized :
    ¬ phase1Blocker003SplitV0.phase2Authorized := by
  intro h
  exact h

/-- The primary four continuum analytic sub-obligations are named explicitly. -/
def primaryContinuumAnalyticSubObligations :
    List ContinuumAnalyticSubObligation :=
  [ ContinuumAnalyticSubObligation.boundaryTermVanishing
  , ContinuumAnalyticSubObligation.operatorDomainClosure
  , ContinuumAnalyticSubObligation.residualSeparation
  , ContinuumAnalyticSubObligation.smoothnessAdmissibleVariation
  ]

/-- The support obligation required by the existing algebraic route. -/
def supportContinuumAnalyticSubObligations :
    List ContinuumAnalyticSubObligation :=
  [ContinuumAnalyticSubObligation.integrationLinearity]

/-- The current split has the expected four primary sub-obligations. -/
theorem phase1_blocker003_primary_split_has_expected_obligations :
    primaryContinuumAnalyticSubObligations =
      [ ContinuumAnalyticSubObligation.boundaryTermVanishing
      , ContinuumAnalyticSubObligation.operatorDomainClosure
      , ContinuumAnalyticSubObligation.residualSeparation
      , ContinuumAnalyticSubObligation.smoothnessAdmissibleVariation
      ] := by
  rfl

/-- Boundary-term sub-obligation, using the existing boundary model object. -/
structure BoundaryTermVanishingSubObligation {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point) where
  boundary_model : BoundaryTermModel integral operator

/--
Operator-domain/closure sub-obligation represented by operator linearity in
the current theorem.
-/
structure OperatorDomainClosureSubObligation {Point : Type}
    (operator : ContinuumField Point → ContinuumField Point) where
  operator_linear : LinearOperator operator

/-- Residual-separation sub-obligation, using the existing separation principle object. -/
structure ResidualSeparationSubObligation {Point : Type}
    (integral : ContinuumField Point → Real) where
  separation : SeparationPrinciple integral

/-- Integration-linearity support obligation used by the current algebraic expansion. -/
structure IntegrationLinearitySubObligation {Point : Type}
    (integral : ContinuumField Point → Real) where
  integral_linear : LinearIntegral integral

/--
Smoothness/admissible-variation sub-obligation.

This is retained as inventory because the current continuum algebraic theorem
is still abstract in `Point` and has not instantiated a concrete function space.
-/
structure SmoothnessAdmissibleVariationSubObligation (Point : Type) where
  inventory : ContinuumAssumptionInventory Point

/--
Bundle of named Blocker 003 sub-obligations sufficient to recover the existing
continuum first-variation obligation bundle.
-/
structure Phase1Blocker003AnalyticBundle {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point) where
  boundary : BoundaryTermVanishingSubObligation integral operator
  operator_domain : OperatorDomainClosureSubObligation operator
  residual_separation : ResidualSeparationSubObligation integral
  integration_linearity : IntegrationLinearitySubObligation integral
  smoothness_admissible_variation :
    SmoothnessAdmissibleVariationSubObligation Point

/--
Bookkeeping discharge: the named Blocker 003 analytic bundle reconstructs the
continuum obligation bundle consumed by `ContinuumFirstVariation.lean`.
-/
def continuumObligationsOfBlocker003Bundle {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (bundle : Phase1Blocker003AnalyticBundle integral operator) :
    ContinuumFirstVariationObligations integral operator where
  integral_linear := bundle.integration_linearity.integral_linear
  operator_linear := bundle.operator_domain.operator_linear
  boundary_model := bundle.boundary.boundary_model
  separation := bundle.residual_separation.separation

/-- The reconstructed obligations preserve the boundary model from the split bundle. -/
theorem blocker003_bundle_preserves_boundary_model {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (bundle : Phase1Blocker003AnalyticBundle integral operator) :
    (continuumObligationsOfBlocker003Bundle integral operator bundle).boundary_model =
      bundle.boundary.boundary_model := by
  rfl

/-- The reconstructed obligations preserve the residual separation principle. -/
theorem blocker003_bundle_preserves_residual_separation {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (bundle : Phase1Blocker003AnalyticBundle integral operator) :
    (continuumObligationsOfBlocker003Bundle integral operator bundle).separation =
      bundle.residual_separation.separation := by
  rfl

/--
Small conditional discharge: a boundary-term sub-obligation is exactly
sufficient for the existing continuum integration-by-parts identity.
-/
theorem boundary_subobligation_suffices_for_integration_by_parts {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (boundary : BoundaryTermVanishingSubObligation integral operator)
    (x y : ContinuumField Point) :
    ContinuumPair integral x (operator y) =
      ContinuumPair integral y (operator x) := by
  exact continuum_integration_by_parts_from_boundary_vanishing
    integral operator boundary.boundary_model x y

end
end ContinuumAnalyticBlocker003
end QFT
end ToeFormal
