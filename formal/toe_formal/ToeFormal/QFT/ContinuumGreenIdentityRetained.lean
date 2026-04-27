/-
ToeFormal/QFT/ContinuumGreenIdentityRetained.lean

Named scalar Green-identity surface for PHASE1-BLOCKER-003A.

Scope:
- select the scalar kinetic boundary problem as the boundary-term target
- define the compact-support or boundary-decay class by trace vanishing
- prove the trace-vanishing class supplies the trace-zero condition required
  by `ContinuumBoundaryTermModel.lean`
- instantiate the two-sided compact-support/decay boundary surface from a
  retained Green identity
- record the exact retained boundary sub-blocker:
  `PHASE1-BLOCKER-003A_GREEN_IDENTITY_RETAINED`
- keep concrete differential operator analysis, operator-domain closure,
  residual separation, and Phase 2 authorization out of scope
-/

import ToeFormal.QFT.ContinuumBoundaryTermModel

namespace ToeFormal
namespace QFT
namespace ContinuumGreenIdentityRetained

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumBoundaryTermModel
set_option autoImplicit false

noncomputable section

/-- The selected scalar operator lane for the current boundary target. -/
inductive ScalarBoundaryOperatorKind where
  | kineticBox
deriving DecidableEq, Repr

/-- The selected function-space lane for the current boundary target. -/
inductive ScalarBoundaryFunctionSpaceKind where
  | smoothCompactSupportOrDecay
deriving DecidableEq, Repr

/-- Exact retained sub-blocker id for the Green identity. -/
def phase1Blocker003AGreenIdentityRetainedId : String :=
  "PHASE1-BLOCKER-003A_GREEN_IDENTITY_RETAINED"

/--
Named scalar kinetic boundary problem.

The operator is the kinetic operator used in the continuum scalar action.  The
mass term is not part of the boundary flux route.
-/
structure ScalarKineticBoundaryProblem (Point : Type) where
  operator_kind : ScalarBoundaryOperatorKind
  function_space_kind : ScalarBoundaryFunctionSpaceKind
  integral : ContinuumField Point → Real
  kineticOperator : ContinuumField Point → ContinuumField Point
  trace : TwoSidedBoundaryTrace Point
  FieldSmooth : ContinuumField Point → Prop
  InOperatorDomain : ContinuumField Point → Prop

/-- The selected bounded target uses the kinetic operator and smooth decay class. -/
structure ScalarKineticBoundaryProblemSelected {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point) where
  operator_kind_selected :
    problem.operator_kind = ScalarBoundaryOperatorKind.kineticBox
  function_space_kind_selected :
    problem.function_space_kind =
      ScalarBoundaryFunctionSpaceKind.smoothCompactSupportOrDecay

/--
Compact support or boundary decay, represented at this boundary layer by
vanishing endpoint traces.
-/
def TraceVanishingCompactSupportOrDecay {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (f : ContinuumField Point) : Prop :=
  problem.trace.leftTrace f = 0 ∧ problem.trace.rightTrace f = 0

/-- The trace-vanishing decay class supplies the required zero boundary traces. -/
theorem trace_vanishing_compact_support_decay_has_zero_traces {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (f : ContinuumField Point)
    (hf : TraceVanishingCompactSupportOrDecay problem f) :
    problem.trace.leftTrace f = 0 ∧ problem.trace.rightTrace f = 0 := by
  exact hf

/--
Retained Green identity for the selected scalar kinetic boundary problem.

This is the exact remaining boundary sub-blocker after the trace-vanishing
part is made mechanical.
-/
structure Phase1Blocker003AGreenIdentityRetained {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point) where
  blocker_id :
    phase1Blocker003AGreenIdentityRetainedId =
      "PHASE1-BLOCKER-003A_GREEN_IDENTITY_RETAINED"
  selected : ScalarKineticBoundaryProblemSelected problem
  green_identity :
    ∀ x y : ContinuumField Point,
      problem.InOperatorDomain x →
      problem.InOperatorDomain y →
        ContinuumPair problem.integral x (problem.kineticOperator y) =
          ContinuumPair problem.integral y (problem.kineticOperator x) +
            twoSidedBoundaryFlux problem.trace x y

/--
Closed restricted field universe for the selected boundary problem.

This remains retained because the current `BoundaryTermModel` API quantifies
over the full field type; the chosen theorem domain must therefore already be
the restricted compact-support/decay universe.
-/
structure ClosedScalarKineticBoundaryUniverse {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point) where
  all_fields_smooth :
    ∀ f : ContinuumField Point, problem.FieldSmooth f
  all_fields_decay :
    ∀ f : ContinuumField Point,
      TraceVanishingCompactSupportOrDecay problem f
  all_fields_in_operator_domain :
    ∀ f : ContinuumField Point, problem.InOperatorDomain f

/-- Boundary surface generated from the retained scalar kinetic Green identity. -/
def scalarKineticBoundarySurfaceOfRetainedGreenIdentity {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (green : Phase1Blocker003AGreenIdentityRetained problem) :
    TwoSidedCompactSupportDecayBoundarySurface
      problem.integral problem.kineticOperator where
  FieldSmooth := problem.FieldSmooth
  CompactSupportOrBoundaryDecay :=
    TraceVanishingCompactSupportOrDecay problem
  InOperatorDomain := problem.InOperatorDomain
  trace := problem.trace
  green_identity := green.green_identity
  trace_zero_of_decay := by
    intro f hf
    exact trace_vanishing_compact_support_decay_has_zero_traces problem f hf

/-- Closed field universe induced by the selected scalar boundary universe. -/
def closedFieldUniverseOfScalarKineticBoundaryProblem {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (green : Phase1Blocker003AGreenIdentityRetained problem)
    (closed : ClosedScalarKineticBoundaryUniverse problem) :
    ClosedCompactSupportDecayFieldUniverse
      (scalarKineticBoundarySurfaceOfRetainedGreenIdentity problem green) where
  all_fields_smooth := closed.all_fields_smooth
  all_fields_decay := closed.all_fields_decay
  all_fields_in_operator_domain := closed.all_fields_in_operator_domain

/-- The retained Green identity yields the boundary model for the selected surface. -/
def scalarKineticBoundaryTermModelOfRetainedGreenIdentity {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (green : Phase1Blocker003AGreenIdentityRetained problem)
    (closed : ClosedScalarKineticBoundaryUniverse problem) :
    BoundaryTermModel problem.integral problem.kineticOperator :=
  boundaryTermModelOfCompactSupportDecaySurface
    (scalarKineticBoundarySurfaceOfRetainedGreenIdentity problem green)
    (closedFieldUniverseOfScalarKineticBoundaryProblem problem green closed)

/--
The named scalar kinetic Green-identity route is sufficient for the
integration-by-parts identity consumed by the scalar first-variation theorem.
-/
theorem scalar_kinetic_retained_green_identity_suffices_for_ibp {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (green : Phase1Blocker003AGreenIdentityRetained problem)
    (closed : ClosedScalarKineticBoundaryUniverse problem)
    (x y : ContinuumField Point) :
    ContinuumPair problem.integral x (problem.kineticOperator y) =
      ContinuumPair problem.integral y (problem.kineticOperator x) := by
  exact compact_support_decay_boundary_surface_suffices_for_ibp
    problem.integral problem.kineticOperator
    (scalarKineticBoundarySurfaceOfRetainedGreenIdentity problem green)
    (closedFieldUniverseOfScalarKineticBoundaryProblem problem green closed)
    x y

/--
Blocker 003A readout: the trace-vanishing part is mechanical, but the concrete
Green identity and closed field universe are retained.  Phase 2 remains held.
-/
def phase1Blocker003AGreenIdentityRetainedV0 : Phase1Blocker003Split where
  boundaryTermVanishingStatus := .dischargedConditional
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized while Blocker 003A is retained. -/
theorem phase1_blocker003a_green_identity_retained_phase2_not_authorized :
    ¬ phase1Blocker003AGreenIdentityRetainedV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumGreenIdentityRetained
end QFT
end ToeFormal
