/-
ToeFormal/QFT/ContinuumPairingLimitAnchoredSeminormSeparationObstruction.lean

Bounded A1A1A1A anchored-seminorm separation obstruction.

Scope:
- prove that anchored evaluation cannot globally separate all fields when the
  point space has a point distinct from the anchor
- show the trivial/subsingleton case where global anchored separation can hold
- define the restricted-field-class route that can make anchored separation
  meaningful without claiming a full field topology
- define the stronger-norm route as the other retained escape hatch
- do not prove pairing compatibility, analytic convergence, continuum pairing
  limit, measure compatibility, quadrature/density, Green identity discharge,
  operator-domain closure, residual separation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumPairingLimitFieldTopologyNormSeparationCompatibility

namespace ToeFormal
namespace QFT
namespace ContinuumPairingLimitAnchoredSeminormSeparationObstruction

open ContinuumAnalyticBlocker003
open ContinuumFirstVariation
open ContinuumPairingLimitFieldTopologyNorm
open ContinuumPairingLimitFieldTopologyNormDischargeAttempt
open ContinuumPairingLimitFieldTopologyNormSeparationCompatibility
set_option autoImplicit false

noncomputable section

/-- Retained id for the anchored-seminorm separation obstruction. -/
def phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationRetainedId :
    String :=
  "PHASE1-BLOCKER-003A1A1C3A1A1A1A1_ANCHORED_SEMINORM_\
  SEPARATION_REQUIRES_RESTRICTED_FIELD_CLASS_OR_STRONGER_NORM"

/-- Machine-facing outcome id for this bounded obstruction slice. -/
def anchoredSeminormSeparationObstructionOutcomeId : String :=
  "ANCHORED_SEMINORM_NOT_GLOBAL_SEPARATING_WITHOUT_RESTRICTED_FIELD_CLASS"

/-- Parent A1A1A1A blocker narrowed by this slice. -/
def phase1Blocker003A1A1C3A1A1A1A1ParentCompatibilityBlockerId :
    String :=
  phase1Blocker003A1A1C3A1A1A1ASeparationOrPairingCompatibilityRetainedId

/-- Remaining objects after recording the anchored-seminorm separation obstruction. -/
inductive Phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationMissingObject where
  | restrictedFieldClass
  | strongerSeparatingNorm
  | pairingCompatibilityAfterSeparation
  | splitFieldEvidence
deriving DecidableEq, Repr

/-- Machine-facing retained ids for the remaining A1A1A1A1 objects. -/
def phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationMissingObjectId :
    Phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationMissingObject ->
      String
  | .restrictedFieldClass =>
      "003A1A1C3A1A1A1A1_RESTRICTED_FIELD_CLASS_RETAINED"
  | .strongerSeparatingNorm =>
      "003A1A1C3A1A1A1A1_STRONGER_SEPARATING_NORM_RETAINED"
  | .pairingCompatibilityAfterSeparation =>
      "003A1A1C3A1A1A1A1_PAIRING_COMPATIBILITY_AFTER_SEPARATION_RETAINED"
  | .splitFieldEvidence =>
      "003A1A1C3A1A1A1A1_SPLIT_FIELD_EVIDENCE_RETAINED"

/-- Exact retained object list after this bounded obstruction slice. -/
def phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationMissingObjectsV0 :
    List Phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationMissingObject :=
  [ .restrictedFieldClass
  , .strongerSeparatingNorm
  , .pairingCompatibilityAfterSeparation
  , .splitFieldEvidence
  ]

/-- The retained object list is explicit. -/
theorem phase1_blocker003a1a1c3a1a1a1a1_missing_objects_v0_expected :
    phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationMissingObjectsV0 =
      [ .restrictedFieldClass
      , .strongerSeparatingNorm
      , .pairingCompatibilityAfterSeparation
      , .splitFieldEvidence
      ] := by
  rfl

/-- A point space has a point away from the chosen anchor. -/
def HasPointAwayFromAnchor
    {Point : Type}
    (anchor : Point) : Prop :=
  ∃ other : Point, other ≠ anchor

/-- A field that is zero at the anchor and nonzero at `other`. -/
noncomputable def spikeAwayFromAnchor
    {Point : Type}
    (other : Point) : ContinuumField Point :=
  fun p => by
    classical
    exact if p = other then 1 else 0

/-- The spike has value zero at the anchor when `other` is distinct. -/
theorem spike_away_from_anchor_value_at_anchor_zero
    {Point : Type}
    (anchor other : Point)
    (hOther : other ≠ anchor) :
    spikeAwayFromAnchor other anchor = 0 := by
  classical
  have hAnchor : anchor ≠ other := by
    intro h
    exact hOther h.symm
  simp [spikeAwayFromAnchor, hAnchor]

/-- The spike has value one at its selected point. -/
theorem spike_away_from_anchor_value_at_other
    {Point : Type}
    (other : Point) :
    spikeAwayFromAnchor other other = 1 := by
  classical
  simp [spikeAwayFromAnchor]

/-- The zero field and the spike have anchored distance zero. -/
theorem anchored_distance_zero_to_spike_away_from_anchor
    {Point : Type}
    (anchor other : Point)
    (hOther : other ≠ anchor) :
    anchoredEvaluationFieldDistance
      anchor (fun _ : Point => 0) (spikeAwayFromAnchor other) = 0 := by
  classical
  have hAnchor : anchor ≠ other := by
    intro h
    exact hOther h.symm
  simp [anchoredEvaluationFieldDistance, fieldDistanceOfNorm,
    anchoredEvaluationSeminorm, spikeAwayFromAnchor, hAnchor]

/-- The zero field is distinct from the spike. -/
theorem zero_field_ne_spike_away_from_anchor
    {Point : Type}
    (other : Point) :
    (fun _ : Point => 0) ≠ spikeAwayFromAnchor other := by
  classical
  intro h
  have hValue :=
    congrArg (fun field : ContinuumField Point => field other) h
  simp [spikeAwayFromAnchor] at hValue

/-- Anchored evaluation is not globally separating on a space with another point. -/
theorem anchored_seminorm_not_global_separating_of_distinct_point
    {Point : Type}
    (anchor other : Point)
    (hOther : other ≠ anchor) :
    Not (AnchoredSeminormSeparationUpgrade anchor) := by
  intro hSep
  have hDistance :=
    anchored_distance_zero_to_spike_away_from_anchor anchor other hOther
  have hEq :=
    hSep (fun _ : Point => 0) (spikeAwayFromAnchor other) hDistance
  exact zero_field_ne_spike_away_from_anchor other hEq

/-- If there is a point away from the anchor, global anchored separation fails. -/
theorem anchored_seminorm_not_global_separating_of_has_point_away
    {Point : Type}
    (anchor : Point)
    (hAway : HasPointAwayFromAnchor anchor) :
    Not (AnchoredSeminormSeparationUpgrade anchor) := by
  rcases hAway with ⟨other, hOther⟩
  exact anchored_seminorm_not_global_separating_of_distinct_point
    anchor other hOther

/-- Global anchored separation forces the absence of points away from the anchor. -/
theorem anchored_global_separation_requires_no_point_away
    {Point : Type}
    (anchor : Point)
    (hSep : AnchoredSeminormSeparationUpgrade anchor) :
    Not (HasPointAwayFromAnchor anchor) := by
  intro hAway
  exact anchored_seminorm_not_global_separating_of_has_point_away
    anchor hAway hSep

/-- On a subsingleton point space, the anchored seminorm is separating. -/
theorem anchored_seminorm_separating_of_subsingleton
    {Point : Type}
    [Subsingleton Point]
    (anchor : Point) :
    AnchoredSeminormSeparationUpgrade anchor := by
  intro x y hDistance
  funext p
  have hp : p = anchor := Subsingleton.elim p anchor
  subst p
  have hAbs : |x anchor - y anchor| = 0 := by
    simpa [anchoredEvaluationFieldDistance, fieldDistanceOfNorm,
      anchoredEvaluationSeminorm] using hDistance
  have hDiff : x anchor - y anchor = 0 := abs_eq_zero.mp hAbs
  exact sub_eq_zero.mp hDiff

/-- Restricted separation for a field class rather than all fields. -/
def AnchoredRestrictedFieldClassSeparation
    {Point : Type}
    (anchor : Point)
    (FieldClass : ContinuumField Point -> Prop) : Prop :=
  ∀ x y : ContinuumField Point,
    FieldClass x ->
      FieldClass y ->
        anchoredEvaluationFieldDistance anchor x y = 0 ->
          x = y

/-- A field class is determined by the anchored value. -/
def FieldClassDeterminedByAnchor
    {Point : Type}
    (anchor : Point)
    (FieldClass : ContinuumField Point -> Prop) : Prop :=
  ∀ field : ContinuumField Point,
    FieldClass field ->
      ∀ p : Point, field p = field anchor

/-- A field class determined by the anchor gives restricted anchored separation. -/
theorem anchored_restricted_separation_of_determined_by_anchor
    {Point : Type}
    (anchor : Point)
    (FieldClass : ContinuumField Point -> Prop)
    (hDetermined : FieldClassDeterminedByAnchor anchor FieldClass) :
    AnchoredRestrictedFieldClassSeparation anchor FieldClass := by
  intro x y hx hy hDistance
  have hAbs : |x anchor - y anchor| = 0 := by
    simpa [anchoredEvaluationFieldDistance, fieldDistanceOfNorm,
      anchoredEvaluationSeminorm] using hDistance
  have hAnchor : x anchor = y anchor := by
    have hDiff : x anchor - y anchor = 0 := abs_eq_zero.mp hAbs
    exact sub_eq_zero.mp hDiff
  funext p
  calc
    x p = x anchor := hDetermined x hx p
    _ = y anchor := hAnchor
    _ = y p := (hDetermined y hy p).symm

/-- A stronger norm can carry its own separation condition. -/
def StrongerFieldNormSeparationUpgrade
    {Point : Type}
    (fieldNorm : ContinuumField Point -> Real) : Prop :=
  ∀ x y : ContinuumField Point,
    fieldDistanceOfNorm fieldNorm x y = 0 -> x = y

/-- The stronger-norm separation condition is exactly the supplied property. -/
theorem stronger_field_norm_separation_supplies_upgrade
    {Point : Type}
    (fieldNorm : ContinuumField Point -> Real)
    (hSep : StrongerFieldNormSeparationUpgrade fieldNorm) :
    ∀ x y : ContinuumField Point,
      fieldDistanceOfNorm fieldNorm x y = 0 -> x = y := by
  exact hSep

/-- Current repository status for the anchored-seminorm separation obstruction. -/
structure AnchoredSeminormSeparationObstructionStatus where
  counterexample_for_two_point_space_closed : Prop
  counterexample_for_two_point_space_closed_supplied :
    counterexample_for_two_point_space_closed
  restricted_field_class_route_defined : Prop
  restricted_field_class_route_defined_supplied :
    restricted_field_class_route_defined
  stronger_norm_route_defined : Prop
  stronger_norm_route_defined_supplied :
    stronger_norm_route_defined
  unconditional_global_separation_closed : Prop
  unconditional_global_separation_not_closed :
    Not unconditional_global_separation_closed
  pairing_compatibility_after_separation_closed : Prop
  pairing_compatibility_after_separation_not_closed :
    Not pairing_compatibility_after_separation_closed
  retained_blocker_id : String
  parent_compatibility_blocker_id : String
  outcome_id : String

/--
Current status: the counterexample and the restricted/stronger alternatives are
recorded, but no global separating field topology is supplied.
-/
def anchoredSeminormSeparationObstructionStatusV0 :
    AnchoredSeminormSeparationObstructionStatus where
  counterexample_for_two_point_space_closed := True
  counterexample_for_two_point_space_closed_supplied := True.intro
  restricted_field_class_route_defined := True
  restricted_field_class_route_defined_supplied := True.intro
  stronger_norm_route_defined := True
  stronger_norm_route_defined_supplied := True.intro
  unconditional_global_separation_closed := False
  unconditional_global_separation_not_closed := by
    intro h
    exact h
  pairing_compatibility_after_separation_closed := False
  pairing_compatibility_after_separation_not_closed := by
    intro h
    exact h
  retained_blocker_id :=
    phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationRetainedId
  parent_compatibility_blocker_id :=
    phase1Blocker003A1A1C3A1A1A1A1ParentCompatibilityBlockerId
  outcome_id := anchoredSeminormSeparationObstructionOutcomeId

/-- Short local status alias. -/
def anchoredSeparationStatusV0 :
    AnchoredSeminormSeparationObstructionStatus :=
  anchoredSeminormSeparationObstructionStatusV0

/-- The counterexample route is mechanically closed. -/
theorem anchored_separation_counterexample_status_closed_v0 :
    anchoredSeparationStatusV0.counterexample_for_two_point_space_closed := by
  exact anchoredSeparationStatusV0.counterexample_for_two_point_space_closed_supplied

/-- The restricted-field-class route is now defined. -/
theorem anchored_separation_restricted_class_route_defined_v0 :
    anchoredSeparationStatusV0.restricted_field_class_route_defined := by
  exact anchoredSeparationStatusV0.restricted_field_class_route_defined_supplied

/-- The stronger-norm route is now defined. -/
theorem anchored_separation_stronger_norm_route_defined_v0 :
    anchoredSeparationStatusV0.stronger_norm_route_defined := by
  exact anchoredSeparationStatusV0.stronger_norm_route_defined_supplied

/-- Unconditional global anchored separation remains retained. -/
theorem anchored_separation_unconditional_global_not_closed_v0 :
    Not anchoredSeparationStatusV0.unconditional_global_separation_closed := by
  exact anchoredSeparationStatusV0.unconditional_global_separation_not_closed

/-- Pairing compatibility after separation remains retained for the branch. -/
theorem anchored_separation_pairing_compat_after_not_closed_v0 :
    Not anchoredSeparationStatusV0.pairing_compatibility_after_separation_closed := by
  exact anchoredSeparationStatusV0.pairing_compatibility_after_separation_not_closed

/-- The slice exposes the expected retained sub-blocker id. -/
theorem anchored_separation_obstruction_retained_id_v0 :
    anchoredSeparationStatusV0.retained_blocker_id =
      phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationRetainedId := by
  rfl

/-- The slice remains below the A1A1A1A compatibility blocker. -/
theorem anchored_separation_obstruction_parent_id_v0 :
    anchoredSeparationStatusV0.parent_compatibility_blocker_id =
      phase1Blocker003A1A1C3A1A1A1ASeparationOrPairingCompatibilityRetainedId := by
  rfl

/-- The slice exposes the expected outcome id. -/
theorem anchored_separation_obstruction_outcome_id_v0 :
    anchoredSeparationStatusV0.outcome_id =
      anchoredSeminormSeparationObstructionOutcomeId := by
  rfl

/--
003A1A1C3A1A1A1A1 readout. The anchored seminorm is not globally separating
on nontrivial point spaces; a restricted field class or stronger norm is needed.
-/
def phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized after this bounded obstruction slice. -/
theorem phase1_blocker003a1a1c3a1a1a1a1_anchored_separation_v0_phase2_not_authorized :
    Not
      phase1Blocker003A1A1C3A1A1A1A1AnchoredSeparationV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumPairingLimitAnchoredSeminormSeparationObstruction
end QFT
end ToeFormal
