/-
ToeFormal/QFT/ContinuumPairingLimitFiniteDomainSupNorm.lean

Bounded A1A1A1A2A1 finite-domain sup norm construction.

Scope:
- define a concrete finite-domain sup norm on a nonempty finite weighted
  approximation domain
- prove the finite sup-like laws: nonnegativity, zero iff equality on the
  finite domain, homogeneity, and triangle inequality
- connect the finite-domain sup norm to the prior sup-like field norm
  candidate route
- record that this is finite-domain only and does not construct a continuum
  sup norm, continuum topology-generation theorem, finite-to-continuum
  pairing-limit theorem, or Phase 2 authorization
-/

import Mathlib.Algebra.Order.GroupWithZero.Finset
import ToeFormal.QFT.ContinuumPairingLimitSupLikeFieldNormCandidate
import ToeFormal.QFT.ContinuumFiniteWeightedIntegralModel

namespace ToeFormal
namespace QFT
namespace ContinuumPairingLimitFiniteDomainSupNorm

open ContinuumAnalyticBlocker003
open ContinuumFirstVariation
open ContinuumFiniteApproximationScheme
open ContinuumFiniteWeightedIntegralModel
open ContinuumPairingLimitAnalyticStructureSplit
open ContinuumPairingLimitFieldTopologyNorm
open ContinuumPairingLimitSupLikeFieldNormCandidate
set_option autoImplicit false

noncomputable section

/-- Retained id for the continuum sup norm still missing after the finite proof. -/
def phase1Blocker003A1A1C3A1A1A1A2A1ContinuumSupNormRetainedId :
    String :=
  "PHASE1-BLOCKER-003A1A1C3A1A1A1A2A1_CONTINUUM_SUP_NORM_RETAINED"

/-- Machine-facing outcome id for this bounded finite-domain sup norm slice. -/
def finiteDomainSupNormOutcomeId : String :=
  "FINITE_DOMAIN_SUP_NORM_SUP_LIKE_LAWS_DISCHARGED_CONTINUUM_SUP_RETAINED"

/-- Parent sup-like candidate blocker narrowed by this slice. -/
def phase1Blocker003A1A1C3A1A1A1A2A1ParentSupLikeBlockerId :
    String :=
  phase1Blocker003A1A1C3A1A1A1A2ASupLikeFieldNormRetainedId

/-- Remaining objects after the finite-domain sup norm laws are proved. -/
inductive Phase1Blocker003A1A1C3A1A1A1A2A1FiniteSupRemainingObject where
  | continuumSupNormDefinition
  | continuumBoundedFieldClass
  | continuumTopologyGeneratedBySupNorm
  | finiteToContinuumSupNormCompatibility
  | analyticPairingCompatibility
deriving DecidableEq, Repr

/-- Machine-facing retained ids after this finite-domain sup norm slice. -/
def phase1Blocker003A1A1C3A1A1A1A2A1FiniteSupRemainingObjectId :
    Phase1Blocker003A1A1C3A1A1A1A2A1FiniteSupRemainingObject ->
      String
  | .continuumSupNormDefinition =>
      "003A1A1C3A1A1A1A2A1_CONTINUUM_SUP_NORM_DEFINITION_RETAINED"
  | .continuumBoundedFieldClass =>
      "003A1A1C3A1A1A1A2A1_CONTINUUM_BOUNDED_FIELD_CLASS_RETAINED"
  | .continuumTopologyGeneratedBySupNorm =>
      "003A1A1C3A1A1A1A2A1_CONTINUUM_SUP_TOPOLOGY_RETAINED"
  | .finiteToContinuumSupNormCompatibility =>
      "003A1A1C3A1A1A1A2A1_FINITE_TO_CONTINUUM_SUP_COMPAT_RETAINED"
  | .analyticPairingCompatibility =>
      "003A1A1C3A1A1A1A2A1_ANALYTIC_PAIRING_COMPATIBILITY_RETAINED"

/-- Exact retained object list after this bounded finite-domain sup norm proof. -/
def phase1Blocker003A1A1C3A1A1A1A2A1FiniteSupRemainingObjectsV0 :
    List Phase1Blocker003A1A1C3A1A1A1A2A1FiniteSupRemainingObject :=
  [ .continuumSupNormDefinition
  , .continuumBoundedFieldClass
  , .continuumTopologyGeneratedBySupNorm
  , .finiteToContinuumSupNormCompatibility
  , .analyticPairingCompatibility
  ]

/-- The retained continuum-side object list is explicit. -/
theorem phase1_blocker003a1a1c3a1a1a1a2a1_remaining_objects_v0_expected :
    phase1Blocker003A1A1C3A1A1A1A2A1FiniteSupRemainingObjectsV0 =
      [ .continuumSupNormDefinition
      , .continuumBoundedFieldClass
      , .continuumTopologyGeneratedBySupNorm
      , .finiteToContinuumSupNormCompatibility
      , .analyticPairingCompatibility
      ] := by
  rfl

/-- Finite-domain sup norm over a nonempty finite weighted domain. -/
def finiteDomainSupNorm
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (_domain : FiniteWeightedBaseDomain Point)
    (field : ContinuumField Point) : Real :=
  (Finset.univ : Finset Point).sup'
    Finset.univ_nonempty
    (fun p : Point => |field p|)

/-- The finite-domain sup norm is nonnegative. -/
theorem finite_domain_sup_norm_nonnegative
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point)
    (field : ContinuumField Point) :
    0 <= finiteDomainSupNorm domain field := by
  let p : Point := Classical.choice inferInstance
  have hp : p ∈ (Finset.univ : Finset Point) := Finset.mem_univ p
  exact (abs_nonneg (field p)).trans
    (by
      simpa [finiteDomainSupNorm] using
        (Finset.le_sup'
          (s := (Finset.univ : Finset Point))
          (f := fun q : Point => |field q|)
          hp))

/-- Zero finite-domain sup norm means pointwise zero on the finite domain. -/
theorem finite_domain_sup_norm_zero_iff_eq
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point)
    (field : ContinuumField Point) :
    finiteDomainSupNorm domain field = 0 <->
      field = fun _ : Point => (0 : Real) := by
  constructor
  · intro hZero
    have hLe : finiteDomainSupNorm domain field <= 0 := by
      simp [hZero]
    have hAll :
        ∀ p ∈ (Finset.univ : Finset Point), |field p| <= 0 := by
      exact
        (Finset.sup'_le_iff
          (s := (Finset.univ : Finset Point))
          (H := Finset.univ_nonempty)
          (f := fun p : Point => |field p|)
          (a := 0)).mp
          (by simpa [finiteDomainSupNorm] using hLe)
    funext p
    have hpAbs : |field p| = 0 := by
      exact le_antisymm (hAll p (Finset.mem_univ p)) (abs_nonneg (field p))
    exact abs_eq_zero.mp hpAbs
  · intro hField
    have hLe : finiteDomainSupNorm domain field <= 0 := by
      apply
        (Finset.sup'_le_iff
          (s := (Finset.univ : Finset Point))
          (H := Finset.univ_nonempty)
          (f := fun p : Point => |field p|)
          (a := 0)).mpr
      intro p _hp
      simp [hField]
    exact le_antisymm hLe
      (finite_domain_sup_norm_nonnegative domain field)

/-- The finite-domain sup norm is homogeneous over real scalars. -/
theorem finite_domain_sup_norm_homogeneity
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point)
    (c : Real)
    (field : ContinuumField Point) :
    finiteDomainSupNorm domain (fun p : Point => c * field p) =
      |c| * finiteDomainSupNorm domain field := by
  by_cases hAbsZero : |c| = 0
  · have hCZero : c = 0 := abs_eq_zero.mp hAbsZero
    subst c
    simp [finiteDomainSupNorm]
  · have hAbsPos : 0 < |c| := by
      exact lt_of_le_of_ne (abs_nonneg c) (by
        intro h
        exact hAbsZero h.symm)
    calc
      finiteDomainSupNorm domain (fun p : Point => c * field p)
          =
        (Finset.univ : Finset Point).sup'
          Finset.univ_nonempty
          (fun p : Point => |c| * |field p|) := by
            simp [finiteDomainSupNorm, abs_mul]
      _ = |c| * finiteDomainSupNorm domain field := by
            rw [← Finset.mul₀_sup'
              (a := |c|)
              (ha := hAbsPos)
              (f := fun p : Point => |field p|)
              (s := (Finset.univ : Finset Point))
              (hs := Finset.univ_nonempty)]
            rfl

/-- The finite-domain sup norm satisfies the triangle inequality. -/
theorem finite_domain_sup_norm_triangle
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point)
    (x y : ContinuumField Point) :
    finiteDomainSupNorm domain (fun p : Point => x p + y p) <=
      finiteDomainSupNorm domain x + finiteDomainSupNorm domain y := by
  apply
    (Finset.sup'_le_iff
      (s := (Finset.univ : Finset Point))
      (H := Finset.univ_nonempty)
      (f := fun p : Point => |x p + y p|)
      (a := finiteDomainSupNorm domain x + finiteDomainSupNorm domain y)).mpr
  intro p hp
  have hx :
      |x p| <= finiteDomainSupNorm domain x := by
    simpa [finiteDomainSupNorm] using
      (Finset.le_sup'
        (s := (Finset.univ : Finset Point))
        (f := fun q : Point => |x q|)
        hp)
  have hy :
      |y p| <= finiteDomainSupNorm domain y := by
    simpa [finiteDomainSupNorm] using
      (Finset.le_sup'
        (s := (Finset.univ : Finset Point))
        (f := fun q : Point => |y q|)
        hp)
  exact (abs_add_le (x p) (y p)).trans (add_le_add hx hy)

/-- The finite-domain sup norm satisfies the sup-like law package. -/
theorem finite_domain_sup_norm_sup_like_laws
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point) :
    SupLikeFieldNormLaws (finiteDomainSupNorm domain) where
  nonnegative := finite_domain_sup_norm_nonnegative domain
  zero_iff_eq := finite_domain_sup_norm_zero_iff_eq domain
  homogeneity := finite_domain_sup_norm_homogeneity domain
  triangle := finite_domain_sup_norm_triangle domain

/-- Finite-domain sup norm candidate using the finite weighted integral target. -/
def finiteDomainSupLikeFieldNormCandidate
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point) :
    SupLikeFieldNormCandidate Point :=
  suppliedSupLikeFieldNormCandidate
    (finiteDomainSupNorm domain)
    (finiteWeightedIntegral domain)

/-- The finite candidate uses the finite-domain sup norm. -/
theorem finite_domain_sup_like_candidate_field_norm_eq
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point) :
    (finiteDomainSupLikeFieldNormCandidate domain).fieldNorm =
      finiteDomainSupNorm domain := by
  rfl

/-- The finite candidate supplies the sup-like norm laws. -/
theorem finite_domain_sup_like_candidate_laws_supplied
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point) :
    (finiteDomainSupLikeFieldNormCandidate domain).sup_like_norm_laws := by
  exact finite_domain_sup_norm_sup_like_laws domain

/-- The finite candidate supplies the stronger-norm separation upgrade. -/
theorem finite_domain_sup_like_candidate_separation_upgrade
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point) :
    (finiteDomainSupLikeFieldNormCandidate domain).separation_upgrade := by
  exact sup_like_candidate_supplies_separation_upgrade
    (finiteDomainSupLikeFieldNormCandidate domain)
    (finite_domain_sup_like_candidate_laws_supplied domain)

/-- The finite candidate supplies zero-distance pairing respect. -/
theorem finite_domain_sup_like_candidate_pairing_compatibility
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point) :
    (finiteDomainSupLikeFieldNormCandidate domain).pairing_compatibility := by
  exact sup_like_candidate_supplies_pairing_compatibility
    (finiteDomainSupLikeFieldNormCandidate domain)
    (finite_domain_sup_like_candidate_laws_supplied domain)

/-- The finite candidate closes its sup-like statement. -/
theorem finite_domain_sup_like_candidate_statement
    {Point : Type}
    [Fintype Point]
    [Nonempty Point]
    (domain : FiniteWeightedBaseDomain Point) :
    (finiteDomainSupLikeFieldNormCandidate
      domain).field_topology_or_norm_statement := by
  exact
    (finiteDomainSupLikeFieldNormCandidate
      domain).statement_from_laws_separation_pairing
        (finite_domain_sup_like_candidate_laws_supplied domain)
        (finite_domain_sup_like_candidate_separation_upgrade domain)
        (finite_domain_sup_like_candidate_pairing_compatibility domain)

/-- Conditional finite-domain evidence for the A1A1A field-topology route. -/
def supLikeFieldNormEvidenceOfFiniteDomainSupNorm
    {ContinuumPoint : Type}
    [Fintype ContinuumPoint]
    [Nonempty ContinuumPoint]
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {analyticStructure : PairingLimitAnalyticStructure scheme}
    (domain : FiniteWeightedBaseDomain ContinuumPoint)
    (statement_supplies_split_field :
      (finiteDomainSupLikeFieldNormCandidate
        domain).field_topology_or_norm_statement ->
        analyticStructure.fieldSpaceTopologyOrNorm) :
    SupLikeFieldNormEvidence scheme analyticStructure where
  candidate := finiteDomainSupLikeFieldNormCandidate domain
  sup_like_norm_laws_supplied :=
    finite_domain_sup_like_candidate_laws_supplied domain
  statement_supplies_split_field := statement_supplies_split_field

/-- Finite-domain sup evidence can fill the A1A1A split field when supplied. -/
theorem finite_domain_sup_norm_evidence_supplies_split_field
    {ContinuumPoint : Type}
    [Fintype ContinuumPoint]
    [Nonempty ContinuumPoint]
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {analyticStructure : PairingLimitAnalyticStructure scheme}
    (domain : FiniteWeightedBaseDomain ContinuumPoint)
    (statement_supplies_split_field :
      (finiteDomainSupLikeFieldNormCandidate
        domain).field_topology_or_norm_statement ->
        analyticStructure.fieldSpaceTopologyOrNorm) :
    analyticStructure.fieldSpaceTopologyOrNorm := by
  exact sup_like_field_norm_evidence_supplies_split_field
    (supLikeFieldNormEvidenceOfFiniteDomainSupNorm
      domain statement_supplies_split_field)

/-- Current repository status for the finite-domain sup norm route. -/
structure FiniteDomainSupNormStatus where
  finite_sup_norm_defined : Prop
  finite_sup_norm_defined_supplied : finite_sup_norm_defined
  finite_sup_like_laws_closed : Prop
  finite_sup_like_laws_closed_supplied : finite_sup_like_laws_closed
  finite_candidate_wired_to_sup_like_route : Prop
  finite_candidate_wired_to_sup_like_route_supplied :
    finite_candidate_wired_to_sup_like_route
  continuum_sup_norm_closed : Prop
  continuum_sup_norm_not_closed : Not continuum_sup_norm_closed
  finite_to_continuum_sup_compatibility_closed : Prop
  finite_to_continuum_sup_compatibility_not_closed :
    Not finite_to_continuum_sup_compatibility_closed
  phase2Authorized : Bool
  retained_blocker_id : String
  parent_sup_like_blocker_id : String
  outcome_id : String

/--
Current status: finite-domain sup laws are discharged, while the continuum
sup-norm construction and compatibility theorem remain retained.
-/
def finiteDomainSupNormStatusV0 : FiniteDomainSupNormStatus where
  finite_sup_norm_defined := True
  finite_sup_norm_defined_supplied := True.intro
  finite_sup_like_laws_closed := True
  finite_sup_like_laws_closed_supplied := True.intro
  finite_candidate_wired_to_sup_like_route := True
  finite_candidate_wired_to_sup_like_route_supplied := True.intro
  continuum_sup_norm_closed := False
  continuum_sup_norm_not_closed := by
    intro h
    exact h
  finite_to_continuum_sup_compatibility_closed := False
  finite_to_continuum_sup_compatibility_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  retained_blocker_id :=
    phase1Blocker003A1A1C3A1A1A1A2A1ContinuumSupNormRetainedId
  parent_sup_like_blocker_id :=
    phase1Blocker003A1A1C3A1A1A1A2A1ParentSupLikeBlockerId
  outcome_id := finiteDomainSupNormOutcomeId

/-- Short local status alias. -/
def finiteDomainSupNormStatus : FiniteDomainSupNormStatus :=
  finiteDomainSupNormStatusV0

/-- The finite-domain sup norm is now defined. -/
theorem finite_domain_sup_norm_defined_v0 :
    finiteDomainSupNormStatus.finite_sup_norm_defined := by
  exact finiteDomainSupNormStatus.finite_sup_norm_defined_supplied

/-- The finite-domain sup-like laws are discharged. -/
theorem finite_domain_sup_like_laws_closed_v0 :
    finiteDomainSupNormStatus.finite_sup_like_laws_closed := by
  exact finiteDomainSupNormStatus.finite_sup_like_laws_closed_supplied

/-- The finite-domain candidate is wired into the sup-like route. -/
theorem finite_domain_sup_norm_candidate_wired_v0 :
    finiteDomainSupNormStatus.finite_candidate_wired_to_sup_like_route := by
  exact finiteDomainSupNormStatus.finite_candidate_wired_to_sup_like_route_supplied

/-- The continuum sup norm remains retained. -/
theorem finite_domain_sup_norm_continuum_sup_not_closed_v0 :
    Not finiteDomainSupNormStatus.continuum_sup_norm_closed := by
  exact finiteDomainSupNormStatus.continuum_sup_norm_not_closed

/-- The finite-to-continuum sup compatibility theorem remains retained. -/
theorem finite_domain_sup_norm_finite_to_continuum_not_closed_v0 :
    Not finiteDomainSupNormStatus.finite_to_continuum_sup_compatibility_closed := by
  exact finiteDomainSupNormStatus.finite_to_continuum_sup_compatibility_not_closed

/-- The slice exposes the expected retained continuum sup blocker. -/
theorem finite_domain_sup_norm_retained_id_v0 :
    finiteDomainSupNormStatus.retained_blocker_id =
      phase1Blocker003A1A1C3A1A1A1A2A1ContinuumSupNormRetainedId := by
  rfl

/-- The slice remains below the sup-like candidate blocker. -/
theorem finite_domain_sup_norm_parent_id_v0 :
    finiteDomainSupNormStatus.parent_sup_like_blocker_id =
      phase1Blocker003A1A1C3A1A1A1A2ASupLikeFieldNormRetainedId := by
  rfl

/-- The slice exposes the expected outcome id. -/
theorem finite_domain_sup_norm_outcome_id_v0 :
    finiteDomainSupNormStatus.outcome_id =
      finiteDomainSupNormOutcomeId := by
  rfl

/--
003A1A1C3A1A1A1A2A1 readout. Finite-domain sup norm laws are discharged,
but continuum sup topology and finite-to-continuum compatibility are retained.
-/
def phase1Blocker003A1A1C3A1A1A1A2A1FiniteDomainSupNormV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Short alias for the finite-domain sup norm readout. -/
def finiteDomainSupNormReadoutV0 : Phase1Blocker003Split :=
  phase1Blocker003A1A1C3A1A1A1A2A1FiniteDomainSupNormV0

/-- Phase 2 remains unauthorized after this finite-domain sup norm slice. -/
theorem phase1_blocker003a1a1c3a1a1a1a2a1_finite_sup_norm_v0_phase2_not_authorized :
    Not finiteDomainSupNormReadoutV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumPairingLimitFiniteDomainSupNorm
end QFT
end ToeFormal
