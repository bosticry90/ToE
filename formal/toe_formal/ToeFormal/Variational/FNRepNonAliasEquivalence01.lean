/-
ToeFormal/Variational/FNRepNonAliasEquivalence01.lean

Non-alias cross-representation equivalence target (skeleton).

Scope:
- Declares explicit transport maps between Rep32 and a non-alias quotient lane.
- States a comparator-surface invariance target under that transport.
- Structural-only; the default non-alias witness is concrete, while the
  sample Rep32 witness remains recorded as an axiom/placeholding row.
- No analytic claims; no physics truth-claim upgrade.
-/

import Mathlib
import ToeFormal.Variational.FieldRepresentation
import ToeFormal.Variational.FieldRepresentationRep32

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-
Tagged non-alias wrapper.
This is structurally distinct from the Rep32 lane while remaining computable.
-/
structure Field2DNonAlias where
  val : Field2DRep32
  tag : Bool

/-- Canonical zero field used to build the default Rep32 quotient witness. -/
def defaultRep32 : Field2DRep32 :=
  Quot.mk RepSetoid32 (fun _ _ _ => 0)

/-- Transport from the Rep32 quotient lane to the non-alias tagged lane. -/
def rep32ToNonAlias (x : Field2DRep32) : Field2DNonAlias :=
  ⟨x, false⟩

/-- Transport default element for negative-control diagnostics. -/
def defaultNonAlias : Field2DNonAlias :=
  rep32ToNonAlias defaultRep32

/-- The default non-alias witness is the concrete zero-field quotient with tag `false`. -/
theorem defaultNonAlias_eq_zero_rep32_false :
    defaultNonAlias = ⟨defaultRep32, false⟩ := by
  rfl

/-- The default non-alias witness is not tag-sensitive. -/
theorem defaultNonAlias_tag_false :
    defaultNonAlias.tag = false := by
  rfl

/-- Transport from the non-alias tagged lane to the Rep32 quotient lane. -/
def nonAliasToRep32 (x : Field2DNonAlias) : Field2DRep32 :=
  x.val

/-
Scope limits (explicit):
- Transport maps are explicit wrappers/projections.
- The tagged lane is structural-only; it does not encode analytic content.
- Comparator surfaces are defined (no axioms), but are currently minimal.
- Invariance lemma below is definitional for the minimal surface only.
- No analytic/physics claims are made.
-/

/-- Comparator-relevant surface on the Rep32 lane (abstract placeholder). -/
def comparatorSurfaceRep32 (_ : Field2DRep32) : ℝ :=
  0

/-- Comparator-relevant surface on the non-alias lane (abstract placeholder). -/
def comparatorSurfaceNonAlias (x : Field2DNonAlias) : ℝ :=
  comparatorSurfaceRep32 x.val

/-- Target invariance claim: transport preserves the comparator surface. -/
theorem comparator_surface_transport_invariant (x : Field2DRep32) :
    comparatorSurfaceNonAlias (rep32ToNonAlias x) = comparatorSurfaceRep32 x := by
  rfl

/-- Round-trip is definitional on Rep32. -/
theorem rep32_nonalias_roundtrip_left (x : Field2DRep32) :
    nonAliasToRep32 (rep32ToNonAlias x) = x := by
  rfl

/-- Non-alias equivalence target (structural placeholder). -/
theorem rep32_nonalias_equivalence_target (x : Field2DRep32) :
    comparatorSurfaceNonAlias (rep32ToNonAlias x) = comparatorSurfaceRep32 x := by
  exact comparator_surface_transport_invariant x

/-
Negative control (v1): an intentionally tag-sensitive diagnostic.
Transport from Rep32 uses the default `false` tag, so that restricted transport
agrees with the Rep32 diagnostic; the tag-sensitive lane below still blocks any
claim that all non-alias diagnostics factor through `.val`.
-/

def diagnosticRep32 (_ : Field2DRep32) : ℝ :=
  0

def diagnosticNonAlias (x : Field2DNonAlias) : ℝ :=
  if x.tag then 1 else 0

theorem diagnostic_transport_default_tag_agrees (x : Field2DRep32) :
    diagnosticNonAlias (rep32ToNonAlias x) = diagnosticRep32 x := by
  simp [diagnosticRep32, diagnosticNonAlias, rep32ToNonAlias]

/-
Minimal concrete constructor (placeholder) for the tagged lane.
This allows nontrivial construction without relying on constant transport.
-/
axiom sampleRep32 : Field2DRep32

def nonAliasSample : Field2DNonAlias :=
  rep32ToNonAlias sampleRep32

theorem negative_control_tag_sensitive (x : Field2DRep32) :
    diagnosticNonAlias ⟨x, true⟩ ≠ diagnosticNonAlias ⟨x, false⟩ := by
  simp [diagnosticNonAlias]

/-
Policy anchor: a channel is cross-rep eligible iff it factors through `.val`.
-/

def eligibleForCrossRep {X : Type} (f : Field2DNonAlias -> X) : Prop :=
  ∃ g : Field2DRep32 -> X, ∀ x : Field2DNonAlias, f x = g x.val

theorem comparatorSurfaceNonAlias_eligible :
    eligibleForCrossRep comparatorSurfaceNonAlias := by
  refine ⟨comparatorSurfaceRep32, ?_⟩
  intro x
  rfl

theorem diagnosticNonAlias_not_eligible :
    ¬ eligibleForCrossRep diagnosticNonAlias := by
  intro h
  rcases h with ⟨g, hg⟩
  have h_true := hg ⟨sampleRep32, true⟩
  have h_false := hg ⟨sampleRep32, false⟩
  have h_eq : diagnosticNonAlias ⟨sampleRep32, true⟩ =
      diagnosticNonAlias ⟨sampleRep32, false⟩ := by
    calc
      diagnosticNonAlias ⟨sampleRep32, true⟩ = g sampleRep32 := h_true
      _ = diagnosticNonAlias ⟨sampleRep32, false⟩ := by
        symm
        exact h_false
  exact (negative_control_tag_sensitive sampleRep32) h_eq

end

end Variational
end ToeFormal
