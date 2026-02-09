import Mathlib
import ToeFormal.CPNLSE2D.PlaneWaveOperatorDefs
-- If Field2D is defined elsewhere, import that instead of PlaneWaveOperatorDefs.

namespace ToeFormal
namespace Constraints

open ToeFormal.CPNLSE2D

noncomputable section

/--
Abstract “linearization at ψ = 0” interface for perturbations.

This is intentionally non-analytic and non-physical: it is only a structural hook
that assigns to each perturbation term `P : Field2D → Field2D` a ℂ-linear operator
`Field2D →ₗ[ℂ] Field2D` interpreted as its “linear part at 0”.
-/
structure LinearizationAt0 (Field : Type) [AddCommGroup Field] [Module ℂ Field] where
  linPartAt0 : (Field → Field) → (Field →ₗ[ℂ] Field)

/-- The extracted linear part at 0, as a ℂ-linear operator. -/
def LinearPartAt0 {Field : Type} [AddCommGroup Field] [Module ℂ Field]
  (L : LinearizationAt0 Field) (P : Field → Field) : (Field →ₗ[ℂ] Field) :=
  L.linPartAt0 P

/-- Predicate: the perturbation has no linear part at 0 (purely structural). -/
def NoLinearPartAt0 {Field : Type} [AddCommGroup Field] [Module ℂ Field]
  (L : LinearizationAt0 Field) (P : Field → Field) : Prop :=
  LinearPartAt0 L P = 0

/-- Specialization to the project’s Field2D. -/
abbrev LinearizationAt0_Field2D : Type :=
  LinearizationAt0 Field2D

/-- Specialization: no-linear-part predicate for Field2D perturbations. -/
abbrev NoLinearPartAt0_Field2D (L : LinearizationAt0_Field2D) (P : Field2D → Field2D) : Prop :=
  NoLinearPartAt0 (Field := Field2D) L P

end
end Constraints
end ToeFormal
