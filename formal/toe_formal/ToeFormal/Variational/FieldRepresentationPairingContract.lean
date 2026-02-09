/-
ToeFormal/Variational/FieldRepresentationPairingContract.lean

Pairing contract on the Field2D representation quotient (structural-only).

Scope:
- Uses the explicit representation quotient policy from FieldRepresentation.
- Derives nondegeneracy on the quotient via delta coverage of `Rep`.
- Does not claim injectivity on Field2D.
- Provides a PairingContract instance for Field2DRep.
- Relies on the existing Rep delta-coverage axioms from FieldRepresentationSample.
-/

import Mathlib
import ToeFormal.Variational.FieldRepresentationSample
import ToeFormal.Variational.PairingConcreteGrid
import ToeFormal.Variational.PairingContract

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Nondegeneracy of the pairing on the Field2D representation quotient. -/
theorem pairingRep_nondegenerate :
    ∀ x y : Field2DRep,
      (∀ v : Field2DRep, pairingRep x v = pairingRep y v) -> x = y := by
  classical
  intro x y h
  revert h
  refine Quot.induction_on₂ x y ?_
  intro x y h
  apply Quot.sound
  funext i j
  apply Complex.ext
  · obtain ⟨ψ, hψ⟩ := Rep_hits_delta_one (i := i) (j := j)
    have hv := h (Quot.mk _ ψ)
    have hv' :
        gridPairing (Rep x) (delta i j 1) =
          gridPairing (Rep y) (delta i j 1) := by
      simpa [pairingRep, RepQ, hψ] using hv
    have hx := (gridPairing_delta (x := Rep x) (i := i) (j := j) (c := (1 : ℂ)))
    have hy := (gridPairing_delta (x := Rep y) (i := i) (j := j) (c := (1 : ℂ)))
    calc
      (Rep x i j).re
          = (Rep x i j).re * (1 : ℂ).re + (Rep x i j).im * (1 : ℂ).im := by
            simp
      _ = gridPairing (Rep x) (delta i j 1) := by
            simpa using hx.symm
      _ = gridPairing (Rep y) (delta i j 1) := by
            exact hv'
      _ = (Rep y i j).re * (1 : ℂ).re + (Rep y i j).im * (1 : ℂ).im := by
            exact hy
      _ = (Rep y i j).re := by
            simp
  · obtain ⟨ψ, hψ⟩ := Rep_hits_delta_I (i := i) (j := j)
    have hv := h (Quot.mk _ ψ)
    have hv' :
        gridPairing (Rep x) (delta i j Complex.I) =
          gridPairing (Rep y) (delta i j Complex.I) := by
      simpa [pairingRep, RepQ, hψ] using hv
    have hx := (gridPairing_delta (x := Rep x) (i := i) (j := j) (c := Complex.I))
    have hy := (gridPairing_delta (x := Rep y) (i := i) (j := j) (c := Complex.I))
    calc
      (Rep x i j).im
          = (Rep x i j).re * (Complex.I).re + (Rep x i j).im * (Complex.I).im := by
            simp
      _ = gridPairing (Rep x) (delta i j Complex.I) := by
            simpa using hx.symm
      _ = gridPairing (Rep y) (delta i j Complex.I) := by
            exact hv'
      _ = (Rep y i j).re * (Complex.I).re + (Rep y i j).im * (Complex.I).im := by
            exact hy
      _ = (Rep y i j).im := by
            simp

/-- Pairing contract on the Field2D representation quotient. -/
def pairingContractFieldRep : PairingContract Field2DRep :=
  { pairing := pairingRep
    nondegenerate_second := pairingRep_nondegenerate }

end

end Variational
end ToeFormal
