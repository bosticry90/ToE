/-
ToeFormal/Variational/FirstVariationDeclaredRep.lean

First-variation pairing contract on the Rep32 quotient (structural-only).

Scope:
- Uses the concrete Rep32 sampling lane.
- Derives nondegeneracy on Field2DRep32 using delta-coverage for Rep32.
- Does not assert injectivity on Field2D.
-/

import Mathlib
import ToeFormal.Variational.FieldRepresentationRep32
import ToeFormal.Variational.PairingConcreteGrid
import ToeFormal.Variational.PairingContract

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Nondegeneracy of the pairing on the Rep32 quotient. -/
theorem pairingRep32_nondegenerate :
    ∀ x y : Field2DRep32,
      (∀ v : Field2DRep32, pairingRep32 x v = pairingRep32 y v) -> x = y := by
  classical
  intro x y h
  revert h
  refine Quot.induction_on₂ x y ?_
  intro x y h
  apply Quot.sound
  -- Show Rep32 x = Rep32 y using delta probe coverage.
  funext i j
  apply Complex.ext
  · obtain ⟨ψ, hψ⟩ := Rep32_hits_delta_one (i := i) (j := j)
    have hv := h (Quot.mk _ ψ)
    have hv' :
        gridPairing (Rep32 x) (delta i j 1) =
          gridPairing (Rep32 y) (delta i j 1) := by
      simpa [pairingRep32, RepQ32, hψ] using hv
    have hx := (gridPairing_delta (x := Rep32 x) (i := i) (j := j) (c := (1 : ℂ)))
    have hy := (gridPairing_delta (x := Rep32 y) (i := i) (j := j) (c := (1 : ℂ)))
    calc
      (Rep32 x i j).re
          = (Rep32 x i j).re * (1 : ℂ).re + (Rep32 x i j).im * (1 : ℂ).im := by
            simp
      _ = gridPairing (Rep32 x) (delta i j 1) := by
            simpa using hx.symm
      _ = gridPairing (Rep32 y) (delta i j 1) := by
            exact hv'
      _ = (Rep32 y i j).re * (1 : ℂ).re + (Rep32 y i j).im * (1 : ℂ).im := by
            exact hy
      _ = (Rep32 y i j).re := by
            simp
  · obtain ⟨ψ, hψ⟩ := Rep32_hits_delta_I (i := i) (j := j)
    have hv := h (Quot.mk _ ψ)
    have hv' :
        gridPairing (Rep32 x) (delta i j Complex.I) =
          gridPairing (Rep32 y) (delta i j Complex.I) := by
      simpa [pairingRep32, RepQ32, hψ] using hv
    have hx := (gridPairing_delta (x := Rep32 x) (i := i) (j := j) (c := Complex.I))
    have hy := (gridPairing_delta (x := Rep32 y) (i := i) (j := j) (c := Complex.I))
    calc
      (Rep32 x i j).im
          = (Rep32 x i j).re * (Complex.I).re + (Rep32 x i j).im * (Complex.I).im := by
            simp
      _ = gridPairing (Rep32 x) (delta i j Complex.I) := by
            simpa using hx.symm
      _ = gridPairing (Rep32 y) (delta i j Complex.I) := by
            exact hv'
      _ = (Rep32 y i j).re * (Complex.I).re + (Rep32 y i j).im * (Complex.I).im := by
            exact hy
      _ = (Rep32 y i j).im := by
            simp

/-- Pairing contract on the representation quotient. -/
def pairingContractRep : PairingContract Field2DRep32 :=
  { pairing := pairingRep32
    nondegenerate_second := pairingRep32_nondegenerate }

end

end Variational
end ToeFormal
