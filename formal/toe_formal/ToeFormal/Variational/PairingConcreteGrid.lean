/-
ToeFormal/Variational/PairingConcreteGrid.lean

Concrete pairing on a finite grid field with a nondegeneracy proof.

Scope:
- Defines an ℝ-valued pairing on FieldGrid via coordinate-wise real/imag parts.
- Proves nondegeneracy by coordinate delta tests.
- Provides a PairingContract instance.
-/

import Mathlib
import ToeFormal.Variational.DiscreteField
import ToeFormal.Variational.PairingContract

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false
open BigOperators

/-- Delta field: value `c` at (i,j), zero elsewhere. -/
def delta {nx ny : Nat} (i : Fin nx) (j : Fin ny) (c : ℂ) : FieldGrid nx ny :=
  fun i' j' => if (i' = i ∧ j' = j) then c else 0

theorem delta_eq_zero_of_ne {nx ny : Nat} {i : Fin nx} {j : Fin ny} {c : ℂ}
    {ij : Fin nx × Fin ny} (h : ij ≠ (i, j)) :
    delta i j c ij.1 ij.2 = 0 := by
  classical
  have h' : ¬ (ij.1 = i ∧ ij.2 = j) := by
    intro hEq
    apply h
    cases hEq with
    | intro hi hj =>
      cases hi
      cases hj
      rfl
  simp [delta, h']

/-- ℝ-valued grid pairing (coordinate-wise real/imag inner product). -/
def gridPairing {nx ny : Nat} (x v : FieldGrid nx ny) : ℝ :=
  (Finset.univ : Finset (Fin nx × Fin ny)).sum (fun ij =>
    (x ij.1 ij.2).re * (v ij.1 ij.2).re +
    (x ij.1 ij.2).im * (v ij.1 ij.2).im)

theorem gridPairing_delta {nx ny : Nat} (x : FieldGrid nx ny)
    (i : Fin nx) (j : Fin ny) (c : ℂ) :
    gridPairing x (delta i j c) =
      (x i j).re * c.re + (x i j).im * c.im := by
  classical
  unfold gridPairing
  refine (Finset.sum_eq_single (i, j) ?_ ?_).trans ?_
  · intro ij _ hneq
    have hdelta : delta i j c ij.1 ij.2 = 0 :=
      delta_eq_zero_of_ne (i := i) (j := j) (c := c) hneq
    simp [hdelta]
  · intro h
    exact (h (by simp)).elim
  · simp [delta]

theorem gridPairing_nondegenerate {nx ny : Nat} :
    ∀ x y : FieldGrid nx ny,
      (∀ v : FieldGrid nx ny, gridPairing x v = gridPairing y v) -> x = y := by
  intro x y h
  funext i j
  apply Complex.ext
  · have h1 := h (delta i j 1)
    simpa [gridPairing_delta, Complex.one_re, Complex.one_im] using h1
  · have h2 := h (delta i j Complex.I)
    simpa [gridPairing_delta, Complex.I_re, Complex.I_im] using h2

/-- PairingContract instance for the grid pairing. -/
def gridPairingContract (nx ny : Nat) : PairingContract (FieldGrid nx ny) :=
  { pairing := gridPairing
    nondegenerate_second := by
      intro x y h
      exact gridPairing_nondegenerate (nx := nx) (ny := ny) x y h }

end

end Variational
end ToeFormal
