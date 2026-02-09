/-
ToeFormal/Variational/FieldRepresentationSample.lean

Restricted sample slice with a concrete representation map (structural-only).

Scope:
- Defines a small sample type `Field2DSample` backed by a pinned grid.
- Provides an explicit embedding into Field2D via point-sampling support.
- Defines `RepSample` by evaluation on the sample grid and proves delta coverage.
- Adds delta-probe compatibility axioms for the global `Rep` on the sample slice.
- Does not replace the main `Rep` axiom on Field2D.
-/

import Mathlib
import ToeFormal.Variational.FieldRepresentation
import ToeFormal.Variational.PairingConcreteGrid

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false
open BigOperators

/-- Sample x-coordinates for the pinned grid. -/
def sampleX (i : Fin repNx) : ℝ := (i.val : ℝ)

/-- Sample y-coordinates for the pinned grid. -/
def sampleY (j : Fin repNy) : ℝ := (j.val : ℝ)

/-- Sample time coordinate for the pinned grid. -/
def sampleT : ℝ := 0

theorem sampleX_injective : Function.Injective sampleX := by
  intro i j h
  apply Fin.ext
  exact Nat.cast_inj.mp (by simpa [sampleX] using h)

theorem sampleY_injective : Function.Injective sampleY := by
  intro i j h
  apply Fin.ext
  exact Nat.cast_inj.mp (by simpa [sampleY] using h)

/-- Sample slice backed by the pinned grid. -/
structure Field2DSample where
  grid : RepGrid

/-- Embedding of the sample slice into Field2D via point support. -/
def toField2D (s : Field2DSample) : Field2D :=
  fun x y t =>
    (Finset.univ : Finset (Fin repNx × Fin repNy)).sum (fun ij =>
      if (x = sampleX ij.1 ∧ y = sampleY ij.2 ∧ t = sampleT) then
        s.grid ij.1 ij.2
      else 0)

/-- Representation map on the sample slice (evaluation on the sample grid). -/
def RepSample (s : Field2DSample) : RepGrid :=
  fun i j => toField2D s (sampleX i) (sampleY j) sampleT

/-- Compatibility: global `Rep` agrees with `RepSample` on delta probes (value `1`). -/
axiom Rep_on_samples_delta_one :
  ∀ (i : Fin repNx) (j : Fin repNy),
    Rep (toField2D ⟨delta i j 1⟩) = RepSample ⟨delta i j 1⟩

/-- Compatibility: global `Rep` agrees with `RepSample` on delta probes (value `I`). -/
axiom Rep_on_samples_delta_I :
  ∀ (i : Fin repNx) (j : Fin repNy),
    Rep (toField2D ⟨delta i j Complex.I⟩) = RepSample ⟨delta i j Complex.I⟩

theorem RepSample_eq_grid (s : Field2DSample) : RepSample s = s.grid := by
  classical
  funext i j
  unfold RepSample toField2D
  refine (Finset.sum_eq_single (i, j) ?_ ?_).trans ?_
  · intro ij _ hneq
    have hcond' : ¬ (sampleX i = sampleX ij.1 ∧ sampleY j = sampleY ij.2) := by
      intro hcond'
      have hx : ij.1 = i :=
        (sampleX_injective (by simpa [sampleX] using hcond'.1)).symm
      have hy : ij.2 = j :=
        (sampleY_injective (by simpa [sampleY] using hcond'.2)).symm
      apply hneq
      cases hx
      cases hy
      rfl
    simp [sampleT, hcond']
  · intro h
    exact (h (by simp)).elim
  · simp [sampleT]

/-- Delta coverage on the sample slice (value `1`). -/
theorem RepSample_hits_delta_one :
    ∀ (i : Fin repNx) (j : Fin repNy),
      ∃ s : Field2DSample, RepSample s = delta i j 1 := by
  intro i j
  refine ⟨⟨delta i j 1⟩, ?_⟩
  simp [RepSample_eq_grid]

/-- Delta coverage on the sample slice (value `I`). -/
theorem RepSample_hits_delta_I :
    ∀ (i : Fin repNx) (j : Fin repNy),
      ∃ s : Field2DSample, RepSample s = delta i j Complex.I := by
  intro i j
  refine ⟨⟨delta i j Complex.I⟩, ?_⟩
  simp [RepSample_eq_grid]

/-- Delta coverage for the global `Rep` (value `1`) witnessed by the sample slice. -/
theorem Rep_hits_delta_one :
    ∀ (i : Fin repNx) (j : Fin repNy),
      ∃ ψ : Field2D, Rep ψ = delta i j 1 := by
  intro i j
  refine ⟨toField2D ⟨delta i j 1⟩, ?_⟩
  calc
    Rep (toField2D ⟨delta i j 1⟩)
        = RepSample ⟨delta i j 1⟩ := Rep_on_samples_delta_one i j
    _ = delta i j 1 := by
        simp [RepSample_eq_grid]

/-- Delta coverage for the global `Rep` (value `I`) witnessed by the sample slice. -/
theorem Rep_hits_delta_I :
    ∀ (i : Fin repNx) (j : Fin repNy),
      ∃ ψ : Field2D, Rep ψ = delta i j Complex.I := by
  intro i j
  refine ⟨toField2D ⟨delta i j Complex.I⟩, ?_⟩
  calc
    Rep (toField2D ⟨delta i j Complex.I⟩)
        = RepSample ⟨delta i j Complex.I⟩ := Rep_on_samples_delta_I i j
    _ = delta i j Complex.I := by
        simp [RepSample_eq_grid]

end

end Variational
end ToeFormal
