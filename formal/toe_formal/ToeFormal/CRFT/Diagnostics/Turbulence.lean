import Mathlib

namespace ToeFormal.CRFT.Diagnostics

noncomputable section
set_option autoImplicit false

open scoped BigOperators

-- LOCK_TURB_C12_C13_TURBULENCE_DIAGNOSTICS.md
-- Files covered (authoritative in numerical layer):
--   crft/diagnostics/turbulence.py
--   crft/tests/crft_turb_c12_c13.py
--
-- This Lean file locks:
--   • 1D spectrum computation shape: rFFT k-array + E_k := |F|^2 / N^2 (NO dx scaling, NO factor 2)
--   • band partition masks (k_low, k_mid)
--   • coherent-structure detector: thresholded contiguous segments on 1D grid
--     (NO explicit periodic wrap-around merging)

--------------------------------------------------------------------------------
-- 1D Spectrum (structural lock: rFFT primitives are opaque in Lean)
--------------------------------------------------------------------------------

/-- Spectrum container (non-negative rFFT k and corresponding E_k). -/
structure Spectrum1D (N : Nat) where
  k : Fin (N / 2 + 1) → ℝ
  Ek : Fin (N / 2 + 1) → ℝ

-- Opaque FFT helpers (stand-ins for numpy.rfft and numpy.fft.rfftfreq).
opaque rfft {N : Nat} : (Fin N → ℝ) → (Fin (N / 2 + 1) → ℂ)
opaque rfftfreq (N : Nat) (d : ℝ) : Fin (N / 2 + 1) → ℝ

/-- Locked spectrum computation:
  k = 2π * rfftfreq(N, d=dx),  F = rfft(field),  E_k = |F|^2 / N^2. -/
def computeSpectrum1D {N : Nat} (_hN : 0 < N) (field : Fin N → ℝ) (L : ℝ) : Spectrum1D N :=
  let dx : ℝ := L / (N : ℝ)
  let kfun : Fin (N / 2 + 1) → ℝ := fun i => (2 * Real.pi) * (rfftfreq N dx i)
  let F : Fin (N / 2 + 1) → ℂ := rfft (N := N) field
  let Ekfun : Fin (N / 2 + 1) → ℝ := fun i => Complex.normSq (F i) / ((N : ℝ) ^ 2)
  ⟨kfun, Ekfun⟩

theorem computeSpectrum1D_Ek_normalization
    {N : Nat} (hN : 0 < N) (field : Fin N → ℝ) (L : ℝ) (i : Fin (N / 2 + 1)) :
    (computeSpectrum1D (N := N) hN field L).Ek i
      = Complex.normSq (rfft (N := N) field i) / ((N : ℝ) ^ 2) := by
  rfl

--------------------------------------------------------------------------------
-- Band partition (definitional lock; Bool masks via `decide`)
--------------------------------------------------------------------------------

/-- Band-energy sums (low/mid/high) plus total over stored rFFT modes. -/
structure SpectralBands1D where
  Elow : ℝ
  Emid : ℝ
  Ehigh : ℝ
  Etot : ℝ

/-- Locked partition masks:
  Low: 0 <= k < k_low
  Mid: k_low <= k < k_mid
  High: k >= k_mid
  with energies as sums of E_k over masks. -/
def partitionSpectrum1D {N : Nat} (spec : Spectrum1D N) (k_low k_mid : ℝ) : SpectralBands1D := by
  classical
    let idx : Finset (Fin (N / 2 + 1)) := Finset.univ
  let Etot : ℝ := Finset.sum idx (fun i => spec.Ek i)
  let lowSet : Finset (Fin (N / 2 + 1)) :=
    idx.filter (fun i => decide (0 ≤ spec.k i ∧ spec.k i < k_low))
  let midSet : Finset (Fin (N / 2 + 1)) :=
    idx.filter (fun i => decide (k_low ≤ spec.k i ∧ spec.k i < k_mid))
  let highSet : Finset (Fin (N / 2 + 1)) :=
    idx.filter (fun i => decide (k_mid ≤ spec.k i))
  let Elow : ℝ := Finset.sum lowSet (fun i => spec.Ek i)
  let Emid : ℝ := Finset.sum midSet (fun i => spec.Ek i)
  let Ehigh : ℝ := Finset.sum highSet (fun i => spec.Ek i)
  exact ⟨Elow, Emid, Ehigh, Etot⟩

theorem partitionSpectrum1D_Etot_def
    {N : Nat} (spec : Spectrum1D N) (k_low k_mid : ℝ) :
    (partitionSpectrum1D (N := N) spec k_low k_mid).Etot
      = Finset.sum (Finset.univ : Finset (Fin (N / 2 + 1))) (fun i => spec.Ek i) := by
  rfl

--------------------------------------------------------------------------------
-- Coherent-structure detection (fully implemented lock)
--------------------------------------------------------------------------------

/-- Coherent structure record (center index, center x, width). -/
structure CoherentStructure1D where
  centerIndex : ℝ
  centerX : ℝ
  width : ℝ

/-- Internal: compute max of a non-empty list. -/
def listMax : List ℝ → Option ℝ
| [] => none
| a :: as => some (as.foldl max a)

/-- Internal: convert a list to a threshold mask (field >= threshold). -/
def thresholdMask (field : List ℝ) (threshold : ℝ) : List Bool :=
  field.map (fun v => decide (v ≥ threshold))

/-- Internal: contiguous True segments on a Bool list, returned as (start,end) inclusive. -/
def trueSegments : List Bool → List (Nat × Nat) :=
  let rec go : List Bool → Nat → Option Nat → List (Nat × Nat) → List (Nat × Nat)
    | [],      _, none,   acc => acc.reverse
    | [],      i, some s, acc => ((s, i - 1) :: acc).reverse
    | b :: bs, i, none,   acc =>
        if b then go bs (i + 1) (some i) acc else go bs (i + 1) none acc
    | b :: bs, i, some s, acc =>
        if b then go bs (i + 1) (some s) acc else go bs (i + 1) none ((s, i - 1) :: acc)
  fun bs => go bs 0 none []

/-- Locked coherent-structure detector:
  - If N == 0 → []
  - max_val := max(field); if max_val <= 0 → []
  - threshold := threshold_fraction * max_val
  - mask := field >= threshold
  - contiguous True segments (NO periodic wrap merge)
  - center_index := 0.5*(start+end), width := (end-start+1)*dx, center_x := center_index*dx -/
def detectCoherentStructures1D
    (field : List ℝ) (dx : ℝ) (threshold_fraction : ℝ := 0.5) :
    List CoherentStructure1D :=
  match listMax field with
  | none => []
  | some max_val =>
      if max_val ≤ 0 then
        []
      else
        let threshold := threshold_fraction * max_val
        let segs := trueSegments (thresholdMask field threshold)
        segs.map (fun se =>
          let s : Nat := se.1
          let e : Nat := se.2
          let centerIndex : ℝ := (1 / 2 : ℝ) * ((s : ℝ) + (e : ℝ))
          let width : ℝ := ((e - s + 1 : Nat) : ℝ) * dx
          let centerX : ℝ := centerIndex * dx
          ⟨centerIndex, centerX, width⟩)

end
end ToeFormal.CRFT.Diagnostics
