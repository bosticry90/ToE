import ToeFormal.Constraints.AD01_AdmissibleOp
import ToeFormal.Constraints.AD01_Breakage
import ToeFormal.Constraints.AD01_Canonicals
import ToeFormal.OperatorCore.Op2DMeta
import ToeFormal.Constraints.SYM01_PhaseInvariant
import ToeFormal.Constraints.CAUS01_CausalityGate
import ToeFormal.OperatorCore.OperatorSignature

namespace ToeFormal
namespace Constraints

open ToeFormal.OperatorCore
open ToeFormal.Constraints
open ToeFormal.Constraints.CAUS01
open ToeFormal.Constraints.SYM01
open ToeFormal.CPNLSE2D
open ToeFormal.Constraints.AD01

/-
Canonical gate instances on the repo's concrete operator type `Op2D`.

These are structural adapters:
- SYM-01 is wired via `SYM01.PhaseInvariant` applied to the underlying map `O.Op`.
- CAUS-01 is wired via `CAUS01.CAUS01_Admissible` applied to `O.Op`, plus a non-circular
  operator-level time-order sanity check (`OperatorCore.TimeOrderSaneOp`).

The canonical choices live in `AD01_Canonicals` (A0, G0) along with a canonical
`OpTimeOrder` tag instance.
-/

instance : SymmGate Op2D where
  symmOk O := SYM01.PhaseInvariant A0 O.Op

instance [OperatorCore.OpTimeOrder Field2D] : CausGate Op2D where
  causOk O :=
    CAUS01.CAUS01_Admissible (F := Field2D) G0 O.Op ∧
    OperatorCore.TimeOrderSaneOp (F := Field2D) G0.form O

/-
Corollary:
If both O and O+E are AD01-admissible, then E is probe-invisible on plane waves.

This is the “wiring convenience theorem” you asked for.
-/
theorem ad01_admissible_implies_breakage_onPlaneWaves
  (O E : Op2D)
  (hO : AdmissibleOp Op2D DispersionCompatible O)
  (hOE : AdmissibleOp Op2D DispersionCompatible (O + E))
  :
  ∀ (A : ℂ) (kx ky : ℝ), E.Op (planeWave A kx ky) = 0 := by
  have hO_dc : DispersionCompatible O :=
    admissibleOp_dispersion
      (α := Op2D)
      (DispersionCompatible := DispersionCompatible)
      (O := O)
      hO
  have hOE_dc : DispersionCompatible (O + E) :=
    admissibleOp_dispersion
      (α := Op2D)
      (DispersionCompatible := DispersionCompatible)
      (O := (O + E))
      hOE
  -- Replace the theorem name below with the exact one you proved in AD01_Breakage.lean
  -- (this is the only potential renaming needed).
  simpa using
    ToeFormal.Constraints.AD01.admissibleOp_breakage_onPlaneWaves (O := O) (E := E) hO_dc hOE_dc

end Constraints
end ToeFormal
