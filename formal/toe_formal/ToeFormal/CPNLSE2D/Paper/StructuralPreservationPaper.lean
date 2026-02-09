/-
StructuralPreservationPaper.lean

This file is a “paper module” that is intended to compile inside your existing ToE / ToeFormal
Lean project. It does NOT introduce any new mathematical claims beyond what is already present
in the referenced Lean modules.

It exists to:
- preserve the publication-style narrative (as comments),
- import the authoritative Lean sources,
- provide a single compilation target you can `lake build`,
- and offer explicit name-level traceability via `#check`.

Source narrative: “Structural Preservation of Plane-Wave Dispersion in the 2D Linear Schrödinger Limit”
(Generated as a Markdown paper, then re-embedded here as Lean comments.)
-/

import Mathlib

/-
IMPORTANT: These imports assume the same module paths you previously provided:

- ToeFormal/CPNLSE2D/Dispersion.lean
- ToeFormal/Derivation/DR01_Redundant.lean
- ToeFormal/CPNLSE2D/PlaneWaveOperators.lean
- ToeFormal/CPNLSE2D/PhaseB/DispersionPreservation.lean

If your local paths differ, adjust the import lines accordingly.
-/
import ToeFormal.CPNLSE2D.Dispersion
import ToeFormal.Derivation.DR01_Redundant
import ToeFormal.CPNLSE2D.PlaneWaveOperators
import ToeFormal.CPNLSE2D.PhaseB.DispersionPreservation

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ToeFormal
namespace CPNLSE2D

/-!
# Structural Preservation of Plane-Wave Dispersion in the 2D Linear Schrödinger Limit

## Abstract
This module packages a purely structural formalization of plane-wave dispersion preservation in the
two-dimensional linear Schrödinger limit. It imports the authoritative Lean sources that define the
dispersion relation and plane-wave template, establish redundant algebraic equivalences, prove
operator-level reduction results under explicitly stated axioms, and show that admissible
perturbations (probe-relative on the plane-wave family) preserve the reduced dispersion form.

## 1. Scope and Epistemic Status
- Structural-only (Lean-verified where stated).
- Linear Schrödinger limit only.
- Plane-wave probe family only.
- Conditional on stated axioms; no analytic PDE development.
- No physical interpretation; no geometry/metric/coherence; no universality or ToE claims.

## 2. Formal Setting and Definitions
### 2.1 Field and Plane-Wave Template
- `Field2D` and `planeWave` are imported from `ToeFormal.CPNLSE2D.Dispersion`.

### 2.2 Locked Dispersion Definition (DR-01)
- `omega` and `omega_expand` are imported from `ToeFormal.CPNLSE2D.Dispersion`.
- DR-01 is defined (not derived) in Lean.

## 3. Redundant Algebraic Derivations (Phase A2)
- `omegaF`, `lambdaO`, and definitional equalities (`rfl`) are imported from
  `ToeFormal.Derivation.DR01_Redundant`.

## 4. Operator-Level Structural Reduction (Phase A3)
- Opaque operators and plane-wave action axioms are imported from `ToeFormal.CPNLSE2D.PlaneWaveOperators`.
- Theorems reduce EQ-02 on plane waves to pointwise coefficient equality, without cancellation.

## 5. Dispersion Preservation Under Admissible Perturbations (Phase B)
- Perturbations and probe-relative admissibility plus the preservation lemma are imported from
  `ToeFormal.CPNLSE2D.PhaseB.DispersionPreservation`.

## 6. Limitations and Non-Claims
Not proven here (and not claimed by the imported modules):
- No analytic linearization or derivative theory.
- No derivation of dispersion from PDE analysis.
- No geometric/metric structure.
- No coherence functional.
- No general perturbation theory.
- No universality beyond the plane-wave probe family.
- No physical or empirical validation inside Lean.

## 7. Summary of Formal Results
See `#check` list below for exact names.
-/

/- --------------------------------------------------------------------------
Compilation-time checks (no new claims): the following should all succeed.
If any fail, it means your local module paths or names differ.
--------------------------------------------------------------------------- -/

-- Section 2: Formal setting
#check Field2D
#check planeWave
#check omega
#check omega_expand

-- Section 3: Redundant algebraic derivations (A2)
#check omegaF
#check lambdaO
#check omegaF_eq_omega
#check lambdaO_eq_omega
#check routeF_equals_routeO

-- Section 4: Operator-level reduction (A3)
#check Dt
#check Dxx
#check Dyy
#check Delta
#check L
#check EQ02Holds
#check eigC
#check Dt_planeWave
#check Delta_planeWave
#check iDt_planeWave_closed
#check negHalfDelta_planeWave_closed
#check EQ02Holds_planeWave_iff

-- Section 5: Perturbation preservation (Phase B)
#check Perturbation
#check AdmissibleOnPlaneWave
#check EQ02PertHolds
#check EQ02Pert_planeWave_reduces_to_same_coeff_equality

end CPNLSE2D
end ToeFormal
