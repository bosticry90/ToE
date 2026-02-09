/-
ToeFormal/Constraints/CT01_ImportCheck.lean

Purpose:
- Isolate the minimal import set required for CT-01 formalization.
- Ensure Aristotle can resolve all identifiers before any proof attempt.
- Contain zero substantive claims.
- Fail fast if names or namespaces are wrong.
-/

import Mathlib
import ToeFormal.CPNLSE2D.Dispersion
import ToeFormal.CPNLSE2D.PlaneWaveOperators
import ToeFormal.CPNLSE2D.PhaseB.DispersionPreservation

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToeFormal
open ToeFormal.CPNLSE2D

/- ------------------------------------------------------------------
Identifier scope checks
If any of these fail, Aristotle cannot reason about CT-01 yet.
------------------------------------------------------------------ -/

-- Core field and probe
#check Field2D
#check planeWave

-- Linear equation predicate
#check EQ02Holds

-- Perturbed equation predicate (Phase B)
#check EQ02PertHolds

-- Perturbation-related definitions
#check Perturbation
#check AdmissibleOnPlaneWave

-- Phase B preservation lemma (reference target)
#check EQ02Pert_planeWave_reduces_to_same_coeff_equality

end ToeFormal
