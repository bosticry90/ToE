/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 46b9b111-de8e-4782-bee7-1c9079311483

Aristotle encountered an error while processing imports for this file.
Error:
Axioms were added during init_sorries: ['ToeFormal.CPNLSE2D.Delta_planeWave', 'ToeFormal.CPNLSE2D.Dt_planeWave']
-/

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
