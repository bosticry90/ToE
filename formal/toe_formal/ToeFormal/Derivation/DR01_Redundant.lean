/-
ToeFormal/CPNLSE2D/DR01_Redundant.lean

Phase A2: DR-01 redundant derivations, formal equivalence of Route F and Route O.

Scope:
- This file makes NO physical claims.
- It proves that the Route F expression and Route O expression are identical as real-valued
  functions of (kx, ky), and both coincide with the locked definition `omega` from
  `ToeFormal.CPNLSE2D.Dispersion`.

What this file does NOT do (by design, at this stage):
- It does not formalize PDE derivatives (Dt, Dxx, Dyy, Laplacian) acting on exponentials.
  That would require either:
  (a) a dedicated 2D derivative operator layer with axioms/conventions, or
  (b) a full analytic development using Mathlib differentiability for ℝ → ℝ → ℝ → ℂ fields.
  Those can be added later without changing the statement proven here.

Deliverable:
- A Lean-certified equivalence layer: RouteF = RouteO = locked omega.
-/

import Mathlib
import ToeFormal.CPNLSE2D.Dispersion

namespace ToeFormal
namespace CPNLSE2D

noncomputable section
set_option autoImplicit false

/-
Route F (plane-wave substitution) produces the algebraic dispersion expression:
  omega_F(kx, ky) = (kx^2 + ky^2) / 2
-/
def omegaF (kx ky : ℝ) : ℝ :=
  (kx ^ 2 + ky ^ 2) / 2

/-
Route O (operator diagonalization) produces the algebraic eigenvalue expression:
  lambda_O(kx, ky) = (kx^2 + ky^2) / 2
-/
def lambdaO (kx ky : ℝ) : ℝ :=
  (kx ^ 2 + ky ^ 2) / 2

/-- Route F matches the locked omega definition. -/
theorem omegaF_eq_omega (kx ky : ℝ) : omegaF kx ky = omega kx ky := by
  rfl

/-- Route O matches the locked omega definition. -/
theorem lambdaO_eq_omega (kx ky : ℝ) : lambdaO kx ky = omega kx ky := by
  rfl

/-- Redundant-derivation equivalence: Route F equals Route O (purely algebraic identity). -/
theorem routeF_equals_routeO (kx ky : ℝ) : omegaF kx ky = lambdaO kx ky := by
  rfl

/-
Optional convenience lemma: both routes equal the canonical closed form.
This is useful as a single rewrite target in downstream files.
-/
theorem routeF_equals_locked_form (kx ky : ℝ) :
    omegaF kx ky = (kx ^ 2 + ky ^ 2) / 2 := by
  rfl

theorem routeO_equals_locked_form (kx ky : ℝ) :
    lambdaO kx ky = (kx ^ 2 + ky ^ 2) / 2 := by
  rfl

/-
Placeholders for the next step IF you choose to formalize the PDE-level “Route F substitution”
or the eigenfunction statement used in “Route O”.

These are intentionally left as stubs so that A2 can land now (equivalence),
while derivative/operator formalization can be added later in a dedicated module.

Suggested next file if you proceed:
  ToeFormal/CPNLSE2D/PlaneWaveOperators.lean

Suggested approach:
- Introduce opaque operators Dt, Dxx, Dyy on Field2D
- Define Delta := Dxx + Dyy and L := -(1/2) * Delta
- Add axioms for Dt and Delta acting on `planeWave` (structural conventions only)
- Prove: (i*Dt) planeWave = (omega kx ky) planeWave and L planeWave = (omega kx ky) planeWave
- Then discharge the “Route F” and “Route O” narratives at the operator level.
-/

end
end CPNLSE2D
end ToeFormal
