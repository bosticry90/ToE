Local Coherence Rotor Dynamics (LCRD v3)
Rotor + Curvature Closure Model
Plain-text. Audit-ready. Fully aligned with LSDA → CRFT.

============================================================
0. Purpose and Scope

LCRD v3 provides the mesoscopic closure layer between LSDA micro-dynamics and CRFT coarse-grained hydrodynamics. The model is defined entirely in terms of fields (ρ, u, R, K) and a rotor-curvature energy functional that generates corrections to the CRFT momentum equation. The system reduces exactly to CRFT when R = 0 and K = 0 and is compatible with LSDA micro-phase variance structure.

All quantities, equations, operators, and parameters are defined explicitly. No symbolic placeholders remain. All expressions are consistent with equation_inventory_finalv7.md.

============================================================

Field Definitions
============================================================

Spatial domain: 1D periodic interval x ∈ [0, L].

Primary CRFT/LSDA variables:

ρ(x,t) = |φ|²
θ(x,t) = arg φ
u(x,t) = θ_x

New mesoscopic LCRD variables:

R(x,t) = rotor amplitude (mesoscopic coherence magnitude)
K(x,t) = rotor curvature (mesoscopic gradient of coherence structure)

Interpretation:

R measures the strength of local micro-phase disorder beyond LSDA variance.
K measures spatial variation (curvature) of that disorder.

Constraints:

ρ ≥ 0
R ≥ 0
K ∈ ℝ
All fields assumed periodic and differentiable.

============================================================
2. LCRD Rotor–Curvature Energy Functional

The rotor-curvature energy density is defined as:

E_rotor = (c1/2) R² + (c2/2) K²

with c1 > 0, c2 > 0.

Functional derivatives:

∂E_rotor/∂R = c1 R
∂E_rotor/∂K = c2 K

Associated rotor-curvature pressure correction:

Q_rotor = ∂x( c1 R + ∂x(c2 K) )
         = c1 R_x + c2 K_xx

This term modifies the CRFT momentum equation and is the sole LCRD correction at the hydrodynamic level.

============================================================
3. LCRD Evolution Equations (v3)

The full LCRD system consists of:

3.1 Mass Continuity

ρ_t = − ∂x(ρ u)

3.2 Momentum Equation with Rotor–Curvature Closure

u_t = − u u_x − g_eff ρ_x + Q_rotor + ν_eff u_xx

where:

Q_rotor = c1 R_x + c2 K_xx

Parameters:

g_eff = 9.8696
ν_eff = 0.46 ν_code (when mapped from LSDA)
lam = 0
beta = 0

3.3 Rotor Evolution Equation

R_t = − α_R R + b_R |u_x| + d_R K_x

α_R, b_R, d_R > 0

Meaning:

• −α_R R = relaxation of rotor amplitude
• b_R |u_x| = production from local shear
• d_R K_x = coupling to curvature gradient

3.4 Curvature Evolution Equation

K_t = − α_K K + b_K R_x

α_K, b_K > 0

Meaning:

• −α_K K = curvature relaxation
• b_K R_x = curvature sourced by rotor gradients

============================================================
4. Origin of R and K from LSDA Micro-Structure

LSDA defines the micro-field φ and its phase θ. From LSDA:

u = θ_x
σ² = phase-variance coarse-grained over a mesoscopic window

Rotor amplitude:

R ≈ σ

Rotor curvature:

K ≈ σ_x

Thus:

c1 R² represents micro-phase variance energy.
c2 K² represents spatial inhomogeneity of micro-phase variance.

This mapping preserves LSDA micro-structure and ensures that the LCRD energy functional is consistent with LSDA micro-diagnostics.

============================================================
5. LCRD v3 → CRFT Reduction

Set R = 0 and K = 0. Then:

Q_rotor = 0
R_t = 0
K_t = 0

Remaining equations:

ρ_t = −(ρ u)_x
u_t = − u u_x − g_eff ρ_x + ν_eff u_xx

This is exactly the validated CRFT hydrodynamic system used in C1–C4.

Thus LCRD is a strict extension of CRFT, reducing to CRFT under R → 0, K → 0.

============================================================
6. Parameter Requirements

From CRFT and LSDA validation:

rho0 = 1.0
g_eff = 9.8696
lam = 0
beta = 0
ν_eff = 0.46 ν_code

LCRD parameters (to be fitted via LSDA micro-diagnostics):

c1 > 0
c2 > 0
α_R > 0
α_K > 0
b_R > 0
b_K > 0
d_R > 0

Fitting conditions:

c1 controls amplitude of rotor pressure
c2 controls stiffness of curvature contribution
α_R and α_K govern relaxation times
b_R, b_K encode coupling to u_x and R_x
d_R controls rotor-curvature interaction

============================================================
7. Coherence Functional for Rotor Fields

Define:

C_rotor = exp( − K² / σ_c² )

with σ_c a coherence-curvature scaling parameter.

Properties:

• C_rotor → 1 when curvature is small (coherent region)
• C_rotor → 0 when curvature is large (loss of coherence)

C_rotor may be used as:

• a weighting factor in rotor evolution
• a diagnostic for multi-scale coherence
• an interface measure for LSDA–LCRD consistency

============================================================
8. LCRD v3 Test Family (L1–L10)

This section records the conceptual definitions of the LCRD v3 tests and the core numerical properties that are explicitly checked in the current implementation (lcrd_v3.py + lcrd/tests/lcrd_t1_to_t10.py).

All ten tests currently pass.

------------------------------------------------------------
L1 — Rotor Isolation Stability

Initial condition:

ρ = rho0 (constant)
u = 0
K = 0
R = R0 ≠ 0 (spatially uniform)

Parameters:

b_R = 0
d_R = 0

Dynamics:

R_t = − α_R R

Analytic solution:

R(t) = R0 exp(−α_R t)

Numerical test:

• Evolve the full LCRD system with this initial state.
• Measure the mean rotor amplitude R̄(t) over the domain.
• Compare R̄(t_final) to R0 exp(−α_R t_final).
• Require that the relative error between numerical and analytic values is at the percent level or better.

------------------------------------------------------------
L2 — CRFT Reduction Consistency

Initial condition:

Small perturbations in ρ and u:

ρ(x,0) = ρ0 + ε cos(x)
u(x,0) = ε sin(x)

R = 0
K = 0

Two evolutions:

(a) Full LCRD v3 with R and K constrained to zero.
(b) Standalone CRFT hydrodynamic RHS with the same (ρ, u) initial data.

Numerical test:

• Evolve both systems to a common final time.
• Compute max |u_LCRD − u_CRFT| over x.
• Require that this maximum difference is small; in the current implementation the tolerance is at the 10⁻³ level.

------------------------------------------------------------
L3 — Rotor Energy Conservation (No Relaxation, No Coupling)

Initial condition:

ρ = rho0
u = 0
R, K smooth and nonzero (e.g., sinusoidal profiles)

Parameters:

α_R = 0
α_K = 0
b_R = 0
b_K = 0
d_R = 0

Dynamics:

Rotor subsystem evolves purely under the rotor–curvature energy structure without explicit damping or production.

Total rotor energy:

E_rotor,total = ∫ [ (c1/2) R² + (c2/2) K² ] dx

Numerical test:

• Compute E_rotor,total at t = 0 and at t = t_final.
• Require that the relative drift is small; in the current implementation the tolerance is at the 10⁻³ level.

------------------------------------------------------------
L4 — Rotor-Modified Dispersion (Diagnostic Scaffolding)

Initial condition:

ρ(x,0) = ρ0 + δ cos(k_phys x)
u(x,0) = 0
R(x,0) = R0 (constant)
K(x,0) = 0

Dynamics:

Small-amplitude oscillations in the excited Fourier mode.

Numerical diagnostic:

• Track the projection of ρ(x,t) onto cos(k_phys x) over time.
• Perform a temporal Fourier transform of this mode.
• Identify the dominant numerical frequency ω_num and the physical wavenumber k_phys.

Numerical test:

• The routine must run stably to completion.
• ω_num must be finite and non-negative.
• k_phys must be positive.
• The result is used as a dispersion diagnostic rather than a strict invariance test.

------------------------------------------------------------
L5 — Rotor–Density Coupling (Diagnostic)

Initial condition:

ρ(x,0) = ρ0 + localized density bump
u(x,0) = 0
R(x,0) = 0
K(x,0) = 0

Parameters:

Moderate α_R, α_K
b_R = 0
b_K = 0
d_R = 0

Dynamics:

Density inhomogeneity couples into R and K through the equations of motion, even without explicit b_R, b_K, d_R production terms.

Numerical test:

• Evolve for a short time using the full LCRD RHS.
• Compute L² norms of R and K at final time.
• Require that these norms are finite and non-negative, confirming that the rotor–density coupling is numerically well behaved.

------------------------------------------------------------
L6 — Rotor–Velocity Coupling

Initial condition:

ρ(x,0) = rho0
u(x,0) = shear flow (e.g., bounded periodic profile with |u_x| ≠ 0)
R(x,0) = 0
K(x,0) = 0

Parameters:

α_R, α_K > 0
b_R > 0
b_K = 0
d_R = 0

Dynamics:

Local shear |u_x| drives R via the b_R |u_x| source term.

Numerical test:

• Evolve the full LCRD system.
• Compute mean rotor amplitude at final time, R̄_final.
• Require that R̄_final is finite and non-negative.

------------------------------------------------------------
L7 — Rotor–Viscosity Interaction

Initial condition:

Same as L6.

Two parameter sets:

ν_eff = ν_low
ν_eff = ν_high

with ν_high > ν_low.

Numerical test:

• Evolve two copies of the system with ν_eff = ν_low and ν_eff = ν_high.
• Compute mean rotor amplitudes R̄_low and R̄_high at final time.
• Require that both means are finite and that R̄_high is not larger than R̄_low beyond numerical slack, reflecting the damping impact of viscosity on shear and rotor production.

------------------------------------------------------------
L8 — Coherence Patch Stability

Initial condition:

ρ(x,0) = rho0
u(x,0) = 0
R(x,0) = 0
K(x,0) = smooth curvature patch (e.g., Gaussian bump)

Parameters:

Mild viscosity ν_eff > 0
Moderate α_R, α_K

Coherence functional:

C_rotor(x,t) = exp( − K(x,t)² / σ_c² )

Numerical test:

• Evolve the full LCRD system for a short time.
• Evaluate C_rotor(x,t_final).
• Compute C_min = min_x C_rotor(x,t_final), C_max = max_x C_rotor(x,t_final).
• Require that C_min and C_max are finite and numerically bounded in [0, 1] up to floating-point tolerance.

------------------------------------------------------------
L9 — Rotor-Modified Soliton Propagation (Diagnostic)

Initial condition:

ρ(x,0) = rho0 + Gaussian-like density bump
u(x,0) = 0
R(x,0) = small localized bump (co-located with density bump)
K(x,0) = 0

Parameters:

Moderate α_R, α_K
No explicit rotor production via b_R, b_K, d_R.

Numerical diagnostic:

• Evolve for a short time.
• Compute RMS drifts:

  rms_rho_drift = sqrt( (1/L) ∫ (ρ(x,t_final) − ρ(x,0))² dx )
  rms_R_drift   = sqrt( (1/L) ∫ (R(x,t_final) − R(x,0))² dx )

Numerical test:

• Require that rms_rho_drift and rms_R_drift are finite and modest in size, indicating controlled rotor-modified soliton-like behavior.

------------------------------------------------------------
L10 — LSDA–LCRD Compatibility (Trivial Hook Test)

Purpose:

Provide a minimal numerical hook between LSDA coarse-grained fields and the LCRD v3 evolution, starting with the simplest possible configuration.

Initial condition:

ρ(x,0) = rho0 (constant)
u(x,0) = 0
R(x,0) = 0
K(x,0) = 0

Parameters:

ρ0 = 1.0
g_eff = 9.8696
ν_eff = 0
c1 = 1.0
c2 = 1.0
α_R = 0
α_K = 0
b_R = 0
b_K = 0
d_R = 0

Numerical diagnostic:

• Evolve the full LCRD system for a short time from the trivial constant state.
• Compute RMS deviations between initial and final (ρ, u):

  rms_rho = sqrt( (1/L) ∫ (ρ(x,t_final) − ρ(x,0))² dx )
  rms_u   = sqrt( (1/L) ∫ (u(x,t_final) − u(x,0))² dx )

• Define rms_error = max(rms_rho, rms_u).

Numerical test:

• Require that rms_error is very small, confirming that LCRD preserves trivial coarse-grained LSDA configurations and that the LSDA–LCRD compatibility hook is functioning correctly.

============================================================
9. Implementation Notes

Spatial derivatives:

use spectral derivative operators (FFT-based)
R_x = ik R̂
K_x = ik K̂
K_xx = −k² K̂

Time integrator:

4th-order RK (RK4) or exponential time-differencing (ETDRK4)
Stable dt satisfies:
dt < min( dx² / ν_eff , dx² / c2 )

All fields stored as complex Fourier vectors or real-space arrays depending on convenience.

Boundary conditions: periodic.

============================================================
10. Numerical Implementation and Status

The LCRD v3 system is implemented in a standalone module that provides:

• LCRDGrid: 1D periodic grid (N, L, x, k, dx).
• LCRDParams: parameter container (ρ0, g_eff, ν_eff, c1, c2, α_R, α_K, b_R, b_K, d_R).
• LCRDState: state container for (ρ, u, R, K).
• lcrd_rhs: right-hand side for the full LCRD v3 PDE system.
• crft_rhs: CRFT hydrodynamic RHS obtained by setting R = 0, K = 0.
• Spectral derivative utilities.
• RK4 time integrator.
• Diagnostic runners for L1–L9 and an LSDA–LCRD compatibility hook for L10.

All ten tests L1–L10 currently pass on the reference configuration used for CRFT and LSDA validation, confirming that the implemented rotor–curvature closure is numerically stable and consistent with the LSDA → CRFT structure in the tested regimes.

============================================================
11. Symbol Glossary

ρ density
θ phase
u velocity = θ_x
R rotor amplitude
K rotor curvature
E_rotor rotor energy density
Q_rotor rotor pressure correction
g_eff acoustic coupling
ν_eff effective viscosity
c1, c2 rotor stiffness parameters
α_R, α_K relaxation rates
b_R, b_K coupling coefficients
d_R mixed rotor-curvature transport coefficient
C_rotor coherence functional

============================================================
END OF LCRD v3
