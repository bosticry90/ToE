STATE OF THE THEORY (v4)
LCRD v2 Baseline and Roadmap
Updated after full code synchronization and v2 structural lock
Source files referenced: config.py, state.py, backend.py, coarse_grain.py, diagnostics.py, stepper_v2.py, runners.py, CG-T8–CG-T11 tests, and prior state_of_the_theory versions.
This file supersedes all earlier versions.

----------------------------------------------------------------
1. PURPOSE
----------------------------------------------------------------

This document is the single authoritative description of the current theory stack:

1. The CRFT continuum model (Coherence-Regularized Field Theory).
2. The LCRD microscopic model (Local Coherence Rotor Dynamics).
3. The validated mapping between them.
4. The locked v2 micro-parameters and verified simulation behavior.
5. The current structural test suite (CG-T8 through CG-T11).

This version removes all accidental renaming and restores CRFT to its correct name:  
Coherence-Regularized Field Theory.

It integrates all results from the test files and the simulator code you provided and reflects the working v2 micro-model that now executes cleanly across all tests.

----------------------------------------------------------------
2. THE TWO-LAYER MODEL
----------------------------------------------------------------

We work with a two-layer structure:

Layer 1: CRFT (Coherence-Regularized Field Theory)
- A classical, nonrelativistic complex scalar field theory.
- Primary field: phi(x,t).
- Derived fields:
  rho = |phi|^2
  theta = arg(phi)
- Governing equation is the CP-NLSE / CE-NWE form.
- Linearized dispersion:
  omega(k)^2 = (k^2/2)^2 + g_eff rho0 k^2 + lam k^4 + beta k^6
- In the present program:
  rho0 = 1, lam = 0, beta = 0
  g_eff determined empirically from LCRD v1: g_eff = 0.1666456

Layer 2: LCRD (Local Coherence Rotor Dynamics)
- A microscopic rotor-density lattice model.
- Variables:
  n_j(t): micro density
  theta_j(t): micro phase
  z_j = sqrt(n_j) exp(i theta_j): micro complex amplitude
- Defined on a periodic lattice j = 0,…,N−1 with spacing epsilon.
- Dynamics governed by local fluxes and Laplacians.
- Coarse-graining over blocks of B sites yields the emergent CRFT field:
  phi_I = sqrt(rho_I) exp(i theta_I)

The research program establishes how LCRD reproduces CRFT behavior after coarse-graining.

----------------------------------------------------------------
3. CANONICAL CRFT EQUATIONS (CONTINUUM)
----------------------------------------------------------------

Canonical governing equation (CP-NLSE / CE-NWE hybrid form):

i phi_t  
+ (1/2) phi_xx  
- g |phi|^2 phi  
+ lam phi_xxxx  
+ beta phi_xxxxxx  
+ (optional coherence penalty term)  
= 0

In the working configuration, lam = 0, beta = 0, and coherence penalty is off.

Hydrodynamic representation (informal summary):
rho_t + (rho v)_x = 0
theta_t + (1/2) v^2 + g rho + dispersive terms = 0

Linearized dispersion around rho0 = 1:
omega(k)^2 = (k^2/2)^2 + g_eff k^2
with g_eff = 0.1666456 from CG-T1 of LCRD v1.

----------------------------------------------------------------
4. LCRD MICROSCOPIC MODEL (v2 IMPLEMENTATION)
----------------------------------------------------------------

All functional details of LCRD v2 come directly from the provided simulator files:

- stepper_v2.py (definitive update rule)
- config.py (parameter container)
- state.py (initialization and state evolution container)
- coarse_grain.py (mapping micro → coarse)
- diagnostics.py (dispersion, drift, spectral power)
- backend.py (CPU)
- runners.py (test harness structuring)

The v2 stepping structure is defined by two coupled equations:

Phase update (schematic):
theta_t ≈  
  - G_density (n_j - rho0)  
  + G_phase Laplacian(theta)  
  + higher-order finite-difference terms from the stepper

Density update (schematic):
n_t ≈  
  - divergence of J  
  + (G_coh + nu_n) Laplacian(n)
where J is the discrete current:
J_{j+1/2} = average(n_j, n_{j+1}) * gradient(theta)

These are not analytic equations; they are the conceptual interpretation of the explicit finite-difference code in stepper_v2.py, which is the canonical definition of LCRD v2.

----------------------------------------------------------------
5. LOCKED v2 BASELINE PARAMETERS
----------------------------------------------------------------

The stable, validated v2 baseline is:

G_phase = 4.5
G_density = 10.0
G_coh = 1.0
nu_n = 0.0

Legacy parameters (kept for compatibility):
A1 = 1.0
A2 = 0.0
A3 = 0.0
G = 12.5
C_coh = -12.5

Lattice and integration defaults for all v2 tests:
N = 512
epsilon = 1
dt = 0.001
t_final = 10
block_size = 4
rho0 = 1

These values come directly from the test scripts you ran and reflect the actual configuration that produced successful runs.

----------------------------------------------------------------
6. COARSE-GRAINING
----------------------------------------------------------------

coarse_grain_lcrd produces:
rho_I = average(n_j over block)
theta_I = wrapped average of theta_j
phi_I = sqrt(rho_I) exp(i theta_I)

This is the only accepted coarse mapping.
All dispersion, drift, and spectral diagnostics operate on this coarse field.

----------------------------------------------------------------
7. TEST SUITE CG-T8 THROUGH CG-T11 (v2 STRUCTURAL SUITE)
----------------------------------------------------------------

All results summarized here are taken from your successful full test sweep.  
These tests certify structural correctness, not physical calibration.

CG-T8 v2 k-scan
- Confirms frequency scaling with k is stable and monotonic.
- Low modes behave sensibly.
- No blow-ups or pathological oscillations.

CG-T8 v2 calibration
- Compares measured omega(k) to CRFT omega(k).
- RMS error remains O(1), as expected before calibration.
- Not used for fitting; only a qualitative check.

CG-T9 v2 amplitude scan (canonical amplitude test)
- Scans A from 1e-3 to 1e-1.
- omega(A) shows weak nonlinear dependence.
- System remains stable throughout.
- No anomalous amplitude effects.

CG-T10 v2 mode coupling
- Strong nonlinear transfer between modes.
- Total spectral power conserved to within drift ~1e-8.
- Confirms the v2 stepping supports multiscale structure.

CG-T11 v2 long-time drift
- Mass drift ~1e-9 (excellent).
- Energy-proxy drift ~0.14 (within structural tolerance 0.2).
- Confirms long-time stability.

CG-T11 v2 k–A drift mapping
- Mass drift extremely small for modes m=1–32 across A≤0.2.
- Power drift remains within structural tolerance for the same window.
- High-k/high-A combinations show large drift, defining the UV boundary.

----------------------------------------------------------------
8. NUMERICAL VALIDITY WINDOW (OFFICIAL)
----------------------------------------------------------------

Definitions:
DeltaM/M = (M(T) - M(0)) / M(0)
DeltaP/P = (P(T) - P(0)) / P(0)

Tolerances:
|DeltaM/M| ≤ 0.05
|DeltaP/P| ≤ 1.0

Empirical findings:
- Modes m = 1–32 for amplitudes A in [1e-3, 0.2] show:
  Mass drift 10^{-11}–10^{-3}
  Power drift ≤ 0.75
  Smooth, stable omega(k,A)

- Mode m = 48 behaves as a transitional edge mode.
- Mode m = 64 becomes unreliable for A > 0.05.

Therefore the official validity window for LCRD v2 is:

Modes m = 1–32  
Amplitude A = 1e-3 to 0.2

Outside this domain, the system enters a strongly nonlinear/UV regime
and dynamics are treated as exploratory but not physically reliable.

----------------------------------------------------------------
9. STATUS OF THE THEORY
----------------------------------------------------------------

All v2 tests pass under structural tolerances.
The system is clean, stable, and fully executable across the entire suite.

CRFT remains the canonical coarse theory.
LCRD v2 is a structurally validated micro-realizer.
The mapping between layers is qualitatively correct; quantitative IR calibration is deferred.

This document is now synchronized with all code files, test outputs,
and prior versions, and uses the correct terminology.

----------------------------------------------------------------
10. NEXT STEPS
----------------------------------------------------------------

1. Begin IR calibration for v2 using targeted k-scans.
2. Introduce controlled parameter sweeps for G_phase and G_density.
3. Define v2-specific effective g_eff(k).
4. Proceed to coherent-structure tests (solitons, oscillons).
5. Expand regression tests to automatically enforce the validity window.

----------------------------------------------------------------
END OF DOCUMENT
----------------------------------------------------------------
