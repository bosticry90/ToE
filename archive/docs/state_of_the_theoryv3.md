# STATE OF THE THEORY (v2) — CRFT + LCRD ALIGNMENT

Last updated: 2025-11-27

Scope:

- This document tracks the **current working scalar field theory (CRFT)** and its
  **alignment with the LCRD fundamental-theory candidate** (Local Complex
  Rotor–Density Algebra) via the Step-5 and Step-6 calibration program.
- All equations recorded here must also appear in the canonical
  `equation_inventory_finalv2.md`. No new equations are introduced here.
- Math is kept in plain text (no LaTeX) to reduce hallucination risk and to keep
  the equation inventory as the single source of truth.


---

## 1. Canonical CRFT scalar model (continuum, CE-NWE / CP-NLSE)

Working assumptions:

- One spatial dimension x with periodic boundary conditions.
- Complex scalar field:
  - phi(x,t) is the primary field,
  - rho(x,t) = |phi|^2 is the density,
  - theta(x,t) = arg(phi) is the phase,
  - v(x,t) = theta_x is the hydrodynamic velocity.
- We work classically, non-relativistically, with no claim of fundamental status.

The **canonical evolution equation** is the CP-NLSE / CE-NWE form:

- i phi_t = -(1/2) phi_xx + g |phi|^2 phi
           + lam phi_xxxx + beta phi_xxxxxx
           + (coherence-penalty term if included),

with:

- g: cubic nonlinearity (effective interaction),
- lam (lambda_disp): quartic dispersion coefficient,
- beta (beta_disp): sixth-order dispersion coefficient.

Hydrodynamic representation uses:

- rho_t + (rho v)_x = 0   (continuity),
- theta_t + (1/2) v^2 + g rho + dispersion terms + coherence terms = 0.


---

## 2. Coherence functional and CE-NWE structure

We continue to treat coherence via a **coherence functional** C[phi] of the form:

- C[phi] ~ (1/2) lambda_coh ∫ (rho(x) - rho0)^2 dx,

or similar penalty that suppresses large deviations from a chosen background
density rho0. This produces an additional term in the equation of motion:

- + lambda_coh (rho - rho0) phi.

For the current LCRD calibration and Step-5 / Step-6 tests we have:

- Focused on the **simplified case** lam = 0, beta = 0, lambda_coh = 0
  in the dynamical equation used for comparisons.
- Treated coherence primarily through the LCRD couplings (G, C_coh) and
  through the existence of a well-behaved hydrodynamic limit, not by adding
  explicit continuum coherence terms into the CP-NLSE testbed.


---

## 3. Linear dispersion and IR calibration target (CRFT side)

Around a uniform background rho = rho0, with small-amplitude plane-wave
perturbations of the form:

- phi(x,t) = sqrt(rho0) + A exp(i (k x - omega t)),

the working **CRFT dispersion relation** is:

- omega^2(k) = (k^2 / 2)^2 + g rho0 k^2 + lam k^4 + beta k^6,

with lam = 0, beta = 0 in the current test configuration.

For the IR calibration used in LCRD Step-5 and Step-6:

- rho0 = 1,
- lam = 0,
- beta = 0,
- g is treated as an effective parameter to be inferred from LCRD.


---

## 4. Fundamental Theory candidate (LCRD v1)

The Fundamental Theory (FT) program defines a **microscopic candidate**:

- LCRD: Local Complex Rotor–Density Algebra,

with:

- 1D periodic lattice:
  - N sites,
  - lattice spacing epsilon,
  - physical length L = N * epsilon.
- At each site j:
  - n_j >= 0: micro-density (occupancy),
  - u_j in U(1): rotor, u_j = exp(i theta_j),
  - theta_j in [0, 2 pi),
  - z_j = sqrt(n_j) u_j: micro-complex amplitude.

Coarse-graining:

- Blocks of b sites define coarse cells I.
- rho_I is the average of n_j over the block.
- theta_I is a wrapped average of theta_j over the block.
- phi_I ≈ sqrt(rho_I) exp(i theta_I) is the emergent CRFT field value
  associated with the cell.

Working microscopic dynamics (LCRD v1) are defined in the FT documents and
simulator code, with parameters:

- epsilon: lattice spacing,
- b: block size,
- G, C_coh: local couplings between density and rotor,
- rho0: reference density used in initialization,
- and a time-stepping scheme that conserves discrete analogues of mass and
  energy.


---

## 5. FT Step-5: IR dispersion and conservation calibration

FT Step-5 required that LCRD v1, under the chosen coarse-graining, reproduce:

1. The CRFT dispersion relation near k -> 0 up to an **effective** g_eff.  
2. Coarse-grained mass conservation.  
3. Coarse-grained energy conservation (with g identified as g_eff).  
4. A near-linear regime in amplitude at fixed k.

The key tests (all using 1D, N = 512, epsilon = 1.0, L = 512, dt = 0.001,
t_final = 10.0, block_size = 4, rho0 = 1.0, lam = beta = 0) are:

- CG-T1: linear dispersion test at small k.
- CG-T2: amplitude robustness at fixed k.
- CG-T3: coarse-grained mass conservation.
- CG-T4: coarse-grained energy conservation.

With parameters:

- mode_index = 1,
- A1 = A2 = A3 = 0 (no nonlinear seeding in density/phase for CG-T1–T4),
- G = 12.5,
- C_coh = −12.5,

we obtained:

- A fitted effective nonlinearity g_eff ≈ 0.1666456 for mode_index = 1.  
- Excellent agreement |omega_measured| ≈ omega_CRFT(g_eff) at k ≈ 1.227185e−2.  
- Mass drift of order 10^−9 over t = 10.  
- Energy drift of order 10^−8 over t = 10 when interpreted with g_eff.

This established:

- An IR mapping between LCRD v1 and CRFT with g -> g_eff,
- Coarse-grained discrete mass and energy behaving as invariants over the
  test window,
- A well-behaved near-linear regime for A up to 0.02 in the CG-T2 scans.


---

## 6. FT Step-6: Nonlinear and multiscale calibration

Step-6 extends the calibration beyond strictly linear IR behavior to test
nonlinearity and multiscale features, without introducing any new CRFT
equations. It adds:

- CG-T5: nonlinear dispersion vs amplitude,
- CG-T6: mode coupling / spectral transfer,
- CG-T7: long-time drift of invariants.

The tests are run in the same 1D configuration as Step-5 with:

- N = 512,
- epsilon = 1.0,
- L = 512.0,
- dt = 0.001,
- block_size = 4,
- rho0 = 1.0,
- lam = 0, beta = 0,
- G = 12.5, C_coh = −12.5,
- A1 = A2 = A3 = 0 unless otherwise specified.

### 6.1 CG-T5: Nonlinear dispersion vs amplitude

We fix the mode:

- mode_index = 1,
- k ≈ 1.227185e−2,

and the IR-calibrated effective coupling:

- g_eff_IR = 0.1666456.

We then scan amplitudes:

- A in {1.0e−3, 3.0e−3, 1.0e−2, 2.0e−2, 5.0e−2, 1.0e−1},

for t_final = 10.0. For each amplitude we measure omega_measured and infer
an effective g_eff(A) by inverting the CRFT dispersion relation with lam = beta = 0.

Results (representative):

- |omega_measured| agrees with omega_CRFT_IR (using g_eff_IR) with relative
  error:
  - ~1.3e−7 at A = 1.0e−3,
  - ~1.2e−7 at A = 3.0e−3,
  - ~3.5e−9 at A = 1.0e−2,
  - ~3.9e−7 at A = 2.0e−2,
  - ~3.2e−6 at A = 5.0e−2,
  - ~1.3e−5 at A = 1.0e−1.

- The inferred g_eff(A) satisfies:

  - g_eff(A) ≈ g_eff_IR for all A tested,
  - max relative deviation |g_eff(A)/g_eff_IR − 1| ≈ 2.6e−5 at A = 0.1.

Interpretation:

- For this configuration, LCRD v1 behaves as an **almost amplitude-independent
  nonlinear medium** up to at least A = 0.1 (10% density perturbation).
- The earlier “strictly linear” band A ≤ 0.02 remains conservative; Step-6
  shows that the same g_eff works with very small corrections well beyond
  that band.

We continue to treat:

- g_eff_IR = 0.1666456

as the effective CRFT nonlinearity for the 1D calibration at rho0 = 1, with
the understanding that g_eff(A) remains extremely close to this value for
0 < A ≤ 0.1.


### 6.2 CG-T6: Mode coupling and spectral transfer

Here we seed two coarse modes in the phase:

- k1_index = 1,
- k2_index = 2,
- A1_theta = 0.01,
- A2_theta = 0.01,

and evolve with the same parameters as above for t_final = 10.0.

Diagnostics:

- P0(k): initial spectral power in each coarse mode,
- PT(k): spectral power at final time,
- PT / P0: ratio indicating redistribution.

Representative outcome:

- Mode 1:
  - P0(k1) ≈ 4.05e−1,
  - PT(k1) ≈ 5.74e−4,
  - PT / P0 ≈ 1.4e−3 (strong depletion).

- Mode 2:
  - P0(k2) ≈ 4.11e−1,
  - PT(k2) ≈ 4.07e−1,
  - PT / P0 ≈ 0.99 (mild change).

- Neighboring modes (3, 4, 5, …) pick up or lose power at levels
  ~10^−3–10^0 in consistent patterns.

- Total spectral power:
  - sum_k P0(k) ≈ 1.6384e4,
  - sum_k PT(k) ≈ 1.6384e4,
  - relative drift ≈ 9.6e−9.

Interpretation:

- LCRD v1 exhibits **nontrivial nonlinear mode coupling** that redistributes
  power between modes, while conserving total spectral power to within
  ~10^−8.
- This supports the view that the microscopic dynamics can support a
  CP-NLSE-like turbulent or multiscale regime without introducing spurious
  growth or decay in coarse invariants.


### 6.3 CG-T7: Long-time drift of invariants

We return to a single-mode perturbation:

- mode_index = 1,
- A = 0.01,
- t_final = 20.0 (twice the CG-T1–T4 horizon),
- other parameters as in CG-T1–T4.

We track:

- M(t): coarse-grained mass,
- E(t): coarse-grained energy, evaluated using g = g_eff_IR.

Results:

- M(0) and M(T) agree with relative drift:

  - rel_drift_M ≈ 5.1e−11.

- E(0) and E(T) agree with relative drift:

  - rel_drift_E ≈ 1.0e−10.

Interpretation:

- Over a doubled time window, LCRD v1 preserves coarse-grained invariants
  at the level of ~10^−10. This is consistent with a robust conservative
  microscopic dynamics and with the CP-NLSE interpretation using g_eff_IR.


---

## 7. Current status and next steps

As of this document version:

1. **CRFT layer**  
   - The scalar CE-NWE / CP-NLSE model with parameters (g, lam, beta,
     lambda_coh) remains the canonical continuum description.
   - For the 1D IR calibration with lam = beta = 0 and rho0 = 1, g has been
     effectively pinned to:
       - g_eff_IR ≈ 0.1666456,
     based on LCRD v1 dispersion matching.

2. **LCRD v1 (Fundamental Theory candidate)**  
   - Satisfies Step-5 IR calibration requirements for:
     - dispersion,
     - mass conservation,
     - energy conservation,
     - small-amplitude linear behavior.  
   - Satisfies Step-6 nonlinear and multiscale calibration in the tested
     configuration:
     - g_eff(A) nearly constant for 0 < A ≤ 0.1,
     - nonlinear mode coupling with total spectral power conserved to ~10^−8,
     - long-time coarse mass and energy drift only ~10^−10 over t = 20.

3. **Interpretive stance**  
   - LCRD v1 is a **working microscopic surrogate** that reproduces the
     current CRFT scalar model in a well-tested regime.
   - No claim is made that LCRD v1 is a final or unique fundamental theory.
   - All higher-level field-theory claims must still be grounded in the
     documented CRFT equations and in explicit simulation results.

4. **Next steps (beyond Step-6)**  
   Future FT steps may include:
   - Extending tests to higher modes and broader k-ranges,
   - Exploring multi-soliton and turbulence analogues under LCRD v1,
   - Refining or replacing the microscopic rule if new failures appear,
   - Carefully reevaluating coherence-functional behavior in more complex
     scenarios.

Until such steps are completed, this document and the equation inventory
codify the **current validated status** of the scalar CRFT layer and its
LCRD v1 microscopic surrogate.
