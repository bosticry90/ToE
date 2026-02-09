# EQUATION INVENTORY (CRFT Master Document)
# Fully Synchronized With LCRD Step-5 (IR Calibration)

This document collects all CRFT equations exactly as validated,
and records the alignment layer with the Fundamental Theory (LCRD v1).
No new equations are introduced at the CRFT level.

--------------------------------------------------------------------
# 0. Unified Symbol Glossary (Canonical)
--------------------------------------------------------------------

Coordinates:
    x, t

Derivatives:
    ∂x, ∂xx, ∂xxx, ∂xxxx, ∇, Δ
    τ — coherence gradient-flow time

Fields:
    φ(x,t) — complex field
    ρ = |φ|² — density
    θ = arg(φ) — phase
    v = θ_x — velocity
    q, p — real components of φ = q + i p

Fourier:
    k — wavenumber
    ω — angular frequency
    φ̂(k) — Fourier transform

CRFT parameters:
    hbar, m
    g — cubic nonlinearity
    lam — k⁴ dispersion
    beta — k⁶ dispersion
    rho0 — background density
    lambda_coh — coherence penalty

Potentials:
    U(ρ), Up(ρ) = dU/dρ

Hydrodynamics:
    P(ρ) — pressure
    Q — quantum pressure
    c_eff — effective sound speed

Coherence:
    C = (|φ|² − rho0)²
    δC/δφ*

--------------------------------------------------------------------
# 1. First-Order CRFT: CP–NLSE
--------------------------------------------------------------------

## 1.1 Lagrangian
L = − hbar ρ θ_t
    − (hbar² / (2m)) ρ θ_x²
    − lam (ρ_x)² / (4ρ)
    + U(ρ)

## 1.2 Equation of motion
i φ_t
+ (1/2) φ_xx
− g |φ|² φ
+ lam φ_xxxx
+ beta φ_xxxxxx
= 0

## 1.3 Linear dispersion (canonical)
ω²(k)
= (k²/2)²
  + g rho0 k²
  + lam k⁴
  + beta k⁶

--------------------------------------------------------------------
# 2. Second-Order CRFT: CE–NWE
--------------------------------------------------------------------

## 2.1 Equation
φ_tt
+ (1/4) φ_xxxx
− g rho0 φ_xx
= 0

## 2.2 Lagrangian
L = (1/2)|φ_t|²
  − (1/2)c²|φ_x|²
  + (1/2)lam|φ_xx|²
  + (1/2)beta|φ_xxx|²
  − (1/2)g(|φ|² − rho0)²

## 2.3 Dispersion
ω²(k)
= (k²/2)²
  + g rho0 k²
  + lam k⁴
  + beta k⁶

--------------------------------------------------------------------
# 3. Hydrodynamic Lift (Madelung)
--------------------------------------------------------------------

φ = sqrt(ρ) exp(i θ)
v = θ_x

Continuity:
    ρ_t + ∂x(ρ v) = 0

Phase:
    θ_t + v θ_x + (1/ρ) ∂x P = 0

Quantum pressure:
    Q = −(1/(2ρ)) (∂xx sqrt(ρ)) / sqrt(ρ)

--------------------------------------------------------------------
# 4. Coherence Functional
--------------------------------------------------------------------

Coherence density:
    c(ρ) = (ρ_x)² / (4ρ)

Penalty:
    C = (|φ|² − rho0)²

Variation:
    δC/δφ* = 2(|φ|² − rho0)φ

Coherence-modified NLSE:
    R = R₀ + lambda_coh (|φ|² − rho0)φ

--------------------------------------------------------------------
# 5. Frozen-Core CRFT
--------------------------------------------------------------------

## 5.1 Lagrangian
L = −(hbar²/2m)|φ_x|²
    − hbar ρ θ_t
    + lam (ρ_x²)/(4ρ)
    + U(ρ)

## 5.2 EOM
i hbar φ_t
+ (hbar²/2m) φ_xx
+ Up(|φ|²) = 0

## 5.3 Continuity (correct form)
ρ_t + ∂_x[(hbar/m) ρ θ_x] = 0

## 5.4 Dispersion
ω² = c² k² + (hbar²/(2m) + lam) k⁴

--------------------------------------------------------------------
# 6. Solitons, Vortices, Turbulence
--------------------------------------------------------------------

(unchanged; all expressions validated as originally written)

--------------------------------------------------------------------
# 7. CRFT–LCRD Alignment Layer (Fundamental Theory Link)
--------------------------------------------------------------------

This section **does not add new equations**.  
It records only the relationships *proven by Step-5*.

## 7.1 Microscopic DOFs (LCRD v1)
At micro-site j:
    n_j ≥ 0        — micro-density
    u_j ∈ U(1)     — rotor
    θ_j            — micro-phase
    z_j = sqrt(n_j) u_j

Coarse cell average over block size b:
    ρ_I  = average n_j
    θ_I  = wrapped average of θ_j
    φ_I ≈ sqrt(ρ_I) exp(i θ_I)

## 7.2 Dispersion calibration (CG-T1)
For rho0 = 1, lam = 0, beta = 0:

Measured IR-effective nonlinearity:
    g_eff ≈ 0.1666

This value is **only** used when interpreting LCRD as a micro-realizer of CRFT.

## 7.3 Mass and energy conservation (CG-T3, CG-T4)
Both pass:
    mass drift  ~ 10⁻⁹
    energy drift ~ 10⁻⁸

## 7.4 Amplitude robustness (CG-T2)
Linear regime remains accurate for A ≤ 0.02.

# 6. Fundamental Theory Layer (LCRD Candidate) — Alignment Only

This section records how the existing CRFT equations in this inventory are
currently aligned with the first Fundamental Theory (FT) candidate:

- LCRD: Local Complex Rotor–Density Algebra (Candidate Algebra 01),
- its microscopic dynamics and discrete mapping,
- and the Step-5 and Step-6 simulation and calibration work.

It does not redefine the CRFT equations. The CRFT layer remains the canonical
continuum description. The FT layer is a microscopic candidate whose
coarse-grained behavior has been numerically checked against the CRFT
dispersion and conservation laws in a specific 1D regime.


## 6.1 FT symbols and objects used in alignment

At the FT layer (LCRD v1), the microscopic degrees of freedom and lattice
setup are:

- One-dimensional periodic lattice with:
  - N: number of micro sites,
  - epsilon: lattice spacing,
  - L = N * epsilon: physical length.
- At each lattice site j:
  - n_j >= 0: micro-density or occupancy,
  - u_j in U(1): micro-rotor, written as u_j = exp(i * theta_j),
  - theta_j in [0, 2 pi): micro-phase,
  - z_j = sqrt(n_j) * u_j: micro-complex amplitude.
- Coarse-graining:
  - A contiguous block of b sites defines a coarse cell I,
  - rho_I is the block-averaged density,
  - theta_I is a block-averaged or wrapped phase,
  - phi_I ≈ sqrt(rho_I) * exp(i * theta_I) is the emergent CRFT field value
    in that cell.

These objects live “under” the CRFT fields rho(x,t), theta(x,t), phi(x,t) that
appear in Sections 1–5 of this inventory.


## 6.2 Parameters relevant for CRFT alignment

The LCRD v1 dynamics and coarse-graining introduce the following parameters
that are used when aligning to the CRFT equations:

- epsilon: micro lattice spacing,
- b: block size used in the coarse-graining map,
- G, C_coh: local coupling coefficients between micro density and rotor,
- g_eff: effective CRFT nonlinearity inferred from LCRD dispersion,
- rho0: reference (background) density.

In the CRFT layer, the scalar model uses the parameters:

- g: CRFT nonlinearity,
- lam (lambda_disp): quartic dispersion coefficient,
- beta (beta_disp): sixth-order dispersion coefficient,
- lambda_coh (or similar): coherence regularization strength.

The FT calibration identifies how the microscopic parameters (G, C_coh,
epsilon, b, etc.) give rise to an effective g_eff that plugs into the CRFT
dispersion relation and nonlinearity.


## 6.3 CRFT dispersion relation (for reference)

The CRFT layer uses the linear dispersion relation around a uniform background
rho = rho0:

- omega^2(k) = (k^2 / 2)^2 + g * rho0 * k^2 + lam * k^4 + beta * k^6,

in the small-amplitude, plane-wave limit. This is the canonical form used for
all CE-NWE / CP-NLSE dispersion comparisons.

For the current LCRD calibration regime:

- rho0 = 1,
- lam = 0,
- beta = 0,

and g is treated as an effective parameter to be inferred from LCRD v1.


## 6.4 IR calibration (Step-5 summary)

In the 1D test configuration with:

- N = 512,
- epsilon = 1.0,
- L = 512.0,
- dt = 0.001,
- t_final = 10.0,
- block_size = 4,
- rho0 = 1.0,
- lam = 0, beta = 0,
- G = 12.5, C_coh = −12.5,
- A1 = A2 = A3 = 0,

we define the linear dispersion test CG-T1:

- excite a mode with mode_index = 1 at k ≈ 1.227185e−2,
- measure omega_measured,
- fit g_eff so that omega_CRFT(k; g_eff) matches |omega_measured|.

The result is:

- g_eff ≈ 0.1666456,

with excellent agreement between |omega_measured| and omega_CRFT(k; g_eff).

Additional Step-5 tests:

- CG-T2: amplitude robustness at fixed k in a small band 0 < A <= 0.02,
- CG-T3: coarse-grained mass conservation,
- CG-T4: coarse-grained energy conservation.

These show:

- A near-linear regime for A <= 0.02 where |omega_measured| ≈
  omega_CRFT(k; g_eff) with very small relative error,
- mass drift of order 10^−9,
- energy drift of order 10^−8 over t = 10,

when interpreted with g = g_eff. This validates the use of:

- g -> g_eff ≈ 0.1666456

as the effective CRFT nonlinearity for the 1D IR regime at rho0 = 1.


## 6.5 Nonlinear and multiscale calibration (Step-6 summary)

Step-6 adds three calibration tests that do not change any CRFT equations but
test their applicability over a broader nonlinear and multiscale regime:

- CG-T5: nonlinear dispersion vs amplitude,
- CG-T6: mode coupling and spectral transfer,
- CG-T7: long-time drift of invariants.

All are run in the same 1D configuration as Section 6.4, with lam = 0, beta = 0,
rho0 = 1, G = 12.5, C_coh = −12.5.

### 6.5.1 CG-T5: amplitude dependence of effective g_eff

We fix:

- mode_index = 1,
- k ≈ 1.227185e−2,
- g_eff_IR = 0.1666456,

and scan amplitudes:

- A in {1.0e−3, 3.0e−3, 1.0e−2, 2.0e−2, 5.0e−2, 1.0e−1}.

For each A we:

1. Measure omega_measured from the LCRD v1 simulation (t_final = 10),
2. Compare |omega_measured| to omega_CRFT(k; g_eff_IR),
3. Invert the CRFT dispersion to obtain g_eff(A) for that A.

Findings:

- |omega_measured| and omega_CRFT(k; g_eff_IR) match with relative error
  from ~10^−9 up to ~10^−5 across the scanned amplitudes.
- The inferred g_eff(A) satisfies:

  - g_eff(A) ≈ g_eff_IR,
  - max relative deviation |g_eff(A)/g_eff_IR − 1| ≈ 2.6e−5 at A = 0.1.

Interpretation:

- g_eff is effectively amplitude-independent for 0 < A <= 0.1 in this
  configuration.
- The “strictly linear” amplitude band 0 < A <= 0.02 from CG-T2 remains a
  conservative sub-regime, but the same CRFT dispersion form and g_eff_IR
  describe the dynamics well up to at least 10% density perturbations.


### 6.5.2 CG-T6: mode coupling and spectral transfer

We seed two coarse modes in the phase:

- k1_index = 1,
- k2_index = 2,
- A1_theta = 0.01,
- A2_theta = 0.01,

and evolve with the IR-calibrated parameters for t_final = 10.

Diagnostics:

- P0(k): initial spectral power in each coarse mode,
- PT(k): spectral power at final time,
- PT/P0: ratio of final to initial power per mode,
- sum_k P0(k) and sum_k PT(k): total spectral power.

Representative results:

- Mode 1: strong depletion, PT/P0 ~ 1.4e−3.
- Mode 2: mild change, PT/P0 ~ 0.99.
- Neighboring modes (3,4,5,…) show power at levels ~10^−3–10^0.

Total spectral power:

- sum_k P0(k) ≈ 1.6384e4,
- sum_k PT(k) ≈ 1.6384e4,
- relative drift ≈ 9.6e−9.

Interpretation:

- LCRD v1 exhibits nonlinear mode coupling and spectral transfer while
  conserving total spectral power to within ~10^−8.
- This is consistent with CRFT expectations for a conservative CP-NLSE-like
  system and supports using the same CRFT invariants for interpreting the
  coarse dynamics.


### 6.5.3 CG-T7: long-time drift of coarse invariants

We revisit a single-mode configuration:

- mode_index = 1,
- A = 0.01,
- t_final = 20.0,
- same parameters as in Step-5.

We monitor:

- M(t): coarse-grained mass,
- E(t): coarse-grained energy, evaluated with g = g_eff_IR.

Results:

- Mass drift: rel_drift_M ≈ 5.1e−11.
- Energy drift: rel_drift_E ≈ 1.0e−10.

Interpretation:

- Over a doubled time horizon compared to the Step-5 tests, coarse mass and
  energy remain invariant to within ~10^−10.
- This supports the use of CRFT mass and energy densities as appropriate
  coarse invariants for LCRD v1 in this regime.


### 6.5.4 Status

Within the tested 1D configuration (rho0 = 1, lam = beta = 0, G = 12.5,
C_coh = −12.5, A <= 0.1):

- The LCRD v1 microscopic model reproduces the CRFT dispersion with an
  effectively constant g_eff,
- Exhibits nonlinear mode coupling consistent with a conservative CP-NLSE
  system,
- Preserves coarse invariants (mass, energy, total spectral power) to very
  high accuracy.

No new CRFT equations are introduced here; this section only documents how
the existing CRFT scalar equations relate to the tested LCRD v1 dynamics.


--------------------------------------------------------------------
# END OF DOCUMENT
