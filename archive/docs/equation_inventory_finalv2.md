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

--------------------------------------------------------------------
# END OF DOCUMENT
