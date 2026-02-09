# EQUATION INVENTORY (v4)
# Canonical CRFT Equations + LCRD Alignment Layer
# Fully synchronized with Step-5 and Step-6 results

This document is the single source of truth for all equations.
All math is kept in plain text.

--------------------------------------------------------------------
# 0. Unified Symbol Glossary
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
    lam — quartic dispersion  
    beta — sixth-order dispersion  
    rho0 — background density  
    lambda_coh — coherence penalty weight

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

## 1.3 Linear dispersion
ω²(k)  
= (k² / 2)²  
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
= (k² / 2)²  
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
+ Up(|φ|²)  
= 0

## 5.3 Continuity (corrected)
ρ_t + ∂_x[(hbar/m) ρ θ_x] = 0

## 5.4 Frozen-core dispersion
ω² = c² k² + (hbar²/(2m) + lam) k⁴

--------------------------------------------------------------------
# 6. Solitons, Vortices, Turbulence
--------------------------------------------------------------------

(unchanged; same validated expressions)

--------------------------------------------------------------------
# 7. CRFT–LCRD Alignment Layer
--------------------------------------------------------------------

This section **adds no new continuum equations**.  
It records empirical relationships proven by Step-5 and Step-6.

## 7.1 Microscopic DOFs (LCRD v1)
n_j ≥ 0  
u_j ∈ U(1)  
θ_j micro-phase  
z_j = sqrt(n_j) u_j

Coarse cell I using block size b:  
ρ_I = avg(n_j)  
θ_I = wrapped avg(θ_j)  
φ_I ≈ sqrt(ρ_I) exp(i θ_I)

## 7.2 IR dispersion calibration (CG-T1)
For ρ0 = 1, lam = 0, beta = 0:

Effective cubic nonlinearity:  
g_eff ≈ 0.1666456

## 7.3 Coarse conservation (CG-T3, CG-T4)
mass drift  ~ 1e−9  
energy drift ~ 1e−8

## 7.4 Amplitude robustness (CG-T2)
Linear regime: A ≤ 0.02

## 7.5 Nonlinear/multiscale regime (Step-6)
All CG-T5, CG-T6, CG-T7 results embedded in Step-6 doc.

--------------------------------------------------------------------
# 8. Fundamental Theory Layer (LCRD Candidate)
--------------------------------------------------------------------

This section **summarizes** how LCRD v1 maps to CRFT.  
It **does not define CRFT equations**.

## 8.1 FT symbols
n_j, u_j, θ_j, z_j  
ε, b, G, C_coh, ρ0

## 8.2 Parameters affecting CRFT alignment
g_eff, lam, beta  
ρ0, coherence penalty, block size, subsystem averaging

## 8.3 CRFT reference dispersion
ω²(k) = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶

## 8.4 Step-5 summary (IR)
g_eff = 0.1666456  
mass drift ~1e−9  
energy drift ~1e−8

## 8.5 Step-6 summary (nonlinear/multiscale)
g_eff amplitude drift ≤ 2.6e−5  
spectral-power drift ~1e−8  
long-time drift ~1e−10

--------------------------------------------------------------------
# END
