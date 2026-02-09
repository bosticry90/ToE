# EQUATION INVENTORY (CRFT Master Document)
*Hierarchically Organized, with Unified Symbol Glossary*

This document catalogs all equations used in the **Coherence-Regularized Field Theory (CRFT)** program.  
It presents the CP-NLSE (first-order), CE-NWE (second-order), hydrodynamic lifts, coherence functionals, geometric extensions, soliton structures, turbulence models, coherence metrics, regime classifiers, and output bundling systems.

All equations are reproduced strictly from the provided source document (no additions).  
:contentReference[oaicite:1]{index=1}

---

# UNIFIED SYMBOL GLOSSARY

## Coordinates & Derivatives
- **x, t** — spatial and temporal coordinates  
- **∂x, ∂xx, ∇, Δ** — spatial derivatives  
- **τ** — artificial coherence-evolution time (gradient flow)  

## Fourier / Spectral Variables
- **k** — wave number  
- **omega (ω)** — angular frequency  
- **ψ̂(k)** — Fourier transform of field ψ  

## Fields
- **φ(x,t)** — complex scalar field  
- **ψ(x,t)** — alternative complex field (turbulence context)  
- **χ(x,t)** — real coherence/strain field (coupled CRFT)  
- **q(x,t), p(x,t)** — real components of φ = q + i p  
- **ρ(x,t) = |φ|²** — density  
- **θ(x,t)** — phase  
- **v = θ_x** — hydrodynamic velocity  

## Parameters (CRFT, CP-NLSE, CE-NWE)
- **hbar** — reduced Planck constant  
- **m** — mass parameter  
- **g** — cubic nonlinearity  
- **lam** — 4th-order (k⁴) dispersion coefficient  
- **beta** — 6th-order (k⁶) dispersion coefficient  
- **rho0** — background density  
- **lambda_coh** — coherence-penalty coupling  
- **c** — sound speed  
- **xi** — healing length  
- **α, γ** — φ–χ coupling strengths  
- **lam_χ, beta_χ** — χ-field dispersion coefficients  

## Potentials & Energies
- **U(ρ)** — potential  
- **Up(ρ)** — derivative of U(ρ)  
- **L, L_coh** — Lagrangian density terms  
- **H(q,p)** — Hamiltonian in symplectic coordinates  
- **V_eff** — soliton interaction potential  

## Hydrodynamic Quantities
- **Q** — quantum pressure  
- **P(ρ)** — effective pressure  
- **c_eff** — effective sound speed  
- **A(U)** — hydrodynamic Jacobian matrix  
- **λ (characteristic)** — characteristic speeds  

## Coherence & Gradient Flow
- **C = (|φ|² − rho0)²** — coherence functional  
- **δC/δφ*** — variation under φ*  
- **∂τ φ = ...** — coherence gradient flow  
- **c(ρ)** — 1D coherence density (ρ_x² / (4ρ))  

## Geometric / Tensor Symbols
- **g_{μν}** — effective metric tensor  
- **T_{μν}** — stress–energy tensor  
- **R_{μν}** — Ricci tensor  
- **R** — Ricci scalar  
- **G_{μν}** — Einstein-like tensor  
- **κ** — backreaction coupling  

## Soliton & Vortex Parameters
- **A** — soliton amplitude  
- **w** — soliton width  
- **v** — soliton velocity  
- **x0** — soliton/vortex center  
- **depth** — dark soliton depth  
- **charge** — vortex winding number  
- **core_scale** — vortex core size  

## Turbulence & Spectral Diagnostics
- **mass = ∫|ψ|²** — conserved mass  
- **roughness** — ∫|ψ_x|² / ∫|ψ|²  
- **coherence energy** — ~||ψ_xx||²  
- **spectral centroid** — ∫k S(k)/∫S(k)  
- **S(k)** — structure factor  
- **p(k)** — normalized spectrum  
- **k_rms** — root-mean-square wavenumber  
- **ξ_k = 1/k_rms** — spectral coherence length  

## Coherence Metrics & Correlation Functions
- **g1(r)** — two-point correlation  
- **ξ = ∫|g1(r)|/|g1(0)| dr** — correlation length  
- **Var(ρ), Var(ψ)** — variances  
- **PCI = |<exp(iθ)>|** — phase coherence index  
- **SCI = Σ p_k²** — spectral coherence index  

## Classification & Stability Metrics
- **P** — phase order  
- **U** — uniformity  
- **C** — coherence functional measure  
- **ξ_corr, ξ_spec** — correlation & spectral coherence lengths  
- **corr_score, coh_score** — normalized coherence/regularity scores  
- **F** — fragmentation index  
- **conv_rate** — multisoliton convergence rate  

## Parameter Containers & Diagnostics
- **CRFTParams1D** — 1D parameter bundle  
- **CRFT_PARAMS_1D_SYMBOLIC** — symbolic parameter set  
- **relative_difference(a,b)** — invariant comparison metric  

---

# 1. CRFT Core Foundations

## 1.1 Canonical Symbols
(Already listed above—retained for structure)

Coordinates: x, t  
Fourier variables: k, omega  
Fields: φ(x,t), ρ = |φ|², θ  
Parameters: hbar, m, g, lam, beta, rho0, lambda_coh, c, xi  
Potentials: U(ρ), Up(ρ)

---

# 2. First-Order CRFT: CP-NLSE (Coherence-Penalized Nonlinear Schrödinger Equation)

## 2.1 CP-NLSE Lagrangian
L = − hbar ρ θ_t  
  − (hbar²/(2m)) ρ θ_x²  
  − lam (ρ_x)² / (4ρ)  
  + U(ρ)

## 2.2 CP-NLSE Equation of Motion
R₁[φ] =  
 i φ_t  
 + (1/2) φ_xx  
 − g |φ|² φ  
 + lam φ_xxxx  
 + beta φ_xxxxxx

## 2.3 CP-NLSE Dispersion
ω² = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶

## 2.4 Parameter Containers
CRFTParams1D(g, rho0, lam, beta, lambda_coh, hbar, m, c, xi)  
CRFT_PARAMS_1D_SYMBOLIC

---

# 3. Second-Order CRFT: CE-NWE (Coherence-Extended Nonlinear Wave Equation)

## 3.1 CE-NWE Equation
R₂[φ] =  
 φ_tt  
 + (1/4) φ_xxxx  
 − g rho0 φ_xx

## 3.2 CE-NWE Lagrangian
L = (1/2)|φ_t|² − (1/2)c²|φ_x|²  
  + (1/2)lam|φ_xx|² + (1/2)beta|φ_xxx|²  
  − (1/2)g(|φ|² − rho0)²

## 3.3 CE-NWE Dispersion
ω² = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶

---

# 4. Hydrodynamic Lift (Madelung Formulation)

## 4.1 Madelung Map
φ = sqrt(ρ) exp(i θ)  
v = θ_x

## 4.2 Hydrodynamic Equations
ρ_t + ∂x(ρ v) = 0  
θ_t + v θ_x + (1/ρ) ∂x P = 0

Quantum pressure:  
Q = −(1/(2ρ)) (∂xx sqrt ρ)/sqrt ρ

## 4.3 Hydrodynamic Pressure and Sound Speed
P(ρ) = (g/2) ρ² + lambda_coh(ρ − rho0)  
c_eff² = g rho0 + lambda_coh

---

# 5. Coherence Functionals and Variational Structures

## 5.1 Coherence Density
c(ρ) = (ρ_x)² / (4ρ)

## 5.2 Coherence Lagrangian Term
L_coh = lam (ρ_x)² / (4ρ)

## 5.3 Variational Contribution
δL/δρ − ∂x(δL/δρ_x)

Includes:  
− lam (ρ_x²)/(4ρ²)  
+ lam (ρ_xx)/(2ρ)  
+ rational terms

## 5.4 Coherence Functional and Variation
C = (|φ|² − rho0)²  
δC/δφ* = 2(|φ|² − rho0)φ

## 5.5 Coherence-Modified CP-NLSE and CE-NWE
R = R₀ + lambda_coh(|φ|² − rho0)φ  
R₂ = R₂₀ + lambda_coh(|φ|² − rho0)φ

---

# 6. Symplectic (q,p) Reformulation

φ = q + i p  
ρ = q² + p²

Hamiltonian:  
H(q,p) = (hbar²/(2m))(q_x² + p_x²) + lam/rho (q q_x + p p_x)² + U(ρ)

Gradient identity:  
|φ_x|² = q_x² + p_x²

---

# 7. Frozen-Core CRFT (Minimal CP-NLSE)

## 7.1 Frozen Lagrangian
L = −(hbar²/2m)|φ_x|² − hbar ρ θ_t + lam(ρ_x²)/(4ρ) + U(ρ)

## 7.2 Frozen EOM
i hbar φ_t + (hbar²/2m) φ_xx + Up(|φ|²) = 0

## 7.3 Frozen Continuity
ρ_t + ∂_x[(hbar/m) ρ θ_x] = 0

## 7.4 Frozen Dispersion and Healing Length
ω² = c² k² + (hbar²/(2m) + lam) k⁴  
xi² = (hbar²/(2m) + lam)/c²

## 7.5 Noether Current
J_t = −hbar ρ  
J_x = (hbar ρ/m) θ_x  

---

# 8. Multi-Dimensional CRFT

i φ_t = −½ ∇² φ + g|φ|² φ + lam ∇⁴ φ + beta ∇⁶ φ  
ω(k) = ½ k² + lam k⁴ + beta k⁶

---

# 9. Coupled CRFT (φ–χ System)

i φ_t = −½ φ_xx + g|φ|²φ + lam φ_xxxx + beta φ_xxxxxx + α χ φ  
χ_tt = −½ χ_xx − lam_χ χ_xxxx − beta_χ χ_xxxxxx − γ(|φ|² − rho0)

---

# 10. CRFT Geometry and Backreaction

## 10.1 Acoustic Metrics
1D: diag(−1/c², 1)  
2D: diag(−1/c², 1+rho0 x, 1+rho0 y)  
3D: diag(−1/c²+rho0 t, 1,1,1)

Curvature proxies:  
R₁D~1/(c²rho0), R₂D~rho0/c², R₃D~rho0/c³

---

## 10.2 Stress–Energy Tensor
T_00 = |φ|² + |φ_x|²  
T_tx = φ* φ_x  
T_xx = |φ_x|² + lam ρ_xx + beta ρ_xxxx

Backreacted metric:  
g_tt = −(1/c²)(1 + κ(ρ−rho0)/rho0)

Trace equation:  
trace(g) + κ trace(T) = 0

---

## 10.3 Einstein-Like Extensions
Ricci tensor  
Ricci scalar  
Einstein tensor:  
trace(G) = κ(ρ−rho0)/rho0

---

# 11. Solitons and Vortices in CRFT

## 11.1 Coherence Gradient Flow
∂τ φ = −lambda_coh(|φ|² − rho0) φ

## 11.2 Bright Soliton
φ = sqrt(rho0) + A exp(−(x−x0)²/(2w²)) exp(i v (x−x0))

## 11.3 Dark Soliton
ρ = rho0(1 − depth exp(−((x−x0)/w)²/2))

## 11.4 Vortex (2D)
Amplitude ~ tanh(r/core)  
Phase ~ exp(i charge θ)

## 11.5 Soliton Interaction Potential
V_eff = g(|φ|² − rho0) + lambda_coh(rho0 − |φ|²)

---

# 12. Turbulence and Coherence Maps

## 12.1 Turbulent CRFT Evolution
ψ_k ← ψ_k exp(−i k² dt/2) exp(−lambda_coh k⁴ dt)  
ψ ← ψ exp(−i(gρ + lam ρ² + beta ρ³)dt)

## 12.2 Turbulence Diagnostics
mass = ∫|ψ|²  
roughness = ∫|ψ_x|² / ∫|ψ|²  
spectral centroid  
coherence energy ≈ ||ψ_xx||²

## 12.3 Coherent Phenomenology
- roughness_ratio  
- mass_drift  
- invariant scans  
- monotonicity in λ_coh  
- regimes: turbulence, soliton, mixed, stabilized

---

# 13. Coherence Metrics (General ND)

ρ = |ψ|²  
Var(ρ), Var(ψ)  
e_grad = Σ|∂i ψ|²  
g1(r)  
ξ = ∫|g1(r)|/|g1(0)| dr  
ξ_k = 1/k_rms  
PCI = |<exp(iθ)>|  
SCI = Σ p_k²  
S(k) = |FFT(ρ−<ρ>)|²

---

# 14. Field Classification and Stability

- P  
- U  
- C  
- ξ_corr, ξ_spec  
- corr_score, coh_score  
- Regimes: plane-wave, patterned, partial, noise  
- Stability: C, P, U, F  
- Multisoliton convergence  
- Master stability diagram

---

# 15. Output Bundling

Includes bundling of:

- coherence drifts  
- soliton diagnostics  
- turbulence maps  
- stability diagrams  
- statistical summaries  

---

# END OF DOCUMENT
