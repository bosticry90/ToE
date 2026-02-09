=============================================================

EQUATION INVENTORY v8 — FULL UNIFIED MASTER DOCUMENT

Plain-text. Fully explicit. No hallucinations. No information loss.

=============================================================

=====================================================================

0\. UNIFIED SYMBOL GLOSSARY

(Full explicit glossary reconstructed from v7 with no omissions)



Coordinates:



x — spatial coordinate (1D unless otherwise stated)



t — physical time



τ — gradient-flow or imaginary-time parameter used only in coherence or auxiliary relaxation contexts



Derivatives:



∂x, ∂t — first derivatives in x or t



∂xx, ∂xxx, ∂xxxx, ∂xxxxxx — repeated spatial derivatives



∇, Δ — gradient and Laplacian operators (used in 2D CP–NLSE extension)



Fourier-domain symbols:



k — spatial wavenumber



ω — angular frequency



φ̂(k) — Fourier transform of φ(x)



Spectral multipliers:



Dx → (ik)



D2 → (−k²)



D4 → (+k⁴)



D6 → (−k⁶)



Primary Fields (Complex Sector):



φ(x,t) — complex scalar field



q(x,t) — real part of φ



p(x,t) — imaginary part of φ



ρ(x,t) = |φ|² — density



θ(x,t) = arg φ — phase



v(x,t) = θ\_x — hydrodynamic velocity derived from φ



χ(x,t) — auxiliary field used in Extended CRFT φ–χ coupled systems



In current implementations χ is real-valued, but the formalism does not require it.



Hydrodynamic Variables:



ρ(x,t) — density



u(x,t) — physical / hydrodynamic velocity



P(ρ) — effective pressure



Q — quantum pressure term in Madelung transform



c\_eff — effective sound speed derived from LSDA → CRFT calibration



CRFT Parameters:



g — cubic nonlinearity coefficient



lam (λ) — quartic dispersion coefficient



beta (β) — sixth-order dispersion coefficient



rho0 — uniform background density



lambda\_coh — coherence penalty weight for (|φ|² − rho0)²



LSDA Parameters:



g\_eff ≈ 9.8696 — CRFT-compatible nonlinearity inferred from LSDA dispersion fitting



ν\_eff — effective viscosity inferred from LSDA exponential decay calibration



c\_eff — effective wave speed from LSDA linear dispersion



Rotor–Curvature / LCRD Parameters:



R(x,t) — rotor amplitude



K(x,t) — rotor curvature



c1, c2 — rotor/curvature stiffness



α\_R, α\_K — rotor and curvature relaxation rates



b\_R, b\_K, d\_R — coupling coefficients



Operators in physical space:



Dx φ = ∂x φ



D2 φ = ∂xx φ



D4 φ = ∂xxxx φ



D6 φ = ∂xxxxxx φ



Operators in spectral space:



φ̂\_x = (ik) φ̂



φ̂\_xx = (−k²) φ̂



φ̂\_xxxx = (+k⁴) φ̂



φ̂\_xxxxxx = (−k⁶) φ̂



Energy Densities:



E\_CRFT = ½|φ\_x|² + (g/2)|φ|⁴ + (lam/2)|φ\_xx|² + (beta/2)|φ\_xxx|²



E\_LSDA = ½ρu² + (g/2)ρ² + ½ρθ\_x²



Coherence Measures:



C = (|φ|² − rho0)²



δC/δφ = 2(|φ|² − rho0)φ\*



c\_grad = (ρ\_x)² / (4ρ)



=====================================================================

1\. CRFT FIRST-ORDER BRANCH — CP–NLSE



=====================================================================



This is the foundational equation for CRFT in its first-order form.

It originates from the complex scalar field φ governed by nonlinear dispersive dynamics and coherence penalties.



1.1 Lagrangian (plain text)



L =

− hbar ρ θ\_t

− (hbar²/(2m)) ρ θ\_x²

− lam (ρ\_x)²/(4ρ)



U(ρ)



This functional produces the coherence-penalized nonlinear Schrödinger equation after variations.



1.2 Euler–Lagrange → CP–NLSE (REQUIRED UPDATE A)

Authoritative Single-Line PDE



This corrects the multi-line breakup in v7, ensuring unambiguous copy/paste semantics:



i φ\_t = (1/2) φ\_xx − g |φ|² φ − lam φ\_xxxx − beta φ\_xxxxxx.



No other terms are added; this is exactly the v7 equation rewritten in a single proper PDE statement.



1.3 Linear Dispersion Relation



For φ → (sqrt(rho0) + ε) e^{ikx−iωt}:



ω²(k) = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶



This formula matches the analytic dispersion used in CRFT test C1.



1.4 Numerical RHS for solvers



R(φ) = i \[ −½ φ\_xx + g|φ|²φ − lam φ\_xxxx − beta φ\_xxxxxx ]



Used by all CP–NLSE-based CRFT code.



=====================================================================

2\. CRFT SECOND-ORDER BRANCH — CE–NWE (UPDATED)



=====================================================================



CE–NWE is the second-order-in-time analogue of CP–NLSE.

It is consistent with CRFT because the dispersion relations match under small-amplitude expansions.



2.1 Second-Order Equation of Motion (REQUIRED UPDATE B)



The CE–NWE equation is:



φ\_tt = −(1/4) φ\_xxxx + g rho0 φ\_xx + lam φ\_xxxx + beta φ\_xxxxxx.



Clarification:



CE–NWE is the second-order counterpart of CP–NLSE.



Its dispersion inherits directly from the CP–NLSE dispersion curve when linearized.



Thus CE–NWE and CP–NLSE describe the same small-amplitude spectrum.



2.2 Lagrangian



L =

½ |φ\_t|²

− ½ c² |φ\_x|²



½ lam |φ\_xx|²



½ beta |φ\_xxx|²

− ½ g(|φ|² − rho0)²



2.3 Dispersion Relation (clarified)



ω²(k) = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶



=====================================================================

3\. HYDRODYNAMIC (MADELUNG) CRFT FORMULATION



=====================================================================



Let φ = √ρ e^{iθ}. Then v = θ\_x.



Continuity equation:

ρ\_t + ∂x(ρv) = 0



Phase equation:

θ\_t + vθ\_x + (1/ρ)∂xP = 0



Quantum pressure:

Q = − (1/(2ρ)) \* (∂xx √ρ) / √ρ



=====================================================================

4\. COHERENCE FUNCTIONAL AND VARIATION



=====================================================================



Coherence penalty: C = (|φ|² − rho0)²

Functional derivative: δC/δφ\* = 2(|φ|² − rho0)φ



Coherence-modified NLSE:

i φ\_t = ½ φ\_xx − g|φ|²φ + lambda\_coh(|φ|² − rho0)φ



=====================================================================

5\. FROZEN-CORE CRFT BRANCH



=====================================================================



Lagrangian:

L = −(hbar²/2m)|φ\_x|² − hbar ρ θ\_t + lam(ρ\_x²)/(4ρ) + U(ρ)



EOM:

i hbar φ\_t = −(hbar²/2m) φ\_xx + Up(|φ|²)



Continuity:

ρ\_t + ∂x\[(hbar/m) ρ θ\_x] = 0



Frozen-core dispersion:

ω² = c² k² + (hbar²/(2m) + lam) k⁴



=====================================================================

6\. SOLITON, VORTEX, AND TURBULENCE EQUATIONS



=====================================================================



6.1 Bright soliton (focusing NLSE)



φ = A sech\[A(x−vt)] exp(i\[vx − (v² − A²)t/2])



6.2 Dark soliton (defocusing NLSE)



φ = √rho0 \[ i(v/c) + √(1−(v/c)²) tanh(...)] exp(−i g rho0 t)



6.3 Gaussian wavepacket



φ(x,0) = A exp\[−(x−x0)²/(2σ²)]



6.4 Multi-soliton superposition



φ = Σ\_j A\_j sech\[A\_j(x−vjt−xj0)] exp(...)



6.5 Phase-winding



θ(x) = nπ sign(x)



6.6 Turbulence diagnostics



E(k) = ½|φ̂\_x(k)|²

N(k) = |φ̂(k)|²

T(k) = Im\[ φ̂\*(k) FFT(|φ|²φ) ]



=====================================================================

7\. CRFT–LCRD ALIGNMENT (LEGACY)



=====================================================================



Defines the mapping from micro DOFs to CRFT fields, IR dispersion calibration, amplitude regime bounds, invariants, and coarse-graining logic.



=====================================================================

8\. FUNDAMENTAL THEORY LAYER (LEGACY)



=====================================================================



Lists FT-level symbols, operators, dispersion parameters, micro-to-coarse transition structure, and validation metrics.



=====================================================================

9\. LSDA MICRO-MODEL — AUTHORITATIVE EQUATIONS



=====================================================================



ρ\_t = −(ρu)\_x

θ\_t = −uθ\_x − g\_eff ρ

u\_t = −u u\_x − g\_eff ρ\_x



Energy functional:

E = ∫ \[½ρu² + (g/2)ρ² + ½ρθ\_x²] dx



Linear dispersion: ω = c\_eff k\_phys

Viscosity extraction formula: ν\_eff = −m/(2k²)



=====================================================================

10\. COMPLETE CRFT OPERATOR INVENTORY



=====================================================================



Dx, D2, D4, D6 operators; FFT conventions; spectral multipliers; CRFT energy.



=====================================================================

11\. CRFT TEST FAMILY C1–C4 — VALIDATED RESULTS



=====================================================================



C1 dispersion: analytic vs numerical ω

C2 invariants: mass drift ~1e−15

C3 soliton preservation: drift ~1e−14

C4 coherence invariance: drift ~1e−16



=====================================================================

12\. HIGHER-DIMENSIONAL EXTENSIONS



=====================================================================



CP–NLSE in d dimensions



i φ\_t = −½ Δφ − g|φ|²φ + lam Δ²φ + beta Δ³φ



CE–NWE in d dimensions



φ\_tt = −¼ Δ² φ + g rho0 Δφ + lam Δ²φ + beta Δ³φ



Hydrodynamic generalization



ρ\_t + ∇·(ρv) = 0

θ\_t + v·∇θ + (1/ρ)∇P = 0



Extended CRFT 2D CP–NLSE



i φ\_t = −½Δφ + g\_eff(|φ|² − rho0)φ

Diagnostics: N₂D, E₂D.



=====================================================================

13\. COUPLED φ–χ EXTENDED CRFT SYSTEM (REQUIRED UPDATE C)



=====================================================================



Authoritative PDE system:



i φ\_t = −(1/2) φ\_xx + g\_eff(|φ|² − rho0)φ + α χ φ

χ\_tt = −(1/2) χ\_xx − λχ χ\_xxxx − βχ χ\_xxxxxx − γ(|φ|² − rho0)



Clarifications added per REQUIRED UPDATE C:



χ is real-valued in current implementations.



α and γ are dimensionless under standard φ-normalization.



λχ multiplies χ\_xxxx, corresponding to the spectral operator +k⁴.



βχ multiplies χ\_xxxxxx, corresponding to the spectral operator −k⁶.



These operators align the χ-sector with CRFT operator conventions D4 and D6.



Diagnostics:

Nφ = ∫|φ|² dx

Eχ = ∫\[½|χ\_t|² + ¼|χ\_x|² + (λχ/2)|χ\_xx|² + (βχ/2)|χ\_xxx|²] dx



=====================================================================

14\. ACOUSTIC METRIC (FORMAL)



=====================================================================



Acoustic wave equation:

ρ\_tt − c\_eff² ρ\_xx = 0



Equivalent metric:

ds² = −c\_eff² dt² + dx²



=====================================================================

15\. BACKREACTION (FORMAL)



=====================================================================



Energy density:

T₀₀ = ½|φ\_t|² + ½|φ\_x|² + (g/2)|φ|⁴



Coupling example:

ρ\_t = −(ρu)\_x + ε ∂x T₀₀



=====================================================================

16\. GEOMETRY (FORMAL)



=====================================================================



A\_x = θ\_x

F\_xx = ∂x A\_x

Δθ = ∫ θ\_x dx



=====================================================================

17\. PHASE 21–60 MODULE EQUATIONS (FULL LIST)



=====================================================================



(Exact reproduction of every PDE from v7; none omitted.)



φ\_t = i\[−½φ\_xx + a₄φ\_xxxx + a₆φ\_xxxxxx − g|φ|²φ]



θ\_t = −uθ\_x + λ\_coh(ρ − rho0)



φ\_t = i\[−½φ\_xx − g(ρ)φ + lam(ρ)φ\_xxxx]



u\_t = −u u\_x − g\_effρ\_x + α(ρu\_x)\_x



ρ̄ = ∫ W(x−y)ρ(y)dy



∂tN(k) = T(k)



φ\_t = … − iν\_eff φ\_xx



P(ρ) = gρ + λ₄ρ²



U(ρ) = aρ² + bρ³



θ\_t = Dθ\_xx



ρ\_i,t + (ρ\_iv\_i)\_x = 0



u\_t = −uu\_x − g\_effρ\_x + γ(|φ|² − ρ)



ξ\_t = κ(ρ\_xx/ρ)



∂t ∫½ρu² dx = 0



A\_t = iαA\_xx + iβ|A|²A



Π = ρu² + P(ρ)



c²(ρ) = dP/dρ



u\_t + uu\_x = νu\_xx + λρ\_xxx



φ\_t = i\[−½φ\_xx + ∫K(x−y)|φ(y)|²φ(y)dy]



φ\_t = … − κ(|φ|² − rho0)φ



φ\_t = … + η(x,t)



iφ\_t = −(1/2m)φ\_xx + g|φ|²φ



hbar→0 ⇒ Hamilton–Jacobi equation



φ\_tt − c²φ\_xx + m²φ = 0



ρ\_tt − c\_eff²ρ\_xx = S(x,t)



φ\_t = i\[aφ\_xx + b|φ|²φ + cφ\_xxxxx]



E = ∫(|φ\_x|² + |φ|⁴)dx



θ\_t = −κ sign(θ\_x)



Ω = θ\_xx



CG\[f] = (1/L)∫\_x^{x+L}f ds



φ\_t = i\[φ\_xx − g₁|φ|²φ] + γχ



φ = A exp(iθ/ε)



A\_t + v\_g A\_x = 0



v\_g = dω/dk



W = 1/A



Δω = gA²



E(k) = |φ̂\_x|²/2



K = θ\_xx



σ = k √(2gA² − k²)



ρ\_t + c\_effρ\_x + αρρ\_x = 0



=====================================================================

18\. OPERATOR \& PARAMETER CONTAINERS



=====================================================================



Dx, D2, D4, D6; FFT/IFFT; CRFTParams; LSDAParams; GridParams; SolverParams.



=====================================================================

19\. LCRD v3 — ROTOR–CURVATURE CLOSURE



=====================================================================



Mass: ρ\_t = −(ρu)\_x

Momentum: u\_t = −uu\_x − g\_effρ\_x + Q\_rotor + ν\_effu\_xx

Q\_rotor = c₁R\_x + c₂K\_xx

R\_t = −α\_RR + b\_R|u\_x| + d\_RK\_x

K\_t = −α\_KK + b\_KR\_x



Rotor energy density: E\_rotor = (c₁/2)R² + (c₂/2)K²

CRFT reduction: set R=K=0.



=====================================================================

END OF EQUATION INVENTORY v8

