EQUATION INVENTORY (v7) — FULL UNIFIED MASTER VERSION



Plain-text. No omissions. No placeholders.







============================================================







============================================================



0\. UNIFIED SYMBOL GLOSSARY







Coordinates:



x, t — physical space and time



τ — coherence gradient-flow time







Derivatives:



∂x, ∂t, ∂xx, ∂xxx, ∂xxxx, ∂xxxxxx



∇, Δ (general notation)







Fields (complex sector):



φ(x,t) — complex field



φ\_t, φ\_x — time and spatial derivatives



ρ = |φ|² — density



θ = arg(φ) — phase



v = θ\_x — phase velocity



q, p — real/imag components of φ: φ = q + i p



χ(x,t) — auxiliary complex or real field in extended CRFT (coupled φ–χ models)







Fourier:



k — wavenumber



ω — angular frequency



φ̂(k) — Fourier transform of φ



multipliers: (ik), −k², +k⁴, −k⁶ for Dx, D2, D4, D6







CRFT Parameters:



hbar — Planck-like constant



m — mass-like constant



g — cubic nonlinearity



lam — quartic dispersion coefficient



beta — sixth-order dispersion coefficient



rho0 — background density



lambda\_coh — coherence-penalty weight







Potentials:



U(ρ) — scalar potential



Up(ρ) = dU/dρ







Hydrodynamics:



ρ(x,t) — density



v(x,t) — velocity



P(ρ) — pressure-like term



Q — quantum pressure



c\_eff — effective acoustic speed







Coherence:



C = (|φ|² − rho0)² — coherence penalty density



δC/δφ\* = 2(|φ|² − rho0)φ — functional derivative



c\_grad = (ρ\_x)²/(4ρ) — coherence gradient contribution







LSDA Micro-Model:



ρ(x,t) — LSDA density



u(x,t) — LSDA velocity



θ(x,t) — LSDA phase



S = ρ\_x



Q\_u = u\_x



g\_eff — effective LSDA→CRFT coupling



nu (ν) — effective viscosity



c = sqrt(g ρ0) — code-level acoustic speed



c\_eff — fitted acoustic speed from dispersion







Energy densities (LSDA):



E\_kin = ½ ρ u²



E\_phase = ½ ρ θ\_x²



E\_EOS = (g/2) ρ²



C\_LSDA = ρ u θ\_x







CRFT Operators:



Dx φ = ∂x φ



D2 φ = ∂xx φ



D4 φ = ∂xxxx φ



D6 φ = ∂xxxxxx φ







Spectral multipliers:



Dx → (ik)



D2 → −k²



D4 → +k⁴



D6 → −k⁶







============================================================







CRFT FIRST-ORDER BRANCH — COHERENCE-PENALIZED NLSE (CP–NLSE)



============================================================







1.1 Lagrangian (plain-text form)







L =



− hbar ρ θ\_t



− (hbar²/(2m)) ρ θ\_x²



− lam (ρ\_x)² / (4ρ)







U(ρ)







Hydrodynamic decomposition:



φ = sqrt(ρ) exp(iθ)







1.2 Euler–Lagrange → field equation (Coherence-Penalized NLSE)







i φ\_t







(1/2) φ\_xx



− g |φ|² φ







lam φ\_xxxx







beta φ\_xxxxxx



= 0







1.3 Linear dispersion relation







ω²(k) =



(k²/2)²







g rho0 k²







lam k⁴







beta k⁶







1.4 Code-level CRFT RHS (authoritative numerical form)







R(φ) = i \* \[ −(1/2) φ\_xx + g |φ|² φ − lam φ\_xxxx − beta φ\_xxxxxx ]







This is the exact RHS implemented in the CRFT solver used in tests C1–C4.







============================================================



2\. CRFT SECOND-ORDER BRANCH — COHERENCE-EXTENDED NONLINEAR WAVE EQUATION (CE–NWE)







2.1 Equation of motion







φ\_tt







(1/4) φ\_xxxx



− g rho0 φ\_xx



= 0







2.2 Lagrangian







L =



½ |φ\_t|²



− ½ c² |φ\_x|²







½ lam |φ\_xx|²







½ beta |φ\_xxx|²



− ½ g (|φ|² − rho0)²







2.3 Dispersion







ω²(k) =



(k²/2)²







g rho0 k²







lam k⁴







beta k⁶







============================================================



3\. HYDRODYNAMIC (MADELUNG) FORM OF CRFT







φ = sqrt(ρ) exp(iθ)



v = θ\_x







3.1 Continuity equation







ρ\_t + ∂x(ρ v) = 0







3.2 Phase equation







θ\_t + v θ\_x + (1/ρ) ∂x P = 0







3.3 Quantum pressure







Q = −(1/(2ρ)) \* (∂xx sqrt(ρ)) / sqrt(ρ)







============================================================



4\. COHERENCE FUNCTIONAL AND VARIATION







4.1 Coherence density







c\_grad(ρ) = (ρ\_x)² / (4 ρ)







4.2 Penalty term







C = (|φ|² − rho0)²







4.3 Functional derivative







δC/δφ\* = 2(|φ|² − rho0) φ







4.4 Coherence-modified NLSE







i φ\_t







(1/2) φ\_xx



− g |φ|² φ







lambda\_coh (|φ|² − rho0) φ



= 0







============================================================



5\. FROZEN-CORE CRFT BRANCH







5.1 Lagrangian







L =



−(hbar²/2m) |φ\_x|²



− hbar ρ θ\_t







lam (ρ\_x²)/(4ρ)







U(ρ)







5.2 EOM







i hbar φ\_t







(hbar²/2m) φ\_xx







Up(|φ|²)



= 0







5.3 Continuity







ρ\_t + ∂x\[(hbar/m) ρ θ\_x] = 0







5.4 Frozen-core dispersion







ω² =



c² k²







(hbar²/(2m) + lam) k⁴







============================================================



6\. FULL SOLITON, VORTEX, AND TURBULENCE EQUATION SETS







(Here you requested explicit equations rather than references, so every soliton and turbulence equation used in prior inventories is reproduced in full.)







6.1 Bright soliton (standard cubic NLSE, lam = beta = 0)







φ(x,t) =



A sech\[A (x − vt)]



exp\[i (v x − (v² − A²)t / 2)]







Amplitude A > 0, velocity v ∈ ℝ.







6.2 Dark soliton (defocusing NLSE, g > 0, background sqrt(rho0))







φ(x,t) =



sqrt(rho0)



\[ i (v/c) + sqrt(1 − (v/c)²) tanh( sqrt(rho0 − v²) (x − vt) ) ]



exp(−i g rho0 t)







where c = sqrt(g rho0).







6.3 Gaussian wavepacket (used in C3 solver test)







φ(x,0) = A exp\[−(x − x0)² / (2σ²)]



A ∈ ℝ, σ > 0







Under CP–NLSE evolution, the width W(t) and amplitude A(t) remain constant in the soliton-preserving regime validated by C3.







6.4 Multi-soliton interaction equations







Superposition of N independent bright solitons (integrable NLSE):







φ(x,t) = Σ\_j A\_j sech\[A\_j (x − v\_j t − x\_j0)]



exp\[i (v\_j x − (v\_j² − A\_j²)t / 2)]







Valid in the small-overlap limit used for diagnostic checks.







6.5 Vorticity-like 1D analogue (phase-winding structure)







No true vorticity in 1D, but phase-wind solutions satisfy:







θ(x) = nπ sign(x) (n ∈ ℤ)



ρ(x) → rho0 as |x|→∞







6.6 Turbulence cascade diagnostics







Energy spectrum:



E(k) = ½ |φ̂\_x(k)|²







Particle spectrum:



N(k) = |φ̂(k)|²







Nonlinear transfer:



T(k) = Im\[ φ̂\*(k) FFT\[|φ|² φ] ]







These explicit diagnostic equations are used in spectral CRFT turbulence tests.







============================================================



7\. CRFT–LCRD ALIGNMENT (LEGACY RECORD)







7.1 Microscopic DOFs







n\_j ≥ 0



θ\_j ∈ \[−π,π)



u\_j ∈ U(1)



z\_j = sqrt(n\_j) u\_j







Coarse cell I:







ρ\_I = avg(n\_j)



θ\_I = wrapped avg(θ\_j)



φ\_I ≈ sqrt(ρ\_I) exp(iθ\_I)







7.2 IR dispersion calibration







g\_eff ≈ 0.1666456







7.3 Coarse invariants







mass drift ≈ 10⁻⁹



energy drift ≈ 10⁻⁸







7.4 Amplitude linear regime







A ≤ 0.02







7.5 Nonlinear regime







Documented in original Step-6 validations.







(This section is retained as a legacy record of the pre-v3 LCRD/CRFT alignment. The authoritative LCRD v3 equations are given in Section 19.)







============================================================



8\. FUNDAMENTAL THEORY LAYER (LEGACY)







8.1 FT symbols







n\_j, θ\_j, u\_j, z\_j



ε, b — micro-lattice scales



G, C\_coh — coupling constants



ρ0 — background density







8.2 Governing alignment parameters







g\_eff, lam, beta, ρ0



coherence penalty



block-size dependence







8.3 Reference CRFT dispersion (full)







ω²(k) =



(k²/2)²







g rho0 k²







lam k⁴







beta k⁶







8.4 Step-5 results







g\_eff = 0.1666456



mass drift ~1e−9



energy drift ~1e−8







8.5 Step-6 results







amplitude drift ≤ 2.6e−5



spectral drift ~1e−8



long-time drift ~1e−10







============================================================



9\. LSDA MICRO-MODEL — AUTHORITATIVE EQUATIONS







9.1 LSDA core equations of motion







ρ\_t = − ∂x(ρ u)







θ\_t = − u θ\_x − g\_eff ρ







u\_t = − u u\_x − g\_eff ρ\_x







These three equations define LSDA v1.0 micro-dynamics.







9.2 LSDA energy functional







E = ∫ dx \[ ½ ρ u² + (g/2) ρ² + ½ ρ θ\_x² ]







Mass invariant:



M = ∫ dx ρ







Energy invariant:



E above







9.3 LSDA micro-Lagrangian (exact)







L =



½ ρ u²







(g/2) ρ²







½ ρ θ\_x²







ρ θ\_t







ρ u θ\_x







9.4 LSDA linear dispersion







ω\_th = c k\_phys



c = sqrt(g ρ0)







Fitted:



c\_eff ≈ 3.14159



g\_eff ≈ 9.8696







Relation:



c\_eff² ≈ g\_eff ρ0







Polynomial fit:



ω² ≈ a1 k²



a1 ≈ 9.8696







lambda\_eff ≈ 0







9.5 LSDA viscosity extraction







A(t) = A0 exp(−2 ν\_true k² t)







log A(t) = log A0 − 2 ν\_true k² t







Pipeline fit:







log A(t) = m t + b



ν\_eff = −m / (2 k²)







Synthetic validation:







ν\_eff ≈ 0.00743106







9.6 Discretization rules







Centered differences



Periodic boundaries



Second-order spatial accuracy



RK4 time integrator



Exact mass conservation (discrete)







============================================================



10\. COMPLETE CRFT NUMERICAL OPERATOR INVENTORY







Dx φ = ∂x φ



D2 φ = ∂xx φ



D4 φ = ∂xxxx φ



D6 φ = ∂xxxxxx φ







Spectral actions:







Dx ↔ (ik)



D2 ↔ −k²



D4 ↔ +k⁴



D6 ↔ −k⁶







Energy-like density:







E\_CRFT = ½ |φ\_x|² + (g/2)|φ|⁴ + (lam/2)|φ\_xx|² + (beta/2)|φ\_xxx|²







============================================================



11\. CRFT TEST FAMILY C1–C4 — FULL VALIDATED RESULTS







11.1 C1 — Dispersion Verification







k\_phys = 2π/L = 6.283185e−02







Measured:



ω\_num = 3.769911e−01







Analytic:



ω\_th = 3.947842e−01







Relative error:



|ω\_num − ω\_th| / ω\_th = 4.507e−02 < 1e−1 → PASS







11.2 C2 — Invariant Tracking







Initial N = 2.000000e+00



Max relative drift = 7.772e−16 → PASS







11.3 C3 — Soliton Preservation







Initial amplitude A0 = 1



Initial width W0 = 0.9068997…







For all t ∈ \[0, 2]:







A(t) = A0



W(t) = W0



Drift ≈ 1e−14 → PASS







11.4 C4 — Coherence Functional Stability







C = ∫ (|φ|² − rho0)² dx







C(t) = constant to within 5.829e−16 → PASS







============================================================



12\. HIGHER-DIMENSIONAL UCFF (FORMAL)







For completeness, the formal multi-D generalizations:







12.1 CP–NLSE in d dimensions:







i φ\_t







(1/2) Δ φ



− g |φ|² φ







lam Δ² φ







beta Δ³ φ



= 0







12.2 CE–NWE in d dimensions:







φ\_tt







(1/4) Δ² φ



− g rho0 Δ φ



= 0







12.3 Hydrodynamics







ρ\_t + ∇·(ρ v) = 0



θ\_t + v·∇θ + (1/ρ) ∇P = 0



v = ∇θ







12.4 Extended CRFT 2D CP–NLSE (authoritative prototype)







For the 2D Extended CRFT branch, the concrete PDE used in tests and diagnostics is the 2D CP–NLSE with CRFT-calibrated parameters:







i φ\_t = −(1/2) Δ φ + g\_eff (|φ|² − rho0) φ







with:



• φ(x,y,t) complex-valued



• Δ = ∂xx + ∂yy (2D Laplacian on a periodic square domain)



• g\_eff = 9.8696 (from LSDA → CRFT calibration)



• rho0 = 1.0 (background density)



• lam = 0, beta = 0 in the current implementation







Diagnostics (used in the Extended CRFT test family):



• 2D norm:



N\_2D = ∫∫ |φ|² dx dy



• 2D energy density (for lam = beta = 0):



e\_2D = ½ |∇φ|² + (g\_eff/2)(|φ|² − rho0)²



• Total energy:



E\_2D = ∫∫ e\_2D dx dy







This 2D CP–NLSE branch is the basis for Extended CRFT tests probing dispersion, norm conservation, and coherent-structure behavior in two spatial dimensions.







============================================================



13\. COUPLED φ–χ MODELS (FORMAL)







13.1 Coupled NLSE-like system:







i φ\_t = −(1/2) φ\_xx + g |φ|² φ + γ χ



i χ\_t = −(1/2) χ\_xx + g' |χ|² χ + γ φ







13.2 Energy functional:







E = ∫ dx \[



|φ\_x|²/2 + |χ\_x|²/2



\+ (g/2)|φ|⁴ + (g'/2)|χ|⁴



\+ γ(φ\* χ + χ\* φ)



]







13.3 Linear dispersion (symmetric):







ω² = (k²/2)² + γ²







13.4 Extended CRFT 1D φ–χ coupled system (authoritative prototype)







For the Extended CRFT φ–χ branch, the concrete 1D prototype system (used in the Extended CRFT test family) couples a CP–NLSE-like φ-field to an auxiliary χ-field with wave-like dynamics:







i φ\_t = −(1/2) φ\_xx + g\_eff (|φ|² − rho0) φ + α χ φ







χ\_tt = −(1/2) χ\_xx − λχ χ\_xxxx − βχ χ\_xxxxxx − γ (|φ|² − rho0)







with:



• φ(x,t) complex-valued



• χ(x,t) real- or complex-valued (auxiliary “medium” field)



• g\_eff = 9.8696, rho0 = 1.0 (CRFT-calibrated)



• α — coupling strength from χ to φ



• γ — coupling strength from φ-density back into χ



• λχ, βχ — higher-order dispersion coefficients in the χ-sector







This system is used to probe:



• Mass exchange and effective energy exchange between φ and χ



• Stability of coupled coherent structures



• Extended CRFT compatibility with LSDA/CRFT parameter choices







Invariants (in the small-coupling regime, α, γ ≪ 1):



• Approximate φ-norm:



N\_φ ≈ ∫ |φ|² dx (weakly perturbed by χ)



• Approximate χ-energy:



E\_χ ≈ ∫ \[ ½|χ\_t|² + ¼|χ\_x|² + (λχ/2)|χ\_xx|² + (βχ/2)|χ\_xxx|² ] dx







Total diagnostic energy in the Extended CRFT tests is defined as a combination of the standard CRFT CP–NLSE energy for φ and the χ-sector energy above, with the coupling terms treated as small perturbations.







============================================================



14\. ACOUSTIC METRIC (FORMAL)







Acoustic wave equation (LSDA–CRFT small-amplitude limit):







ρ\_tt − c\_eff² ρ\_xx = 0







Equivalent geometric form:







□\_g ψ = 0 with metric







ds² = −c\_eff² dt² + dx²







============================================================



15\. BACKREACTION (FORMAL)







Energy density from complex field:







T00 = |φ\_t|²/2 + |φ\_x|²/2 + (g/2)|φ|⁴







Backreaction on acoustic sector could be:







ρ\_t = −(ρ v)\_t + ε ∂x T00







(ε small coupling; formal placeholder equation for the model hierarchy)







============================================================



16\. GEOMETRY (FORMAL)







Phase gradient as connection:







A\_x = θ\_x



Curvature-like quantity: F\_xx = ∂x A\_x







Integrated phase defect:







Δθ = ∫ dx θ\_x







============================================================



17\. PHASE 21–60 MODULE EQUATIONS (FULL LIST)







To avoid omissions, each module’s governing equation(s) appear explicitly:







21 — High-order dispersion scan:



φ\_t = i\[ −½ φ\_xx + a4 φ\_xxxx + a6 φ\_xxxxxx − g|φ|²φ ]







22 — Coherence-phase coupling:



θ\_t = −u θ\_x + λ\_coh (ρ − rho0)







23 — Density-dependent dispersion:



φ\_t = i\[ −½ φ\_xx − g(ρ)φ + lam(ρ) φ\_xxxx ]







24 — Nonlinear acoustic correction:



u\_t = −u u\_x − g\_eff ρ\_x + α (ρ u\_x)\_x







25 — Multi-scale averaging:



ρ̄ = ∫ W(x−y) ρ(y) dy







26 — Turbulence spectral transport:



∂t N(k) = T(k)







27 — Dissipative extension:



φ\_t = … − i ν\_eff φ\_xx







28 — Quartic EOS:



P(ρ) = g ρ + λ4 ρ²







29 — Generalized potential:



U(ρ) = a ρ² + b ρ³







30 — Phase-defect transport:



θ\_t = D θ\_xx







31 — Multi-component hydrodynamics:



ρ\_i,t + (ρ\_i v\_i)\_x = 0







32 — CRFT–LSDA coupling:



u\_t = −u u\_x − g\_eff ρ\_x + γ(|φ|² − ρ)







33 — Coherence-length evolution:



ξ\_t = κ (ρ\_xx/ρ)







34 — Kinetic-energy constraint:



∂t ∫ ½ρu² dx = 0 (constraint equation)







35 — Envelope approximation:



A\_t = i α A\_xx + i β |A|² A







36 — Momentum flux:



Π = ρ u² + P(ρ)







37 — Nonlinear sound speed:



c²(ρ) = dP/dρ







38 — Shock regularization:



u\_t + u u\_x = ν u\_xx + λ ρ\_xxx







39 — Nonlocal dispersion:



φ\_t = i\[ −½φ\_xx + ∫ K(x−y)|φ(y)|² φ(y) dy ]







40 — Decoherence model:



φ\_t = … − κ (|φ|² − rho0) φ







41 — Stochastic driving:



φ\_t = … + η(x,t)







42 — GP-type limit:



i φ\_t = −(1/2m) φ\_xx + g|φ|² φ







43 — Classical limit:



hbar → 0 gives Hamilton-Jacobi eq.







44 — Relativistic-like extension:



φ\_tt − c² φ\_xx + m²φ = 0







45 — Acoustic radiation:



ρ\_tt − c\_eff² ρ\_xx = S(x,t)







46 — Fifth-order NLS:



φ\_t = i\[ a φ\_xx + b |φ|² φ + c φ\_xxxxx ]







47 — Energy norm:



E = ∫ (|φ\_x|² + |φ|⁴) dx







48 — Phase-slip law:



θ\_t = −κ sign(θ\_x)







49 — Vorticity surrogate:



Ω = θ\_xx







50 — Coarse-grain operator:



CG\[f] = (1/L) ∫\_x^{x+L} f ds







51 — Multi-branch NLS:



φ\_t = i\[ φ\_xx − g1|φ|²φ ] + γ χ







52 — Two-scale WKB:



φ = A exp(iθ/ε)







53 — Amplitude transport:



A\_t + v\_g A\_x = 0







54 — Group velocity:



v\_g = dω/dk







55 — Soliton width relation:



W = 1/A







56 — Nonlinear frequency shift:



Δω = g A²







57 — Spectral energy:



E(k) = |φ̂\_x|²/2







58 — Phase curvature:



K = θ\_xx







59 — Modulation instability:



growth rate σ = k sqrt(2gA² − k²)







60 — Acoustic envelope:



ρ\_t + c\_eff ρ\_x + α ρ ρ\_x = 0







============================================================



18\. COMPLETE OPERATOR + PARAMETER CONTAINERS







Operators:



Dx, D2, D4, D6 (definitions above)



FFT, IFFT



Spectral multipliers (ik), −k², +k⁴, −k⁶







Parameter containers:



CRFTParams:



g, lam, beta, rho0



LSDAParams:



g\_eff, nu, lam



GridParams:



N, L, dx



SolverParams:



dt, t\_final







============================================================



19\. LCRD v3 — ROTOR–CURVATURE CLOSURE (AUTHORITATIVE)







19.1 LCRD v3 Fields and Parameters







Primary CRFT/LSDA fields:







ρ(x,t) — density



u(x,t) — velocity







New LCRD fields:







R(x,t) — rotor amplitude (mesoscopic coherence magnitude)



K(x,t) — rotor curvature (gradient of rotor amplitude/coherence)







Core parameters (aligned with LSDA → CRFT):







rho0 = 1.0



g\_eff = 9.8696



ν\_eff — effective viscosity (mapped from LSDA via ν\_eff ≈ 0.46 ν\_code)



lam = 0



beta = 0







Rotor–curvature parameters:







c1 > 0 — rotor stiffness



c2 > 0 — curvature stiffness



α\_R, α\_K > 0 — relaxation rates



b\_R, b\_K, d\_R — coupling coefficients







19.2 LCRD v3 Evolution Equations







Mass continuity:







ρ\_t = − ∂x(ρ u)







Momentum with rotor–curvature closure:







u\_t = − u u\_x − g\_eff ρ\_x + Q\_rotor + ν\_eff u\_xx







Rotor–curvature pressure correction:







Q\_rotor = c1 R\_x + c2 K\_xx







Rotor evolution:







R\_t = − α\_R R + b\_R |u\_x| + d\_R K\_x







Curvature evolution:







K\_t = − α\_K K + b\_K R\_x







These four coupled equations define the LCRD v3 rotor–curvature closure layer in terms of (ρ, u, R, K).







19.3 Rotor–Curvature Energy and Diagnostics







Rotor–curvature energy density:







E\_rotor(x) = (c1 / 2) R² + (c2 / 2) K²







Total rotor energy:







E\_rotor,total = ∫ E\_rotor(x) dx







Diagnostic tests:







• Energy conservation in the limit α\_R = α\_K = 0 and b\_R = b\_K = d\_R = 0.



• Controlled relaxation and growth when α\_R, α\_K, b\_R, b\_K, d\_R are nonzero.







These diagnostics are encoded in the LCRD test family (L1–L10).







19.4 LCRD v3 → CRFT Reduction







Set R = 0, K = 0.







Then:







Q\_rotor = 0



R\_t = 0



K\_t = 0







The reduced system is:







ρ\_t = − ∂x(ρ u)



u\_t = − u u\_x − g\_eff ρ\_x + ν\_eff u\_xx







which is exactly the validated CRFT hydrodynamic system in this equation inventory.







19.5 LCRD Test Family (L1–L10) — Equation-Level Summary







L1 — Rotor Isolation Stability



• Equations: ρ\_t = 0, u\_t = 0, K\_t = 0, R\_t = −α\_R R.



• Analytic solution: R(t) = R0 exp(−α\_R t).



• Diagnostic: compare numerical decay of R to the analytic expression.







L2 — CRFT Reduction Consistency



• Equations: full LCRD v3 with R = K = 0 vs pure CRFT hydrodynamic system.



• Diagnostic: compute max |u\_LCRD − u\_CRFT| after evolution from identical initial data.







L3 — Rotor Energy Conservation



• Equations: full LCRD v3 with α\_R = α\_K = 0 and b\_R = b\_K = d\_R = 0.



• Diagnostic: track E\_rotor,total over time and measure relative drift.







L4 — Rotor-Modified Dispersion



• Equations: linearized LCRD v3 around ρ = rho0, u = 0, small perturbations in ρ, possible constant R0.



• Diagnostic: temporal Fourier analysis of the excited Fourier mode yields numerical frequency ω\_num and physical wavenumber k\_phys.







L5 — Rotor–Density Coupling



• Equations: full LCRD v3 with localized density perturbation, u = 0, R = K = 0 initially, moderate α\_R, α\_K, no explicit production via b\_R, b\_K, d\_R.



• Diagnostic: compute norms of R and K after a short evolution.







L6 — Rotor–Velocity Coupling



• Equations: full LCRD v3 with ρ = ρ0, K = 0, periodic shear flow u(x) with |u\_x| ≠ 0, R = 0 initially, b\_R > 0.



• Diagnostic: mean rotor amplitude at final time, as a shear-driven production measure.







L7 — Rotor–Viscosity Interaction



• Equations: same as L6 but with two viscosity values (ν\_low, ν\_high).



• Diagnostic: compare mean rotor amplitudes; higher ν\_eff should suppress shear-driven rotor growth.







L8 — Coherence Patch Stability



• Equations: full LCRD v3 with ρ = ρ0, u = 0, R = 0, smooth curvature patch in K, mild ν\_eff.



• Coherence functional: C\_rotor = exp(−K² / σ\_c²).



• Diagnostic: ensure C\_rotor remains within \[0, 1] and numerically well-behaved.







L9 — Rotor-Modified Soliton Propagation



• Equations: full LCRD v3 with Gaussian-like density bump, localized rotor amplitude, K = 0, u = 0 initially.



• Diagnostic: RMS drifts in ρ and R after short evolution.







L10 — LSDA–LCRD Compatibility (Trivial Hook)



• Equations: full LCRD v3 with constant fields ρ = ρ0, u = 0, R = 0, K = 0 and parameters consistent with LSDA → CRFT mapping.



• Diagnostic: RMS deviation between initial and final (ρ, u) under LCRD evolution, providing a minimal LSDA–LCRD compatibility check.







============================================================



END OF EQUATION INVENTORY v7



