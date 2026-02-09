STATE OF THE THEORY (v6)



Local Sound-Density Approximation (LSDA)

CRFT-Limit Micro-Model • Full Core + Extended Validation (T1–T10) Complete

All text plain-language, audit-ready, and aligned with validated code.



This document defines the authoritative structure, equations, assumptions, and validation path for LSDA v1.0 as the micro-model that cleanly reproduces CRFT in the long-wavelength and weak-contrast limits.



All content incorporates the fully validated LSDA Core Suite (T1–T4) and the implemented extended LSDA suite (T5–T10).



Core tests: T1, T2, T3, T3b, T4

Extended tests: T5, T6, T7, T7 v2 (synthetic ν pipeline), T8, T9, T10



These tests feed into parameter-identification and CRFT-reduction work (Steps 14–15), which now have concrete numerical inputs but remain analytically incomplete.



PURPOSE OF LSDA REBUILD



LSDA replaces legacy LCRD machinery with a minimal, auditable micro-fluid system featuring:



minimal fields



explicit micro-algebra



exact mass conservation



low-order dynamics



CRFT-limit correctness



correct nonlinear behavior



GPU-ready architecture



Steps 1–13 and tests T1–T10 validate this architecture.



CRFT CONTINUUM TARGET



CRFT equations of motion:



ρₜ = −∂ₓ(ρ u)

θₜ = −u θₓ − g\_eff ρ

uₜ = −(½u²)ₓ − (g\_eff ρ)ₓ



CRFT parameters during LSDA validation:



rho0 = 1.0

g\_eff = nominal CRFT acoustic coupling

lam = 0

beta = 0



LSDA must reproduce these in the coarse-grained weak-contrast limit.



MICRO-FIELDS (LSDA PRIMITIVES)



ρ ≡ s

θ ≡ α

u ≡ v



Derived:



S = ρₓ

Q = uₓ



Energy components:



E\_kin = ½ρ u²

E\_phase = ½ρ θₓ²

E\_EOS = (g\_eff/2) ρ²

C = ρ u θₓ



LSDA MICRO-DYNAMICS (LOCKED)



ρₜ = −∂ₓ(ρ u)

θₜ = −u θₓ − g\_eff ρ

uₜ = −u uₓ − g\_eff ρₓ



These match the Euler–Lagrange equations from the micro-Lagrangian exactly.

No additional terms are included until Step-14/15 or explicit ν, λ experiments.



DISCRETIZATION RULES



uniform grid



periodic BCs



centered differences



exact discrete mass conservation



second-order spatial accuracy



RK4 or symplectic timestepping



STABILITY AND INVARIANT REGIME



Weak-gradient constraints:



|ρₓ| ≪ ρ/L

|uₓ| ≪ u/L



Energy functional:



E = ∫ dx \[½ρu² + (g/2)ρ² + ½ρθₓ²]



Within T1–T4 and safe portions of T5–T10, mass is conserved to roundoff and energy remains bounded.

Large ν, λ or large-amplitude cases outside this envelope are marked explicitly as “unsafe.”



COARSE-GRAINING AND CRFT RECOVERY



ρ\_c = CG(ρ)

u\_c = CG(u)

j\_c = CG(ρu)



CRFT recovery requires continuity mapping, weak-gradient suppression of higher-order terms, and dispersion matching, all validated numerically in T1–T4 and T10.



MICRO-LAGRANGIAN (LSDA)



L =

½ρ u²



(g/2) ρ²



½ρ θₓ²



ρ θₜ



ρ u θₓ



Euler–Lagrange variations reproduce the LSDA system exactly.



NUMERICAL ARCHITECTURE



Modules: backend, grid, state, derivatives, eom, rk4, diagnostics, coarse\_grain

Diagnostics: mass, energy, spectrum, density contrasts, gradient norms, mode fractions



Initialization (T1–T4 baseline):



ρ(x,0) = rho0 + drho cos(kx)

θ(x,0) = 0

u(x,0) = 0



LSDA VALIDATION STEPS (1–13)



Steps 1–13 (algebra → architecture → code → invariants) are complete.

Steps 14–15 remain analytically incomplete but now have numerical inputs.



CORE VALIDATION SUMMARY (T1–T4)



(T1) Smoke: invariants stable

(T2) Linear dispersion matches CRFT with ≲3×10⁻⁴ error

(T3) Nonlinear envelopes consistent

(T3b) Structure diagnostics

(T4) Locked-limit CRFT dispersion exactly satisfied



Conclusion: LSDA v1.0 Core is formally locked as correct for CRFT in the acoustic, weak-contrast regime.



STEP-14 — PARAMETER IDENTIFICATION (IN PROGRESS)



Targets: g\_eff, λ\_eff, ν\_eff

Inputs: T2, T4, T3/T3b, T5, T6, T7, T7v2, T8, T9, T10

Data products: lsda\_T2, lsda\_T4, lsda\_T7\_v2 CSVs.



14.1 g\_eff from dispersion (status)



c\_eff ≈ 3.14159

g\_eff ≈ 9.8696

Residuals ≈ machine precision

Mapping to physical CRFT units pending Step-15.



14.2 λ\_eff from dispersion (status)



Best-fit λ\_eff ≈ 0.

Any lam > 0 produces numerical blow-up (T9).

Trusted LSDA envelope enforces lam = 0.

λ\_eff is diagnostic only.



14.3 ν\_eff calibration — long-run multi-ν LSDA tests (final)



A full LSDA multi-ν calibration has been completed using long-duration T7 ν-lock runs, all conducted under the trusted envelope:



N = 256



L = 2.0



rho0 = 1.0



g = 1.0



lam = 0



drho = 1e−3 (strict acoustic regime)



k\_mode = 1



dt = 1e−3



t\_final = 50



fit window: t ∈ \[5, 40]



projection onto sin(kx)



Three ν\_code values tested:



ν\_code = 0.0005

ν\_code = 0.001

ν\_code = 0.002



Using A(t) ≈ A₀ exp(−γ t), ν\_eff = γ / k\_phys² with k\_phys = π:



Results:



ν\_code = 0.0005 → γ\_fit ≈ 2.148280e−03 → ν\_eff ≈ 2.176663e−04

ν\_code = 0.001 → γ\_fit ≈ 4.674334e−03 → ν\_eff ≈ 4.736091e−04

ν\_code = 0.002 → γ\_fit ≈ 9.702263e−03 → ν\_eff ≈ 9.830448e−04



Ratios ν\_eff / ν\_code:



≈ 0.435, 0.474, 0.491 → tightly clustered.



Calibrated mapping:

ν\_eff ≈ 0.46 ν\_code



All configuration details, including t\_final = 50 and fit window \[5, 40], are now permanently recorded for v6.



14.4 Updated Step-14 acceptance status



g\_eff: locked



λ\_eff: zero and physically disabled



ν\_eff: calibrated



Long-run multi-ν ν-lock extraction complete



Strict configuration defined



ν\_eff ≈ 0.46 ν\_code accepted for v6



14.5 Role of ν and dissipative extensions



ν is an LSDA-level dissipative input, not part of the conservative CRFT Lagrangian.

Extraction validated with long-run multi-ν runs and the synthetic T7 v2 dataset.



Within v6, ν\_eff is:



configuration-specific



used only for CRFT-limit reasoning where dissipation is invoked



not assumed universal across resolutions or dt



This completes the ν-line of Step-14.



STEP-15 — FULL CRFT-LIMIT ANALYTIC REDUCTION (SCAFFOLD)



The analytic LSDA → CRFT mapping is established structurally using:



Locked LSDA micro-dynamics and Lagrangian



CRFT continuum target equations



Step-14 parameters (including long-run ν\_eff calibration)



This scaffold is complete; algebraic derivations will be filled in a later revision.



15.1 Objectives and regime



Goal: Derive CRFT acoustic equations from LSDA via linearization + weak-gradient approximations + coarse-graining, showing:



ρ\_t = −∂ₓ(ρ u)

θ\_t = −u θₓ − g\_eff ρ

u\_t = −(½u²)ₓ − (g\_eff ρ)ₓ



and demonstrate how LSDA ν\_code → CRFT ν\_eff under coarse-graining.



Regime:



small-amplitude perturbations



weak gradients



λ = 0



ν\_code within calibrated regime



trusted LSDA envelope



coarse-graining scale large relative to grid spacing



ν\_eff calibration used: ν\_eff ≈ 0.46 ν\_code.



15.2 Linearization around uniform state



Linearizing LSDA:



δρ\_t = −ρ0 δu\_x

δθ\_t = −g δρ

δu\_t = −g δρ\_x



Acoustic dispersion:



ω² ≈ c\_eff² k², with c\_eff² = g\_eff ρ0.



15.3 Coarse-graining and CRFT identification



ρ\_c = CG(ρ)

u\_c = CG(u)

j\_c = CG(ρu)



Under weak gradients:



∂ₜρ\_c ≈ −∂ₓ(ρ\_c u\_c)



CRFT hydrodynamic fields identified directly as (ρ\_c, u\_c).



15.4 Momentum equation and CRFT inviscid form



Starting LSDA:



u\_t = −u u\_x − g ρ\_x

= −(½u²)\_x − g ρ\_x



After CG and dropping higher-order fluctuations:



u\_c,t ≈ −(½u\_c²)\_x − g\_eff ρ\_c,x



which matches CRFT’s inviscid momentum equation.



15.5 Energy alignment and CRFT Lagrangian consistency



E\_LSDA = ∫ dx \[½ρu² + (g/2) ρ² + ½ρ θ\_x²]



Micro-Lagrangian recorded earlier.



Under weak gradients + CG:



E\_c ≈ ∫ dx \[½ρ\_c u\_c² + (g\_eff/2) ρ\_c² + ½ρ\_c (θ\_c,x)²]



A future explicit derivation will show the CRFT Lagrangian reproduces the CRFT continuum equations.



15.6 Incorporation of ν\_eff as coarse-grained dissipation



CRFT Lagrangian remains conservative. Dissipation enters only at EOM level:



u\_t = −(½u²)\_x − (g\_eff ρ)\_x + ν\_eff u\_xx + higher-order terms



ν\_eff ≈ 0.46 ν\_code

configuration-specific

t\_final = 50, window \[5, 40], λ = 0, small amplitudes



15.7 Summary of Step-15 scaffold



Structure fixed:



Linearization → acoustic modes



CG → CRFT continuity and momentum



Energies align in acoustic limit



ν\_eff enters via calibrated u\_xx term



Reduction consistent with all validated LSDA data



Work remaining:



full algebraic derivations



treatment of neglected terms



derivation of CRFT hydrodynamic Lagrangian



ν\_eff dependency on resolution, dt, amplitude



possible extension beyond acoustic regime



CRFT TEST FAMILY (C1–C4) — SPECIFICATION



Defines canonical CRFT numerical tests, analogous to LSDA T-suite.



C1 — Linear Dispersion Verification



Purpose: verify numerical CRFT dispersion matches analytic CRFT dispersion.



Configuration:



periodic domain



plane-wave initial condition



CP–NLSE or CE–NWE branch



RK4 or split-step integrator



small dt



long enough to resolve several periods



Diagnostics: FFT in time to obtain ω\_num(k).

Acceptance: |ω\_num − ω\_analytic| / |ω\_analytic| ≤ 1e−3 for small k.



C2 — Invariant Tracking and Stability



Purpose: ensure integrator preserves CRFT invariants.



Configuration:



smooth non-trivial initial ϕ



CP–NLSE or CE–NWE



long duration



Invariants: norm-like, energy-like, coherence-specific if defined.

Acceptance: relative drift < 1e−4; no blow-up if dt stable.



C3 — Localized Structure / Soliton Stability



Purpose: validate nonlinear coherent propagation.



Initial conditions: analytic soliton, soliton-ansatz, or Gaussian packet.

Acceptance: amplitude/width changes < 5%; bounded radiation.



C4 — Coherence Functional Dynamics



Purpose: test coherence functional C\[ϕ] under gradient flow and full CRFT evolution.



Gradient flow: C must be strictly non-increasing.

Full CRFT: C must remain finite and physically structured.



END OF STATE OF THE THEORY (v6)

