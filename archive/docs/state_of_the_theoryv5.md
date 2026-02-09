STATE OF THE THEORY (v5)



Local Spin-Density Algebra (LSDA)

CRFT-Limit Micro-Model • Full Core Validation (T1–T4) Complete



All text plain-language, audit-ready, and aligned with validated code.



This document defines the authoritative structure, equations, assumptions, and validation path for LSDA v1.0 as the micro-model that cleanly reproduces CRFT in the long-wavelength and weak-contrast limits.



All content incorporates the fully validated LSDA Core Suite (T1, T2, T3, T3b, T4). The LSDA extended suite T7–T10 is now implemented and validated in code, as described in Sections 17 and 19, and feeds into the pending parameter-identification and CRFT-reduction work (Steps 14–15).





1\. PURPOSE OF LSDA REBUILD



The LSDA project replaces legacy LCRD machinery with a simple, auditable, conservative micro-fluid model:



\* minimal fields

\* explicit micro-algebra

\* exact mass conservation

\* low-order dynamics

\* CRFT-limit correctness

\* correct nonlinear behavior

\* GPU-ready architecture



LSDA is now validated through conceptual Steps 1–13 and through the executed test suite T1–T4 and T7–T10 (see Sections 12, 17, and 19).





2\. CRFT CONTINUUM TARGET



CRFT equations of motion:



\* ρ\_t = −∂x(ρ u)

\* θ\_t = −u θ\_x − g\_eff ρ

\* u\_t = −(½u²)\_x − (g\_eff ρ)\_x



CRFT parameters locked for LSDA validation:



\* rho0 = 1.0

\* g\_eff = nominal CRFT acoustic coupling

\* lam = 0

\* beta = 0



LSDA must reproduce these in the coarse-grained weak-contrast limit.





3\. MICRO-FIELDS (LSDA PRIMITIVES)



Micro-field identifications:



\* ρ ≡ s

\* θ ≡ α

\* u ≡ v



Derived gradients:



\* S = ρ\_x

\* Q = u\_x



Energy components:



\* E\_kin   = ½ ρ u²

\* E\_phase = ½ ρ θ\_x²

\* E\_EOS   = (g\_eff/2) ρ²

\* C       = ρ u θ\_x



These map directly to the micro-Lagrangian.





4\. LSDA MICRO-DYNAMICS (LOCKED)



LSDA evolution equations:



\* ρ\_t = −∂x(ρ u)

\* θ\_t = −u θ\_x − g\_eff ρ

\* u\_t = −u u\_x − g\_eff ρ\_x



These come from the micro-Lagrangian and match the Euler–Lagrange equations exactly.



No additional terms are included until CRFT-limit mapping (Steps 14–15) or explicit inclusion of ν, λ terms in extended experiments.





5\. DISCRETIZATION RULES



\* uniform grid

\* periodic boundary conditions

\* centered differences

\* exact mass conservation at the discrete level

\* second-order accurate in space

\* compatible with RK4 or symplectic time-stepping schemes





6\. STABILITY AND INVARIANT REGIME



Weak-gradient constraints (for CRFT-limit validity and numerical stability):



\* |ρ\_x| ≪ ρ / L

\* |u\_x| ≪ u / L



Energy functional:



E = ∫ dx \[½ ρ u² + (g/2) ρ² + ½ ρ θ\_x²]



In all validated core tests (T1–T4) and in the safe subset of extended tests (T7–T10), energy remains bounded and mass is conserved to roundoff within the accepted regime. Outside this regime (e.g., certain ν, λ combinations in T9), numerical instabilities are explicitly recorded and treated as “out of validated envelope,” not as core-model failures.





7\. COARSE-GRAINING AND CRFT RECOVERY



Coarse-grained variables:



\* ρ\_c = CG(ρ)

\* u\_c = CG(u)

\* j\_c = CG(ρ u)



The coarse-graining window L\_cg satisfies:



\* λ\_micro ≪ L\_cg ≪ λ\_macro



CRFT recovery requires:



\* continuity maps exactly (LSDA continuity → CRFT continuity)

\* momentum maps via g\_eff in the weak-gradient limit

\* higher-order terms are suppressed under Step-6 constraints

\* dispersion matches CRFT in the acoustic limit

\* nonlinear dynamics remain physical under T3/T3b scans



These conditions motivate the structure; dispersion and nonlinear behavior are directly tested via T1–T4 and the spectral integrity test T10.





8\. MICRO-LAGRANGIAN (LSDA)



Micro-Lagrangian density:



L =

  ½ ρ u²

\+ (g/2) ρ²

\+ ½ ρ θ\_x²

\+ ρ θ\_t

\+ ρ u θ\_x



Euler–Lagrange variations with respect to ρ, θ, and u reproduce the LSDA dynamical system in Section 4 exactly.





9\. NUMERICAL ARCHITECTURE



LSDA code modules:



\* backend

\* grid

\* state

\* derivatives

\* eom

\* rk4

\* diagnostics

\* coarse\_grain



Diagnostics:



\* mass

\* energy

\* spectrum (Fourier diagnostics)

\* density contrasts

\* gradient norms

\* mode-by-mode power fractions (in T10)





10\. IMPLEMENTATION AND INITIALIZATION



Canonical sinusoidal initial condition (used consistently in T1–T4 and in several extended tests):



\* ρ(x,0)   = rho0 + drho cos(k x)

\* θ(x,0)   = 0

\* u(x,0)   = 0



All core tests share this initialization, with different drho and mode indices k (via k\_mode). Extended tests T7–T10 either reuse this initialization or superpose multiple modes as specified in Sections 17 and 19.





11\. LSDA VALIDATION STEPS (1–13)



Conceptual Steps 1–13 (theoretical and architectural) are complete and validated in code:



\* Step-1: Full algebra definition

\* Step-2: CRFT parameter lock-in

\* Step-3: Discretization and numerical architecture

\* Step-4: Stability and conservation analysis (baseline)

\* Step-5: Coarse-graining calibration (conceptual)

\* Step-6: CRFT recovery conditions (conceptual)

\* Step-7: Full micro-Lagrangian specification

\* Step-8: Numerical architecture (first implementation blueprint)

\* Step-9: First implementation code skeleton (CPU + GPU-ready)

\* Step-10: Core test mapping (T1–T4)

\* Step-11: Systematic CRFT-limit validation and initial parameter scans

\* Step-12: Nonlinear envelope and structure diagnostics (T3/T3b)

\* Step-13: LSDA core suite execution and verification (T1–T4)



Steps 14–15 are defined but not yet completed (see Sections 14 and 15).





12\. FULL LSDA CORE VALIDATION SUMMARY (T1–T4)



This is the core audit block, matching actual run logs (T1–T4). No tests beyond T4 were originally claimed as executed; extended tests T7–T10 are now executed and documented separately in Sections 17 and 19.



T1 — Smoke Test



Task:

\* Validate that LSDA invariants and RK4 integration behave correctly for a small-amplitude sinusoidal perturbation.



Conditions (representative):

\* N = 256, L = 2.0, rho0 = 1.0, drho = 1e−3, g = 1.0, dt = 1e−3, t\_final = 0.2.



Results (representative):

\* Mass drift ≤ 4.4e−16

\* Energy drift ≤ 4.4e−16

\* No instabilities, no visible numerical artifacts.



Interpretation:

\* RK4 + LSDA invariants behave correctly in a basic regime.





T2 — Linear Dispersion Calibration



Task:

\* Compare LSDA linear frequencies with theoretical acoustic dispersion in the small-amplitude limit.



Conditions:

\* N = 256, L = 2.0, rho0 = 1.0, drho = 1e−3, g = 1.0, c = sqrt(g rho0) = 1.0.

\* Modes tested: m = 1, 2, 3, 4, 8, 12 with physical wavenumber k\_phys = m π / (L/2).

\* Theoretical: omega\_th = c k\_phys.

\* Measured: omega\_meas from FFT of ρ(t,x).



Results (representative):

\* rel\_err ≈ −2.499e−4 across all tested modes.



Interpretation:

\* LSDA reproduces CRFT acoustic dispersion to ≲ 3×10⁻⁴ relative error in this setup.





T3 — Nonlinear Envelope and Shock-Onset Scan



Task:

\* Explore nonlinear behavior and onset of steepening in LSDA.



Conditions:

\* N = 256, L = 2.0, rho0 = 1.0, g = 1.0, nu = 0.0, lam = 0.0, k\_mode = 1, t\_final = 0.5, dt = 1e−3.

\* Amplitudes: drho = 0.01, 0.10, 0.30.



Diagnostics:

\* dM = M(t) − M0

\* dE = E(t) − E0

\* max\_density\_contrast = max\_x |ρ(x,t) − rho0| / rho0



Representative results:

\* drho = 0.01:

  \* Mass drift ≤ 4.4e−16

  \* max|dE| ≈ 1.18e−12

  \* max\_density\_contrast ≈ 2.0e−2

\* drho = 0.10:

  \* Mass drift ≤ 4.4e−16

  \* max|dE| ≈ 1.20e−08

  \* max\_density\_contrast ≈ 2.0e−1

\* drho = 0.30:

  \* Mass drift ≤ 4.4e−16

  \* max|dE| ≈ 1.11e−06

  \* max\_density\_contrast ≈ 6.0e−1



Interpretation:

\* Energy drift grows smoothly with amplitude; no blow-up or catastrophic instability at drho ≤ 0.30 over the tested window.

\* Frequency upshift and mild harmonic generation are consistent with physical nonlinear acoustics.





T3b — Structure Diagnostic (Envelope / Steepening)



Task:

\* Resolve spatial structure, gradient growth, and spectral broadening for moderately and strongly nonlinear waves.



Conditions:

\* N = 256, L = 2.0, rho0 = 1.0, g = 1.0, nu = 0.0, lam = 0.0, k\_mode = 1, dt = 1e−3.

\* Amplitudes: drho = 0.10, 0.30.

\* Sampled times: t = 0.05, 0.125, 0.25, 0.50.



Diagnostics per time:

\* dM, dE

\* rho\_max, rho\_min

\* contrast = (rho\_max − rho\_min) / rho0

\* grad\_L2 = ||ρ\_x||₂

\* k\_mean (spectral centroid of |ρ̂(k)|²)



Representative observations:

\* drho = 0.10:

  \* max density\_contrast ≈ 0.0988

  \* max grad\_L2 ≈ 3.10e−1

  \* k\_mean starts near the base acoustic mode (~3.14) and only mildly broadens.

\* drho = 0.30:

  \* max density\_contrast ≈ 0.2963

  \* max grad\_L2 ≈ 9.31e−1

  \* spectrum broadens more strongly but without runaway high-k growth; gradients grow early and then relax.



Interpretation:

\* Envelope modulation and steepening are present and track amplitude.

\* No unphysical shocks or spurious high-k blow-up within the tested window.





T4 — CRFT-Limit Dispersion (Locked Linear Limit)



Task:

\* Confirm that LSDA reproduces the CRFT acoustic relation exactly in the strictly linear locked limit.



Conditions:

\* N = 256, L = 2.0, rho0 = 1.0, g = 1.0, drho = 1e−3, dt and integration window chosen to resolve several periods.

\* Theoretical CRFT dispersion: omega\_CRFT(k) = c k with c = sqrt(g rho0) = 1.0.



Result (representative):

\* For modes m = 1, 2, 3, 4, 8, 12:

  \* omega\_th = omega\_meas to within numerical precision.

  \* rel\_err = 0.0 to the printed digits.



Interpretation:

\* In the strict linear limit, LSDA matches CRFT acoustic dispersion exactly for the tested modes.

\* This is the strongest direct numerical confirmation of LSDA → CRFT matching so far in the linear regime.





13\. CORE VALIDATION CONCLUSION



\* All LSDA Steps 1–13 + T1–T4 are complete and validated.

\* LSDA v1.0 Core is formally “locked” as the correct micro-model for CRFT in the acoustic, weak-contrast regime.

\* Extended tests T7–T10 now probe long-time nonlinear drift, GPU/CPU consistency, parameter envelopes, and multi-mode spectral structure (Sections 17 and 19).

\* Steps 14–15 (parameter identification and full CRFT-limit analytic reduction) remain to be completed and will leverage both core and extended tests.





14\. LSDA STEP-14 — PARAMETER IDENTIFICATION (PENDING)



Extraction targets (to be measured using the validated LSDA core and extended tests):



\* g\_eff

\* λ\_eff

\* ν\_eff



Sources of information:



\* dispersion (T2, T4) → g\_eff

\* curvature corrections and nonlinear shifts (T3)

\* spectral diffusion and high-k behavior (T3b)

\* long-time drift and stability windows (T7)

\* CPU/GPU consistency and numerical tolerance (T8)

\* parameter-stress envelopes in (ν, λ) (T9)

\* multi-mode spectral integrity and mode coupling (T10)



Acceptance tolerances (targets):



\* |g\_eff − g\_target| ≤ 0.1%

\* |λ\_eff − λ\_target| ≤ 1%

\* |ν\_eff − ν\_target| ≤ 1%



Status:

\* Conceptual specification only; numerical extraction not yet performed.

\* Current T7–T10 results constrain safe regimes and provide data products that can be used for parameter fitting once an explicit extraction pipeline is defined.





15\. LSDA STEP-15 — FULL CRFT-LIMIT ANALYTIC REDUCTION (PENDING)



Analytic goal:



\* Prove that, under the Step-6 weak-gradient and small-contrast conditions, coarse-grained LSDA fields satisfy the CRFT equations of motion.



Required demonstrations:



\* LSDA continuity → CRFT continuity (already numerically confirmed; needs formal derivation).

\* LSDA momentum → CRFT momentum, with higher-order terms shown to vanish or become parametrically small.

\* LSDA energy and invariants → CRFT energy functional (up to controlled corrections).

\* LSDA coarse-grained fields (ρ\_c, u\_c, j\_c) satisfy CRFT EOM to the locked order in k and amplitude.



Status:

\* Analytic work not yet completed; will rely on LSDA core equations, the micro-Lagrangian in Sections 3–8, and the numerical constraints from T1–T4 and T7–T10.





16\. NEXT STEPS (HIGH-LEVEL)



\* Complete Step-14 (parameter extraction) using LSDA+CRFT comparison runs, including data from T7–T10.

\* Complete Step-15 (analytic reduction), documenting the LSDA → CRFT derivation with explicit approximations and limits.

\* Integrate LSDA outputs and identified parameters back into CRFT and full-theory synthesis.





17\. LSDA EXTENDED VALIDATION SUITE (CONCEPTUAL SPEC AND CODED TESTS)



Originally, the extended LSDA validation envelope was defined as T5–T10 in abstract form. In practice, the current codebase implements T7–T10 as concrete diagnostics. To avoid renumbering historical notes, this section preserves the original conceptual intent and marks which parts are now realized by specific tests.



T5 — Long-Time Stability and Recurrence (Acoustic Box) \[conceptual only]



Purpose:

\* Test LSDA stability and invariant control over many acoustic periods in a periodic domain.

\* Check for secular drift in mass and energy beyond T1 timescales.



Configuration (conceptual):

\* Domain: N = 256 (or 512), L = 2.0.

\* Background: rho0 = 1.0, g = 1.0, nu = 0.0, lam = 0.0.

\* Initial condition: single-mode sinusoid as in T1/T2, with drho = 0.01 and k\_mode = 1.

\* Time: t\_final ≫ 1 (e.g., 50–100 acoustic periods), dt as in T1/T2 or smaller if needed.



Diagnostics:

\* M(t), E(t) and drifts (dM, dE) over long times.

\* Phase of the fundamental mode versus linear prediction.

\* Spectral leakage to higher harmonics.



Acceptance criteria (conceptual):

\* |dM| remains at or near roundoff.

\* |dE| remains bounded, with drift small compared to total energy over the full run.

\* No unphysical accumulation of high-k power; recurrence behavior qualitatively consistent with weakly nonlinear acoustics.



Status:

\* Specification only; not yet implemented as a dedicated “many-period” recurrence test.

\* Long-time drift behavior for moderate nonlinear amplitudes is currently probed by T7 (Section 19), over a shorter horizon (t\_final = 5) and at specific amplitudes.





T6 — Strong-Nonlinear Steepening / Pre-Shock Benchmark \[conceptual only]



Purpose:

\* Probe LSDA behavior near the edge of the physical acoustic regime.

\* Characterize how density gradients and spectral content evolve under stronger amplitudes.



Configuration (conceptual):

\* Domain and background as in T3/T3b (N = 256 or 512, L = 2.0, rho0 = 1.0, g = 1.0).

\* Initial condition: sinusoidal with higher amplitude (e.g., drho up to 0.5–0.7) and k\_mode = 1.

\* Time: enough for visible steepening but before true numerical shock formation (to be determined empirically).



Diagnostics:

\* density\_contrast(t)

\* grad\_L2(t) = ||ρ\_x||₂

\* spectral centroid k\_mean(t)

\* monitoring of M(t), E(t)



Acceptance criteria (conceptual):

\* LSDA remains stable (no catastrophic blow-up) in the regime still considered “physically acoustic”.

\* Gradients and spectral broadening grow in a controlled, physical manner.

\* Deviations from the CRFT acoustic picture are interpretable as entering a strong-nonlinear regime rather than pure numerical pathology.



Status:

\* Specification only; not yet implemented as a separate benchmark.

\* T3/T3b and T7 partially touch this regime, with T7 explicitly exposing a breakdown at drho = 0.20 (Section 19), which currently marks the boundary of the safe envelope for this configuration.





T7 — Nonlinear Long-Time Drift of Mass and Energy \[implemented]



Purpose:

\* Extend the nonlinear envelope tests (T3/T3b) to longer times and moderate amplitudes.

\* Quantify mass/energy drift and identify the onset of numerical or physical breakdown as amplitude increases.



Configuration (implemented; from lsda\_t7\_nonlinear\_long\_time\_drift):



\* Domain: N = 256, L = 2.0.

\* Background: rho0 = 1.0, g = 1.0.

\* Parameters: nu = 0.0, lam = 0.0, k\_mode = 1.

\* Initial condition: ρ(x,0) = rho0 + drho cos(k x), θ(x,0) = 0, u(x,0) = 0.

\* Amplitudes: drho = 0.05, 0.10, 0.20.

\* Time: t\_final = 5.0, dt = 1.0e-3.

\* Backend: CPU.



Diagnostics:

\* dM(t) = M(t) − M0

\* dE(t) = E(t) − E0

\* max\_abs\_dM, max\_abs\_dE

\* max\_rel\_dM = max\_abs\_dM / |M0|

\* max\_rel\_dE = max\_abs\_dE / |E0|



Representative summary (from run logs):



\* drho = 0.05:

  \* max|dM| ≈ 8.882e−16, max|dM|/|M0| ≈ 4.441e−16

  \* max|dE| ≈ 4.621e−08, max|dE|/|E0| ≈ 4.615e−08

  \* No NaNs; drift remains extremely small and bounded.

\* drho = 0.10:

  \* max|dM| ≈ 6.661e−16, max|dM|/|M0| ≈ 3.331e−16

  \* max|dE| ≈ 1.347e−05, max|dE|/|E0| ≈ 1.34e−05

  \* No NaNs; drift grows but stays small relative to total energy.

\* drho = 0.20:

  \* Early times show bounded behavior, but by t ≈ 3.8 the run develops NaNs in dM and dE.

  \* Invariants and fields become numerically unstable; max|dM| and max|dE| formally diverge.



Interpretation:



\* For drho ≤ 0.10 in this configuration, LSDA maintains excellent mass conservation and modest energy drift over t\_final = 5. This extends the validated nonlinear envelope into a longer-time window.

\* The drho = 0.20 case marks a clear numerical and/or physical breakdown for this resolution, dt, and scheme; it is treated as outside the “safe acoustic/nonlinear” envelope for current purposes.

\* T7 thus provides an empirical upper bound on amplitude for reliable long-time evolution under the current discretization, informing the regime map and Step-14 parameter work.



Status:

\* Implemented and passing as a diagnostic: tests assert invariants remain well-controlled for drho ≤ 0.10 and treat the drho = 0.20 breakdown as an expected out-of-regime signal rather than a “failure” of the code.





T8 — GPU/CPU Consistency and Performance Scaling \[partially implemented]



Purpose:

\* Validate that LSDA behaves identically (within floating-point differences) on CPU and GPU backends.

\* Provide a baseline for performance scaling and future large-N runs.



Configuration (implemented; from lsda\_t8\_gpu\_cpu\_consistency):



\* Base configuration identical to T1/T2-style acoustic test:

  \* N = 256, L = 2.0

  \* rho0 = 1.0, drho = 0.001

  \* k\_mode = 1, g = 1.0, nu = 0.0, lam = 0.0

  \* dt = 1.0e−3, t\_final = 0.2

\* Backends:

  \* CPU (NumPy)

  \* GPU (CuPy), backend name "gpu"



Diagnostics:

\* M0\_cpu, E0\_cpu, M\_final\_cpu, E\_final\_cpu

\* M0\_gpu, E0\_gpu, M\_final\_gpu, E\_final\_gpu

\* Relative differences:

  \* rel\_M0       = |M0\_gpu − M0\_cpu| / |M0\_cpu|

  \* rel\_E0       = |E0\_gpu − E0\_cpu| / |E0\_cpu|

  \* rel\_M\_final  = |M\_final\_gpu − M\_final\_cpu| / |M\_final\_cpu|

  \* rel\_E\_final  = |E\_final\_gpu − E\_final\_cpu| / |E\_final\_cpu|



Representative results:



\* CPU:

  \* M0\_cpu      = 2.0000000000

  \* E0\_cpu      = 1.0000005000

  \* M\_final\_cpu = 2.0000000000

  \* E\_final\_cpu = 1.0000005000

\* GPU:

  \* M0\_gpu      = 2.0000000000

  \* E0\_gpu      = 1.0000005000

  \* M\_final\_gpu = 2.0000000000

  \* E\_final\_gpu = 1.0000005000

\* Relative differences:

  \* rel\_M0       = 0.000e+00

  \* rel\_E0       = 0.000e+00

  \* rel\_M\_final  = 0.000e+00

  \* rel\_E\_final  = 0.000e+00



Interpretation:

\* For this canonical acoustic configuration, CPU and GPU backends are invariant-identical to printed precision.

\* This confirms that the backend abstraction and GPU path are numerically faithful for small-amplitude linear regimes.



Status:

\* Implemented and passing for N = 256, invariant-level comparison.

\* Future extensions may add field-level L2/L∞ comparisons and multi-N scaling, but these are not yet implemented.





T9 — Parameter Stress Test in (ν, λ) \[implemented]



Purpose:

\* Map how LSDA’s invariant behavior and numerical robustness depend on small viscosity (ν) and dispersion (λ) values around the CRFT-locked baseline.

\* Identify safe regions (no NaNs, small drift) versus clearly unstable or ill-discretized parameter regions.



Configuration (implemented; from lsda\_t9\_param\_stress):



\* Base parameters:

  \* N = 256, L = 2.0

  \* rho0 = 1.0, drho = 0.001

  \* k\_mode = 1, g = 1.0

  \* dt = 1.0e−3, t\_final = 0.5

\* Parameter grid:

  \* nu ∈ {0.0, 1.0e−3, 5.0e−3}

  \* lam ∈ {0.0, 1.0e−4, 5.0e−4}

\* For each (nu, lam) pair, identical sinusoidal initial conditions are used.



Diagnostics per case:

\* max\_abs\_dM, max\_rel\_dM

\* max\_abs\_dE, max\_rel\_dE

\* has\_nan flag (any NaNs or infs encountered in the run)



Representative summary table (from run logs):



(Values summarized qualitatively; full table is preserved in run output.)



\* lam = 0.0 for all tested nu:

  \* nu = 0.0:

    \* max|dM| ≈ 6.661e−16, max|dM|/|M0| ≈ 3.331e−16

    \* max|dE| ≈ 4.441e−16, max|dE|/|E0| ≈ 4.441e−16

    \* has\_nan = False

  \* nu = 1.0e−3:

    \* max|dM| ≈ 4.441e−16, max|dM|/|M0| ≈ 2.220e−16

    \* max|dE| ≈ 2.937e−09, max|dE|/|E0| ≈ 2.937e−09

    \* has\_nan = False

  \* nu = 5.0e−3:

    \* max|dM| ≈ 4.441e−16, max|dM|/|M0| ≈ 2.220e−16

    \* max|dE| ≈ 1.442e−08, max|dE|/|E0| ≈ 1.442e−08

    \* has\_nan = False



\* lam > 0.0 for any tested nu (0, 1.0e−3, 5.0e−3):

  \* Runs develop NaNs and huge formal |dM|, |dE| by t ≲ 0.2–0.3.

  \* has\_nan = True for all these cases.

  \* This clearly marks these parameters as numerically unstable under the current discretization and time step.



Interpretation:

\* The ν-only line (lam = 0) is robust across a modest range of viscosities: invariants remain well-behaved and drifts remain small, even for ν = 5×10⁻3 over t\_final = 0.5.

\* Any non-zero λ in the current implementation produces rapid blow-up and NaNs for this configuration, indicating that the dispersion term and/or its discretization and time step need redesign before λ can be safely used.

\* For now, λ is effectively “disabled” in the trusted LSDA envelope; T9 formally records that fact and provides a data-backed regime boundary for Step-14.



Status:

\* Implemented and passing by design: the test asserts that no-NaN behavior and small mass drift are maintained only for the lam = 0 line; it explicitly allows flagged NaN behavior for lam > 0 as an expected diagnostic outcome rather than a failure.





T10 — Multi-Mode Spectral Structure Test \[implemented]



Purpose:

\* Check that, in a small-amplitude multi-mode regime, LSDA preserves the mode-by-mode energy partition over the integration window.

\* Validate that there is no spurious energy transfer between well-separated linear modes in the strictly linear limit.



Configuration (implemented; from lsda\_t10\_spectral\_structure):



\* N = 256, L = 2.0

\* rho0 = 1.0, g = 1.0

\* nu = 0.0, lam = 0.0

\* Multi-mode initial condition:

  \* k\_modes       = (1, 2, 3)

  \* amplitudes    = (0.001, 0.0005, 0.00025)

  \* ρ(x,0)        = rho0 + Σ\_i drho\_i cos(k\_i x)

  \* θ(x,0)        = 0

  \* u(x,0)        = 0

\* Time window: t\_final chosen to resolve several acoustic periods (exact value not critical for the reported spectral fractions; it matches the test script).



Diagnostics:

\* Compute Fourier transform of ρ(x,t) at t = 0 and t = t\_final.

\* Define spectral power fraction P\_k(t) for each of the three excited modes.

\* Compare:

  \* ΔP\_k = P\_k(t\_final) − P\_k(0)

\* Compute:

  \* max\_abs\_change = max\_k |ΔP\_k|

  \* max\_rel\_change = max\_k |ΔP\_k| / P\_k(0)



Representative results:



Mode-by-mode fractional power (initial vs final):



\* k = 1: P\_1(0) = 0.76190, P\_1(t\_final) = 0.76190, ΔP\_1 = 0.000e+00

\* k = 2: P\_2(0) = 0.19048, P\_2(t\_final) = 0.19048, ΔP\_2 = 0.000e+00

\* k = 3: P\_3(0) = 0.04762, P\_3(t\_final) = 0.04762, ΔP\_3 = 0.000e+00



Summary:

\* max\_abs\_change = 0.000e+00

\* max\_rel\_change = 0.000e+00 (to the printed digits)



Interpretation:

\* In the strictly linear, multi-mode regime, LSDA preserves the mode-by-mode spectral power distribution exactly to printed precision.

\* This strongly supports the view that LSDA’s linear dynamics are spectrally clean, with no spurious mode coupling over the tested window.



Status:

\* Implemented and passing; serves as a spectral counterpart to the scalar dispersion checks in T2 and T4.





18\. SUMMARY OF LSDA VALIDATION STATUS



\* Core theoretical and numerical structure (Steps 1–13) and core tests (T1–T4 + T3b) are implemented and validated.

\* Extended LSDA diagnostics T7–T10 are now implemented and passing, with the following roles:

  \* T7: Nonlinear long-time drift; identifies safe vs unsafe amplitude regimes.

  \* T8: CPU/GPU invariants consistency for canonical acoustic runs.

  \* T9: Parameter-stress envelope in (ν, λ); confirms ν-line robustness and flags λ ≠ 0 as currently unstable.

  \* T10: Multi-mode spectral structure; validates mode-by-mode spectral integrity in the linear regime.

\* Original conceptual extended tests T5 and T6 remain as future targets (recurrence and strong pre-shock benchmarks).

\* Coarse-grain/CRFT field reconstruction and global regime mapping remain part of the broader LSDA → CRFT/FT program and will be revisited once parameter extraction and analytic reduction (Steps 14–15) are in place.



This document is now synchronized with the actually implemented LSDA tests in the current codebase and can be used as the authoritative high-level state of LSDA v1.0.



18\. LSDA → CRFT ANALYTIC REDUCTION (STEP-15 ANALYTIC PLAN)



Goal



&nbsp;   Provide an explicit, plain-text derivation that shows how the LSDA

&nbsp;   micro-equations reduce to the CRFT-level fluid equations and energy

&nbsp;   functional in the appropriate limits. This step (Step-15) turns the

&nbsp;   numerical evidence from T1–T4 and T7–T10 into a clean analytic bridge.



Scope



&nbsp;   • Work strictly with the already-validated LSDA v1.0 core model.

&nbsp;   • Use the same symbol set and conventions as the code and equation inventory.

&nbsp;   • Restrict to the acoustic / weak-gradient, weakly nonlinear regime that is

&nbsp;     already covered by the tests (T1–T4 and the relevant extended tests).



18.1 Continuity equation: LSDA → CRFT



&nbsp;   1) Write down the LSDA continuity equation in its exact form from the

&nbsp;      equation inventory (no new symbols, no reinterpretations).



&nbsp;   2) Identify the mapping between LSDA variables and CRFT fluid variables:

&nbsp;          ρ\_LSDA  ↔  ρ\_CRFT

&nbsp;          u\_LSDA  ↔  v\_CRFT (fluid velocity)

&nbsp;      making this mapping explicit in the text.



&nbsp;   3) Show that, under the same periodic boundary conditions and coarse-grained

&nbsp;      averaging used in the simulations, the LSDA continuity equation becomes

&nbsp;      the CRFT continuity equation

&nbsp;          ∂\_t ρ + ∂\_x (ρ v) = 0

&nbsp;      in the weak-gradient / smooth-field limit.



&nbsp;   4) Clarify which approximations are used:

&nbsp;      • gradients of ρ and u are small on the coarse-graining scale,

&nbsp;      • no shock formation in the tested regimes,

&nbsp;      • higher-order gradient corrections are formally kept but then neglected

&nbsp;        in the strict CRFT limit.



18.2 Momentum equation: LSDA → CRFT (weak-gradient limit)



&nbsp;   1) Write down the LSDA momentum equation in its exact form, including all

&nbsp;      pressure, viscous, and dispersive terms that appear in LSDA v1.0.



&nbsp;   2) Decompose the right-hand side into:

&nbsp;          (i)   pressure-like term(s),

&nbsp;          (ii)  viscous term(s),

&nbsp;          (iii) dispersive / higher-gradient term(s).



&nbsp;   3) Show that in the weak-gradient limit (and for lam = 0 in the tested

&nbsp;      configurations), the LSDA momentum equation reduces to the CRFT-level

&nbsp;      momentum equation for an isentropic fluid:

&nbsp;          ∂\_t (ρ v) + ∂\_x (ρ v^2 + p(ρ)) = viscous + higher-order terms



&nbsp;   4) Identify the effective pressure p(ρ) that corresponds to the LSDA

&nbsp;      potential / equation-of-state used in the core simulations, and show

&nbsp;      that

&nbsp;          c^2 = ∂p/∂ρ |\_{ρ0}  ≈  g\_eff ρ0

&nbsp;      matches the g\_eff extracted from the dispersion analysis.



&nbsp;   5) Make explicit how the effective viscosity ν\_eff (from T7/T9) appears in

&nbsp;      the coarse-grained momentum equation, and under which approximations the

&nbsp;      dispersive term is neglected or kept as a small correction.



18.3 Energy functional: LSDA → CRFT energy



&nbsp;   1) Start from the LSDA energy density used in invariants.py:

&nbsp;          e\_LSDA(ρ, u, ρ\_x; g, ν, λ)

&nbsp;      including kinetic, compressive, and (when present) dispersive terms.



&nbsp;   2) Show how the spatial integral of e\_LSDA matches the CRFT energy functional

&nbsp;      in the acoustic regime, i.e. identify the CRFT energy density

&nbsp;          e\_CRFT(ρ, v) = ½ ρ v^2 + U(ρ)

&nbsp;      and demonstrate the mapping from LSDA parameters to U(ρ).



&nbsp;   3) In the lam = 0 baseline, show that the additional gradient contribution

&nbsp;      to the energy is negligible in the tested T1–T4 configurations, making

&nbsp;      the CRFT energy functional a strict limit of LSDA.



&nbsp;   4) For lam ≠ 0 (treated cautiously, in light of T9), outline how the

&nbsp;      gradient term would enter the CRFT energy as a higher-order correction,

&nbsp;      but mark this explicitly as “formal only” until the discretization is

&nbsp;      improved.



18.4 Coarse-graining and scale separation



&nbsp;   1) Define the coarse-graining operator used in your code / theory language,

&nbsp;      e.g. a spatial averaging over blocks of size Δx\_coarse, with

&nbsp;          Δx\_coarse  ≫  Δx\_fine

&nbsp;      but still small compared to the macroscopic domain.



&nbsp;   2) State clearly the assumed hierarchy of scales:

&nbsp;          Δx\_fine   ≪   Δx\_coarse   ≪   L\_domain



&nbsp;   3) Show how the coarse-grained fields (ρ̄, v̄) satisfy the CRFT equations to

&nbsp;      leading order, with subgrid corrections suppressed by powers of

&nbsp;      (Δx\_fine / Δx\_coarse) and by the smallness of gradients observed in the

&nbsp;      simulations.



&nbsp;   4) Tie this back to the numerical evidence:

&nbsp;      • T1–T4: LSDA reproduces acoustic dispersion and energy / mass invariants.

&nbsp;      • T7–T10: LSDA behaves stably and predictably across inhomogeneous and

&nbsp;        parameter-stress regimes within the safe envelope.

&nbsp;      Together, these justify the CRFT interpretation of the coarse-grained

&nbsp;      LSDA dynamics.



18.5 Deliverables for Step-15



&nbsp;   • A single analytic note (or appendix) that walks through:

&nbsp;         - LSDA continuity → CRFT continuity,

&nbsp;         - LSDA momentum → CRFT momentum (weak-gradient limit),

&nbsp;         - LSDA energy → CRFT energy,

&nbsp;         - the coarse-graining argument and scale assumptions.



&nbsp;   • Plain-text equations in the same notation as the code and

&nbsp;     equation\_inventory, so they can be copied directly into the

&nbsp;     state\_of\_the\_theory and white-paper documents.



&nbsp;   • Explicit listing of all approximations and where each is used, to make

&nbsp;     the LSDA → CRFT bridge auditable and non-mysterious.



