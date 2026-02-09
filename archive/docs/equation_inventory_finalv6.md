\# EQUATION INVENTORY (v6)

\# Canonical CRFT Equations + Legacy LCRD + LSDA Micro-Model

\# Fully synchronized with Step-5/Step-6 and LSDA v1.0 (T1–T10) results



This document is the single source of truth for all equations.

All math is kept in plain text.



---

\# 0. Unified Symbol Glossary

---



Coordinates:

    x, t



Derivatives:

    ∂x, ∂xx, ∂xxx, ∂xxxx, ∇, Δ

    τ — coherence gradient-flow time



Fields (complex-field layer):

    φ(x,t) — complex field

    ρ = |φ|² — density

    θ = arg(φ) — phase

    v = θ\_x — velocity

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

    lambda\_coh — coherence penalty weight



Potentials:

    U(ρ), Up(ρ) = dU/dρ



Hydrodynamics (continuum-level):

    P(ρ) — pressure

    Q — quantum pressure

    c\_eff — effective sound speed



Coherence:

    C = (|φ|² − rho0)²

    δC/δφ\*



LSDA / CRFT-acoustic layer (micro-model and target):

    ρ(x,t) — LSDA density (micro, but identified with fluid density)

    θ(x,t) — LSDA phase

    u(x,t) — LSDA micro-velocity (maps to CRFT fluid velocity)

    S = ρ\_x — density gradient

    Q\_u = u\_x — velocity gradient

    g\_eff — effective acoustic coupling (from dispersion fits)

    nu (ν) — effective viscosity (from decay fits)

    c — acoustic speed with c² = g ρ0 (code-level)

    c\_eff — fitted effective acoustic speed (from LSDA dispersion)



Energies (LSDA micro-structure):

    E\_kin = ½ ρ u²

    E\_phase = ½ ρ θ\_x²

    E\_EOS = (g/2) ρ²

    C\_LSDA = ρ u θ\_x  — LSDA coupling term used in micro-Lagrangian



Data products (for reference, used by extraction tools, not new symbols):

    lsda\_T2\_dispersion\_data.csv

    lsda\_T4\_dispersion\_data.csv

    lsda\_T7\_v2\_decay\_data.csv



---

\# 1. First-Order CRFT: CP–NLSE

---



\## 1.1 Lagrangian

L = − hbar ρ θ\_t

    − (hbar² / (2m)) ρ θ\_x²

    − lam (ρ\_x)² / (4ρ)

    + U(ρ)



\## 1.2 Equation of motion

i φ\_t

\+ (1/2) φ\_xx

− g |φ|² φ

\+ lam φ\_xxxx

\+ beta φ\_xxxxxx

= 0



\## 1.3 Linear dispersion

ω²(k)

= (k² / 2)²

  + g rho0 k²

  + lam k⁴

  + beta k⁶



---

\# 2. Second-Order CRFT: CE–NWE

---



\## 2.1 Equation

φ\_tt

\+ (1/4) φ\_xxxx

− g rho0 φ\_xx

= 0



\## 2.2 Lagrangian

L = (1/2)|φ\_t|²

  − (1/2)c²|φ\_x|²

  + (1/2)lam|φ\_xx|²

  + (1/2)beta|φ\_xxx|²

  − (1/2)g(|φ|² − rho0)²



\## 2.3 Dispersion

ω²(k)

= (k² / 2)²

  + g rho0 k²

  + lam k⁴

  + beta k⁶



---

\# 3. Hydrodynamic Lift (Madelung)

---



φ = sqrt(ρ) exp(i θ)

v = θ\_x



Continuity:

    ρ\_t + ∂x(ρ v) = 0



Phase:

    θ\_t + v θ\_x + (1/ρ) ∂x P = 0



Quantum pressure:

    Q = −(1/(2ρ)) (∂xx sqrt(ρ)) / sqrt(ρ)



---

\# 4. Coherence Functional

---



Coherence density:

    c(ρ) = (ρ\_x)² / (4ρ)



Penalty:

    C = (|φ|² − rho0)²



Variation:

    δC/δφ\* = 2(|φ|² − rho0)φ



Coherence-modified NLSE:

    R = R₀ + lambda\_coh (|φ|² − rho0)φ



---

\# 5. Frozen-Core CRFT

---



\## 5.1 Lagrangian

L = −(hbar²/2m)|φ\_x|²

    − hbar ρ θ\_t

    + lam (ρ\_x²)/(4ρ)

    + U(ρ)



\## 5.2 EOM

i hbar φ\_t

\+ (hbar²/2m) φ\_xx

\+ Up(|φ|²)

= 0



\## 5.3 Continuity (corrected)

ρ\_t + ∂\_x\[(hbar/m) ρ θ\_x] = 0



\## 5.4 Frozen-core dispersion

ω² = c² k² + (hbar²/(2m) + lam) k⁴



---

\# 6. Solitons, Vortices, Turbulence

---



(unchanged; same validated expressions)



---

\# 7. CRFT–LCRD Alignment Layer (legacy, pre-LSDA)

---



This section records empirical relationships proven by Step-5 and Step-6

for the earlier LCRD v1 micro-model.

LSDA v1.0 now replaces this machinery for current work, but the

relationships are retained for audit and comparison.



\## 7.1 Microscopic DOFs (LCRD v1)

n\_j ≥ 0

u\_j ∈ U(1)

θ\_j micro-phase

z\_j = sqrt(n\_j) u\_j



Coarse cell I using block size b:

ρ\_I = avg(n\_j)

θ\_I = wrapped avg(θ\_j)

φ\_I ≈ sqrt(ρ\_I) exp(i θ\_I)



\## 7.2 IR dispersion calibration (CG-T1)

For ρ0 = 1, lam = 0, beta = 0:



Effective cubic nonlinearity:

g\_eff ≈ 0.1666456



\## 7.3 Coarse conservation (CG-T3, CG-T4)

mass drift  ~ 1e−9

energy drift ~ 1e−8



\## 7.4 Amplitude robustness (CG-T2)

Linear regime: A ≤ 0.02



\## 7.5 Nonlinear/multiscale regime (Step-6)

All CG-T5, CG-T6, CG-T7 results embedded in Step-6 doc.



---

\# 8. Fundamental Theory Layer (LCRD Candidate; legacy)

---



This section summarizes how LCRD v1 was mapped to CRFT.

It does not define current LSDA-based CRFT equations and is kept

as a legacy FT candidate for traceability.



\## 8.1 FT symbols

n\_j, u\_j, θ\_j, z\_j

ε, b, G, C\_coh, ρ0



\## 8.2 Parameters affecting CRFT alignment

g\_eff, lam, beta

ρ0, coherence penalty, block size, subsystem averaging



\## 8.3 CRFT reference dispersion

ω²(k) = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶



\## 8.4 Step-5 summary (IR)

g\_eff = 0.1666456

mass drift ~1e−9

energy drift ~1e−8



\## 8.5 Step-6 summary (nonlinear/multiscale)

g\_eff amplitude drift ≤ 2.6e−5

spectral-power drift ~1e−8

long-time drift ~1e−10



---

\# 9. LSDA Micro-Model and CRFT Acoustic Target (current)

---



This section defines the LSDA v1.0 micro-model that replaces

legacy LCRD for CRFT-limit work.

Equations here are taken directly from the validated LSDA core and

extended test suite (T1–T10) and from the current state\_of\_the\_theory.



---

\## 9.1 CRFT acoustic continuum target (hydrodynamic form)

---



Target CRFT equations of motion in acoustic, weak-contrast limit:



ρ\_t = −∂x(ρ u)



θ\_t = −u θ\_x − g\_eff ρ



u\_t = −(½ u²)\_x − (g\_eff ρ)\_x



Equivalently for the velocity equation:



u\_t = −u u\_x − g\_eff ρ\_x



Parameters:



    rho0 = 1.0      (background density, locked in LSDA tests)

    g\_eff           (effective acoustic coupling to be extracted)

    lam = 0         (for baseline LSDA–CRFT matching)

    beta = 0        (for baseline LSDA–CRFT matching)



These are the continuum-level targets LSDA must reproduce after

coarse-graining in the long-wavelength, weak-contrast regime.



---

\## 9.2 LSDA micro-fields and identifications

---



Micro-field identifications:



    ρ ≡ s            (LSDA density)

    θ ≡ α            (LSDA phase)

    u ≡ v            (LSDA velocity)



Derived gradients:



    S = ρ\_x

    Q\_u = u\_x



Energy components (local densities):



    E\_kin   = ½ ρ u²

    E\_phase = ½ ρ θ\_x²

    E\_EOS   = (g/2) ρ²

    C\_LSDA  = ρ u θ\_x



These map directly into the LSDA micro-Lagrangian and the numerical

invariant diagnostics used in the code (mass, energy, spectrum).



---

\## 9.3 LSDA micro-Lagrangian and equations of motion

---



Micro-Lagrangian density (LSDA v1.0 core):



    L =

      ½ ρ u²

    + (g/2) ρ²

    + ½ ρ θ\_x²

    + ρ θ\_t

    + ρ u θ\_x



Euler–Lagrange variations with respect to ρ, θ, and u give the LSDA

dynamical system used throughout the tests:



    ρ\_t = −∂x(ρ u)



    θ\_t = −u θ\_x − g\_eff ρ



    u\_t = −u u\_x − g\_eff ρ\_x



No additional terms are included in the locked LSDA v1.0 core until:

    • explicit ν, λ terms are added in parameter-stress experiments

    • CRFT-limit mapping (Steps 14–15) introduces effective parameters



These equations are the authoritative micro-dynamics for LSDA v1.0.



Associated tests:

    • T1, T2, T3, T3b, T4 — core LSDA validation

    • T5–T10 — extended envelope and parameter-stress validation



---

\## 9.4 LSDA energy functional and invariants

---



Continuous LSDA energy functional:



    E = ∫ dx \[ ½ ρ u² + (g/2) ρ² + ½ ρ θ\_x² ]



Invariants used in diagnostics:



    Mass:

        M = ∫ dx ρ



    Energy:

        E as above



In all trusted runs (core tests and safe extended tests), LSDA

maintains:



    • Exact mass conservation to roundoff

    • Bounded, small energy drift within the validated regime



Representative regimes (from T1–T4, T5–T7):



    • Small amplitude drho ≲ O(10⁻³) → drift at roundoff

    • Moderate amplitude up to drho ≈ 0.1 → small but growing |dE|

    • Strong amplitude drho ≈ 0.2 → breakdown, outside safe envelope



These behaviors are recorded at the state-of-the-theory level; the

equations above are the ones being tested.



---

\## 9.5 LSDA dispersion and g\_eff / λ\_eff extraction

---



Acoustic dispersion relation in the LSDA linear limit:



    ω\_th = c k\_phys



with



    c = sqrt(g rho0)



for code-level parameters (rho0 = 1.0, g = 1.0 in the core tests).



Fitted effective acoustic speed and coupling:



From linear-dispersion tests and extraction tooling:



    c\_eff   ≈ 3.14159

    g\_eff   ≈ 9.8696



with the internal consistency relation:



    c\_eff² ≈ g\_eff ρ0



A polynomial fit for ω² as a function of k² at the LSDA level uses:



    ω² ≈ a0 + a1 k² + a2 k⁴



with representative results (for the locked dispersion window):



    a0 ≈ 1.51e−11

    a1 ≈ 9.8696

    a2 = 0



so that, within numerical precision,



    λ\_eff ≈ 0    (effective k⁴ coefficient in this linear regime)



Important status flags:



    • The dispersion-based extraction of (c\_eff, g\_eff) is numerically

      consistent and stable for the tested LSDA regime.



    • The effective λ\_eff is numerically ≈ 0 in the fitted window.

      However, explicit λ > 0 runs in LSDA currently develop numerical

      instabilities; λ is therefore treated as a diagnostic-only

      coefficient until a redesigned dispersion operator is in place.



Equations for the extraction relations are:



    c\_eff² = g\_eff ρ0

    ω²(k)  ≈ g\_eff ρ0 k²  (in the acoustic limit for lam = beta = 0)



These are the only extraction relations used; no additional hidden

closures are introduced here.



---

\## 9.6 LSDA viscosity ν\_eff extraction (synthetic pipeline)

---



For the synthetic T7 v2 calibration dataset, amplitude decay is given

exactly by:



    A(t) = A0 exp(−2 ν\_true k\_phys² t)



with representative parameters:



    k\_phys = 1.0

    nu\_true ≈ 0.00743106

    A0 = 1.0



Taking logarithms:



    log A(t) = log A0 − 2 ν\_true k\_phys² t



The extraction pipeline fits:



    log A(t) = m t + b



and identifies:



    m = −2 ν\_eff k\_phys²

    ⇒ ν\_eff = −m / (2 k\_phys²)



For the synthetic test:



    ν\_eff ≈ ν\_true ≈ 0.00743106



with residuals at machine precision, confirming that the extraction

equation and pipeline are numerically sound for genuinely exponential

decay.



These formulas are the authoritative relations for ν\_eff extraction

from any future LSDA decay windows that are close to exponential.



---

\## 9.7 Discretization, coarse-graining, and CRFT mapping (equation-level)

---



Discretization rules (summary, equation-level):



    • uniform grid, periodic boundary conditions

    • centered differences for spatial derivatives

    • second-order accurate in space

    • RK4 (and compatible symplectic schemes) for time integration

    • exact discrete mass conservation by construction



Coarse-grained variables (conceptual, for CRFT mapping):



    ρ\_c = CG(ρ)

    u\_c = CG(u)

    j\_c = CG(ρ u)



with a coarse-graining window L\_cg satisfying:



    λ\_micro ≪ L\_cg ≪ λ\_macro



In the weak-gradient, small-contrast regime, the coarse-grained

fields are intended to satisfy the CRFT acoustic equations:



    ρ\_t = −∂x(ρ u)



    u\_t = −u u\_x − g\_eff ρ\_x



up to controlled corrections from viscosity, dispersion, and

sub-grid structure. The explicit analytic derivation (Step-15)

is pending, but no additional equations beyond those already

listed here are assumed.



---

\# END



Appendix A – Terminology and Definitions



This appendix collects the key acronyms and labels used throughout this equation inventory, to keep the larger project terminology consistent and avoid drift.



A.1 LSDA



LSDA = Local Sound-Density Approximation.



In this workspace, LSDA denotes the 1D acoustic-density model implemented in the lsda/ code package and referenced in the LSDA test suite (T1–T10). Concretely:



\- Fields:

  - rho(x, t): scalar density field.

  - u(x, t): scalar velocity field.

\- Parameters:

  - g: effective acoustic coupling (feeds into g\_eff for CRFT).

  - nu: viscosity-like coefficient used in linear-decay and parameter-stress diagnostics.

  - lam: dispersion-like coefficient used as a diagnostic knob (lam = 0 in the trusted baseline).

\- Core equations:

  - Continuity:   rho\_t + (rho \* u)\_x = 0

  - Momentum:     u\_t + u \* u\_x + g \* rho\_x - nu \* u\_xx - lam \* rho\_xxx = 0

\- ν (nu): effective viscosity-like coefficient in LSDA.

&nbsp; - Appears only in LSDA (Local Sound-Density Approximation) PDE as ν u\_xx.

&nbsp; - Does not appear in the CRFT conservative Lagrangian; any ν in CRFT-related equations is treated as a phenomenological, non-Hamiltonian extension.



The LSDA equations, invariants, and tests recorded in this inventory are the sole authoritative reference for the numeric “acoustic baseline” in the ToE workspace.



A.2 CRFT



CRFT = Coherence-Regularized Field Theory.



In this workspace, CRFT is the continuum, coarse-grained field theory that LSDA is meant to approximate in a specific limit (small amplitude, long wavelength, acoustic sector). At the level of parameters:



\- g\_eff is the effective coupling inferred from LSDA dispersion (extracted from T2/T4 data).

\- c\_eff is the corresponding effective sound speed, with c\_eff^2 ≈ g\_eff \* rho0 in the acoustic sector.

\- lambda\_eff is a numerical k^4 correction extracted from LSDA dispersion fits; in the current stencil it is effectively zero and lam > 0 in the PDE is numerically unstable.

\- nu\_eff is an effective viscosity inferred from amplitude decay fits (via the T7 pipeline).



The CRFT reconstruction document (crft\_reconstruction\_v1.md) uses these LSDA-informed parameters as boundary conditions for the coherence field theory.



A.3 LCRD



LCRD = Local Coherence Rotor Dynamics.



LCRD is the higher-level, conceptual model for localized “rotor-like” coherence structures in an underlying field. The intended hierarchy is:



\- LCRD: mesoscopic coherence / rotor model.

\- CRFT: coherence-regularized field theory.

\- LSDA: 1D acoustic-density truncation used for clean numerical testing and parameter extraction.



In this hierarchy, LSDA does not model coherence or spin directly; it provides a stable, well-characterized acoustic sector whose effective parameters constrain CRFT, which in turn is meant to approximate LCRD in an appropriate limit.



A.4 Acoustic sector and effective parameters



In this inventory, “acoustic sector” refers to small-amplitude, long-wavelength perturbations of a uniform background density rho0, where:



\- The dispersion relation is approximately omega ≈ c\_eff \* k.

\- c\_eff is measured from LSDA and used to define g\_eff ≈ c\_eff^2 / rho0.

\- Higher-order corrections (e.g., k^4 terms) are summarized by lambda\_eff, but are currently treated as diagnostic only.



The key effective parameters are:



\- g\_eff: effective acoustic coupling, locked by LSDA dispersion fits.

\- lambda\_eff: effective k^4 coefficient, numerically consistent with 0 in the present discretization; lam = 0 is used in the trusted envelope.

\- nu\_eff: effective viscosity, extracted by fitting exponential amplitude decay in the T7-style pipeline.



Whenever these appear in equation descriptions or test associations, they should be interpreted as parameters inferred from or constrained by LSDA, not arbitrary free parameters.



A.5 Naming discipline



To avoid terminology drift:



\- LSDA must always expand to “Local Sound-Density Approximation” in this project.

\- CRFT must always expand to “Coherence-Regularized Field Theory”.

\- CP–NLSE must always expand to "Coherence-Penalized Nonlinear Schrodinger Equation".

\- CE–NWE must always expand to "Coherence-Extended Nonlinear Wave Equation".

\- LCRD must always expand to “Local Coherence Rotor Dynamics”.



If any future extensions introduce additional acronyms or rename an existing layer, this appendix should be updated at the same time as the corresponding equations and test descriptions.

