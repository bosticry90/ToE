\# FT Step-7 — LCRD v2 Candidate Dynamics

Document: ft\_step7\_lcrd\_v2\_dynamics.md



Context:

\- CRFT equations: frozen and canonical (see equation\_inventory\_finalv4.md).

\- LCRD v1: implemented and validated (CG-T1–CG-T7).

\- Step-7 goal: propose explicit LCRD v2 update formulas F\_n and F\_theta,

&nbsp; introducing coherence-corrected dynamics with better small-k behavior,

&nbsp; while preserving IR calibration and coarse invariants.



Status: DESIGN ONLY (no code yet, no claims of validation).



--------------------------------------------------------------------

\# 1. Lattice Setup and Variables

--------------------------------------------------------------------



1D lattice:

&nbsp;   sites j = 0, 1, ..., N−1

&nbsp;   spacing ε

&nbsp;   length L = N ε



Microscopic DOFs:

&nbsp;   n\_j(t)   ≥ 0      # density-like variable at site j

&nbsp;   theta\_j(t)        # phase-like variable at site j

&nbsp;   u\_j(t)  = exp(i theta\_j(t))

&nbsp;   z\_j(t)  = sqrt(n\_j(t)) \* u\_j(t)



We will define:

&nbsp;   n\_j(t + dt)   = n\_j(t)   + dt \* F\_n(j; n, theta)

&nbsp;   theta\_j(t + dt) = theta\_j(t) + dt \* F\_theta(j; n, theta)



All F\_n and F\_theta expressions below are candidate formulas.



--------------------------------------------------------------------

\# 2. Discrete Stencils and Helper Quantities

--------------------------------------------------------------------



We assume periodic boundary conditions for now:

&nbsp;   j+1 wraps to 0 at j = N−1, etc.



2.1. Discrete gradients

-----------------------



Phase gradient at midpoints:



&nbsp;   grad\_theta\_j\_plus  = (theta\_{j+1} - theta\_j) / ε

&nbsp;   grad\_theta\_j\_minus = (theta\_j - theta\_{j-1}) / ε



Cell-centered phase gradient (symmetric):



&nbsp;   grad\_theta\_j = (theta\_{j+1} - theta\_{j-1}) / (2 ε)



2.2. Discrete Laplacians

-------------------------



Density Laplacian:



&nbsp;   lap\_n\_j = (n\_{j+1} - 2 n\_j + n\_{j-1}) / ε²



Phase Laplacian:



&nbsp;   lap\_theta\_j = (theta\_{j+1} - 2 theta\_j + theta\_{j-1}) / ε²



Both are local and preserve global sums appropriately:

&nbsp;   sum\_j lap\_n\_j = 0   (with periodic BCs).



2.3. Discrete current and divergence

------------------------------------



We define a discrete current analogous to ρ v:



Midpoint densities:



&nbsp;   n\_half\_j\_plus  = 0.5 \* (n\_j + n\_{j+1})

&nbsp;   n\_half\_j\_minus = 0.5 \* (n\_{j-1} + n\_j)



Midpoint velocities:



&nbsp;   v\_half\_j\_plus  = grad\_theta\_j\_plus

&nbsp;   v\_half\_j\_minus = grad\_theta\_j\_minus



Midpoint currents:



&nbsp;   J\_half\_j\_plus  = n\_half\_j\_plus  \* v\_half\_j\_plus

&nbsp;   J\_half\_j\_minus = n\_half\_j\_minus \* v\_half\_j\_minus



Cell-centered divergence:



&nbsp;   div\_J\_j = (J\_half\_j\_plus - J\_half\_j\_minus) / ε



This div\_J\_j is the discrete analogue of ∂x(ρ v).



--------------------------------------------------------------------

\# 3. Parameters for LCRD v2

--------------------------------------------------------------------



We introduce three main couplings:



&nbsp;   G\_phase    ≥ 0  # weight for phase Laplacian term in F\_theta

&nbsp;   G\_density  ≥ 0  # weight for density-driven phase term in F\_theta

&nbsp;   G\_coh      ≥ 0  # weight for coherence-like regularization in F\_n



We also allow an optional small diffusion-like term:



&nbsp;   nu\_n ≥ 0  # density diffusion coefficient



Background density for comparison:



&nbsp;   rho0 = 1  # in the CRFT comparison regime used so far



These parameters will be tuned so that:



\- IR calibration (g\_eff at small k, small amplitude) is preserved.

\- The effective g\_eff(k) becomes more uniform on a small-k band.

\- Coarse-grained mass and energy remain well conserved.



--------------------------------------------------------------------

\# 4. Candidate Phase Update F\_theta

--------------------------------------------------------------------



Design principles for F\_theta:



1\. Respect U(1) symmetry:

&nbsp;  F\_theta depends only on gradients of theta and local densities,

&nbsp;  not on absolute theta.



2\. Provide:

&nbsp;  - a discrete phase Laplacian term (controls dispersion and smoothing),

&nbsp;  - a density-driven term analogous to + g ρ in CRFT (controls

&nbsp;    effective nonlinearity),

&nbsp;  - optional mild damping of high-k noise via coherence coupling.



We propose:



&nbsp;   F\_theta(j; n, theta) =

&nbsp;         - G\_density \* (n\_j - rho0)

&nbsp;         + G\_phase   \* lap\_theta\_j



Notes:



\- The G\_density term enforces a local relation between phase acceleration

&nbsp; and deviations of density from rho0, roughly analogous to how the

&nbsp; CRFT phase equation involves g ρ.



\- The G\_phase \* lap\_theta\_j term introduces a controllable dispersion-like

&nbsp; and smoothing effect at the micro level, which can be tuned to shape

&nbsp; the small-k dispersion band.



\- Additional higher-order terms (e.g. discrete fourth derivatives of theta)

&nbsp; are intentionally not included at this design stage to keep LCRD v2

&nbsp; as simple as possible.



--------------------------------------------------------------------

\# 5. Candidate Density Update F\_n

--------------------------------------------------------------------



Design principles for F\_n:



1\. Leading term should be a discrete continuity form:

&nbsp;  F\_n ≈ − ∂x(ρ v) at micro level, so that coarse-grained mass is conserved.



2\. Coherence regularization should:

&nbsp;  - act via Laplacian of n\_j to suppress short-wavelength noise,

&nbsp;  - keep the global sum of n\_j unchanged (mass conservation),

&nbsp;  - be tunable via G\_coh.



3\. Optional diffusion term nu\_n \* lap\_n\_j can help with numerical

&nbsp;  robustness without breaking mass conservation.



We propose:



&nbsp;   F\_n(j; n, theta) =

&nbsp;         - div\_J\_j

&nbsp;         + G\_coh \* lap\_n\_j

&nbsp;         + nu\_n  \* lap\_n\_j



Thus:



&nbsp;   F\_n(j; n, theta) = - div\_J\_j + (G\_coh + nu\_n) \* lap\_n\_j



Key properties:



\- The continuity-like term −div\_J\_j enforces a discrete analog of

&nbsp; ρ\_t + ∂x(ρ v) = 0.



\- The lap\_n\_j term is mass-conserving under periodic BCs:

&nbsp;     sum\_j lap\_n\_j = 0

&nbsp; so it redistributes density but does not change the total.



\- G\_coh controls how strongly short-scale density fluctuations are

&nbsp; penalized (coherence-promoting effect).



\- nu\_n is a purely numerical diffusion parameter. In principle we can

&nbsp; set nu\_n = 0 if G\_coh suffices for stability.



--------------------------------------------------------------------

\# 6. Summary of LCRD v2 Update Equations

--------------------------------------------------------------------



Microscopic updates (candidate):



&nbsp;   n\_j(t + dt)     = n\_j(t)     + dt \* F\_n(j; n, theta)



&nbsp;   theta\_j(t + dt) = theta\_j(t) + dt \* F\_theta(j; n, theta)



with



&nbsp;   F\_theta(j; n, theta) =

&nbsp;         - G\_density \* (n\_j - rho0)

&nbsp;         + G\_phase   \* lap\_theta\_j



&nbsp;   F\_n(j; n, theta) =

&nbsp;         - div\_J\_j

&nbsp;         + (G\_coh + nu\_n) \* lap\_n\_j



and stencils:



&nbsp;   grad\_theta\_j\_plus  = (theta\_{j+1} - theta\_j)     / ε

&nbsp;   grad\_theta\_j\_minus = (theta\_j - theta\_{j-1})     / ε



&nbsp;   n\_half\_j\_plus      = 0.5 \* (n\_j + n\_{j+1})

&nbsp;   n\_half\_j\_minus     = 0.5 \* (n\_{j-1} + n\_j)



&nbsp;   J\_half\_j\_plus      = n\_half\_j\_plus  \* grad\_theta\_j\_plus

&nbsp;   J\_half\_j\_minus     = n\_half\_j\_minus \* grad\_theta\_j\_minus



&nbsp;   div\_J\_j            = (J\_half\_j\_plus - J\_half\_j\_minus) / ε



&nbsp;   lap\_n\_j            = (n\_{j+1} - 2 n\_j + n\_{j-1}) / ε²

&nbsp;   lap\_theta\_j        = (theta\_{j+1} - 2 theta\_j + theta\_{j-1}) / ε²



All indices are taken modulo N (periodic boundaries).



--------------------------------------------------------------------

\# 7. Expected Continuum Mapping (Qualitative Only)

--------------------------------------------------------------------



Under coarse-graining (block size b) and for small gradients:



\- The continuity-like part of F\_n should approximate:

&nbsp;     ρ\_t + ∂x(ρ v) ≈ 0



\- The phase equation should approximate:

&nbsp;     θ\_t ≈ - g\_eff ρ + (phase dispersion terms)



where g\_eff and the higher-derivative coefficients (effective lam, beta)

are emergent functions of:



&nbsp;   G\_phase, G\_density, G\_coh, nu\_n, ε, dt, block\_size



The design target is:



\- In the IR limit (k small, small amplitude), g\_eff ≈ 0.1666456,

&nbsp; matching the CRFT calibration from LCRD v1.



\- Across a small-k band (e.g. first few modes), the effective g\_eff(k)

&nbsp; is significantly more uniform than for LCRD v1, and any additional

&nbsp; k-dependence can be absorbed into effective lam and beta in the CRFT

&nbsp; dispersion.



--------------------------------------------------------------------

\# 8. Next Steps (Beyond This Document)

--------------------------------------------------------------------



This document finalizes the \*\*candidate form\*\* of LCRD v2 dynamics.

The next steps (in separate files) are:



1\. Define test plan:

&nbsp;  - `ft\_step7\_lcrd\_v2\_test\_plan.md`

&nbsp;  - with CG-T8–CG-T11 (bandwise dispersion, coherence sensitivity, mixed-mode

&nbsp;    dynamics, long-time invariants).



2\. Choose initial trial values for:

&nbsp;  - G\_phase, G\_density, G\_coh, nu\_n, rho0

&nbsp;  - such that the model starts close to LCRD v1 behavior, then tune.



3\. Implement LCRD v2 in the simulation engine:

&nbsp;  - Add a selectable “v2” update in the stepper implementation,

&nbsp;    alongside the existing v1 update.



4\. Run and document:

&nbsp;  - Reproduce IR tests (CG-T1–CG-T4) with v2.

&nbsp;  - Execute new CG-T8–CG-T11 tests.



Only after those steps will we decide whether LCRD v2 is an acceptable

candidate micro model aligned with CRFT.



