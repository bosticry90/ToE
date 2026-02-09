\# FT Step-7 — Coherence-Corrected LCRD v2 Design

Document: `ft\_step7\_lcrd\_v2\_design.md`



Parent documents:

\- `equation\_inventory\_finalv4.md`

\- `state\_of\_the\_theoryv4.md`

\- `ft\_step5\_lcrd\_simulation\_engine.md`

\- `ft\_step6\_nonlinear\_multiscale\_calibration.md`

\- `ft\_candidate\_algebra\_01\_\*` (LCRD v1 algebra, mapping, IR calibration)



Status: Design stage only. No implementation or validation yet.



--------------------------------------------------------------------

\# 1. Goal of LCRD v2

--------------------------------------------------------------------



LCRD v1 has been calibrated to:



\- Match CRFT linear dispersion at a reference IR mode (mode\_index = 1) with

&nbsp; g\_eff ≈ 0.1666456 for rho0 = 1, lam = 0, beta = 0.

\- Preserve coarse-grained mass and energy to very high accuracy.

\- Show stable nonlinear and long-time dynamics within the tested regime.



However, g\_eff extracted from higher modes shows strong k-dependence,

and the mapping from micro-parameters (G, C\_coh, etc.) to CRFT parameters

(g, lam, beta) is not yet cleanly scale-independent.



\*\*LCRD v2 is intended to:\*\*



1\. Preserve all validated IR properties of LCRD v1.

2\. Reduce the k-dependence of g\_eff across a small band of low modes.

3\. Introduce an explicit control knob for coherence regularization that is

&nbsp;  more directly interpretable in CRFT terms (e.g., effective lam, beta).

4\. Maintain numerical stability and invariant conservation at least as well

&nbsp;  as LCRD v1.



This is a \*\*design document\*\*. All equations here are \*candidate dynamics\*,

not yet part of the canonical CRFT inventory.



--------------------------------------------------------------------

\# 2. Recap: LCRD v1 Design Constraints

--------------------------------------------------------------------



LCRD v1 is a local rotor–density model:



\- Sites j = 0, 1, ..., N−1 on a 1D lattice, spacing ε.

\- Microscopic DOFs:

&nbsp;   n\_j ≥ 0       (density-like)

&nbsp;   θ\_j           (phase-like)

&nbsp;   u\_j = exp(i θ\_j)

&nbsp;   z\_j = sqrt(n\_j) u\_j



\- Coarse-graining (block size b):

&nbsp;   ρ\_I ≈ average of n\_j in block I

&nbsp;   θ\_I ≈ wrapped average of θ\_j in block I

&nbsp;   φ\_I ≈ sqrt(ρ\_I) exp(i θ\_I)



LCRD v1 dynamics were chosen to be:



\- Local in space.

\- Approximately norm-preserving at micro level.

\- Tunable through a small set of parameters:

&nbsp;   A1, A2, A3 (microscopic couplings, set to 0 in the validated configuration)

&nbsp;   G, C\_coh   (interaction and coherence couplings)

&nbsp;   ε, b, dt    (discretization parameters)



Step-5 and Step-6 showed that, with a specific choice:



\- A1 = A2 = A3 = 0

\- G = 12.5

\- C\_coh = −12.5

\- ρ0 = 1

\- N = 512, ε = 1, L = 512, dt = 0.001, block\_size = 4



we obtain excellent IR and weakly nonlinear behavior but strong

k-dependence at higher modes.



--------------------------------------------------------------------

\# 3. Design Requirements for LCRD v2

--------------------------------------------------------------------



LCRD v2 must satisfy:



R1. \*\*IR retention\*\*  

&nbsp;   Reproduce the same IR calibration as LCRD v1:

&nbsp;   g\_eff ≈ 0.1666456 at the reference mode and amplitude, with

&nbsp;   similar or better mass/energy conservation.



R2. \*\*Small-k band uniformity\*\*  

&nbsp;   For a band of low modes (e.g. mode\_index = 1–4 or 1–6),

&nbsp;   g\_eff(k) should vary much less than in LCRD v1 for the same micro

&nbsp;   parameter set and coarse-graining.



R3. \*\*Controlled coherence regularization\*\*  

&nbsp;   The role of coherence-like terms should be exposed as a tunable

&nbsp;   parameter with a clear mapping to CRFT dispersion or coherence functionals

&nbsp;   (e.g., effective lam, beta, or effective coherence penalty).



R4. \*\*Numerical robustness\*\*  

&nbsp;   Long-time drift of coarse-grained mass and energy should remain

&nbsp;   at or below the drift levels seen in Step-5 and Step-6.



R5. \*\*Minimal increase in model complexity\*\*  

&nbsp;   LCRD v2 should remain “micro-simple”: nearest-neighbor or short-range

&nbsp;   interactions, no global couplings, and computational cost comparable

&nbsp;   to v1.



--------------------------------------------------------------------

\# 4. Design Levers for LCRD v2

--------------------------------------------------------------------



We restrict ourselves to the same DOFs (n\_j, θ\_j). We adjust:



1\. \*\*Phase dynamics\*\*  

&nbsp;  Add or modify discrete Laplacian-like and higher-order phase couplings

&nbsp;  to better approximate CRFT dispersion across multiple k modes.



2\. \*\*Density dynamics\*\*  

&nbsp;  Refine the way density responds to gradients of θ\_j and local deviations

&nbsp;  from ρ0 to control k-dependent stiffness.



3\. \*\*Coherence term\*\*  

&nbsp;  Introduce an explicit coherence-regularization term that is closer to

&nbsp;  the continuum functional C\[φ] = (ρ − ρ0)² or analogous gradient penalties.



4\. \*\*Parameterization\*\*  

&nbsp;  Split the single pair (G, C\_coh) into a small number of \*\*separate

&nbsp;  knobs\*\*:

&nbsp;  - G\_phase   — phase–phase coupling

&nbsp;  - G\_density — density–density or density–phase coupling

&nbsp;  - G\_coh     — coherence penalty strength



--------------------------------------------------------------------

\# 5. Candidate LCRD v2 Update Structure

--------------------------------------------------------------------



We keep the general form:



n\_j(t + dt)   = n\_j(t)   + dt F\_n(n, θ; parameters)

θ\_j(t + dt)   = θ\_j(t)   + dt F\_θ(n, θ; parameters)



We only sketch qualitative structure; exact discrete stencils will be

decided in the implementation stage:



F\_θ(n, θ; parameters) includes:

&nbsp;   • a discrete Laplacian in θ\_j (phase diffusion)

&nbsp;   • a density-weighted term analogous to g ρ in CRFT

&nbsp;   • a coherence-regularization term that suppresses rapid local deviations

&nbsp;     of n\_j from ρ0



F\_n(n, θ; parameters) includes:

&nbsp;   • a discrete divergence of a discrete current J\_j analogous to ρ v

&nbsp;   • optional small “regularization” terms to stabilize high-k noise,

&nbsp;     tuned to remain conservative at coarse level



We introduce explicit coupling constants:



\- G\_phase: weight for the discrete Laplacian in θ

\- G\_density: weight for density-driven phase terms

\- G\_coh: weight for coherence-driven corrections



The LCRD v2 design goal is to identify a region in (G\_phase, G\_density, G\_coh)

space where:



\- IR calibration is preserved,

\- g\_eff(k) is significantly more uniform across a low-k band,

\- invariants remain well conserved.



--------------------------------------------------------------------

\# 6. Mapping Strategy to CRFT Parameters

--------------------------------------------------------------------



LCRD v2 will still be calibrated against the CRFT dispersion:



ω²(k) = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶



Design strategy for mapping:



1\. Fix rho0 = 1 in CRFT comparison.

2\. IR step:

&nbsp;  - Use a reference mode (e.g. mode\_index = 1) to re-fit g\_eff as in

&nbsp;    LCRD v1 and match it to the CRFT g (as before).

3\. Band step:

&nbsp;  - Extract g\_eff(k) for several low modes, e.g. k modes 1–4 or 1–6.

&nbsp;  - Fit lam and beta (if needed) so that the CRFT dispersion matches the

&nbsp;    LCRD v2 measured ω(k) over this band.

&nbsp;  - Evaluate the residual k-dependence beyond what can be captured by

&nbsp;    (g, lam, beta).



The design is considered successful at this stage if:



\- g\_eff remains close to the IR value across the band,

\- the fitted (lam, beta) are modest and relatively stable under small

&nbsp; changes in micro parameters, and

\- residuals between measured ω(k) and CRFT dispersion remain small.



--------------------------------------------------------------------

\# 7. Planned Test Suite for LCRD v2

--------------------------------------------------------------------



We will introduce new tests:



\- CG-T8 — Bandwise dispersion calibration (multi-k fit)

\- CG-T9 — Coherence sensitivity (vary G\_coh)

\- CG-T10 — Mixed-mode dynamics with coherence (extension of CG-T6)

\- CG-T11 — Long-time, multi-mode invariant drift



Each test will re-use the existing CG infrastructure where possible

and only adjust:



\- Micro-level update (stepper implementation)

\- Parameter sets and initial conditions



Design principle:

&nbsp;   LCRD v1 is kept as a frozen reference configuration.  

&nbsp;   LCRD v2 is introduced in parallel as a new “engine,” not as a

&nbsp;   replacement, so we can directly compare v1 vs v2 for the same

&nbsp;   CG tests.



--------------------------------------------------------------------

\# 8. Output of Step-7

--------------------------------------------------------------------



The expected concrete outputs of FT Step-7 are:



1\. A finalized LCRD v2 update rule with:

&nbsp;  - explicit F\_n, F\_θ functional forms,

&nbsp;  - explicit parameter list (G\_phase, G\_density, G\_coh, etc.).



2\. A mapping specification:

&nbsp;  - how to infer (g, lam, beta) from measured ω(k) for LCRD v2.



3\. A proposed default parameter set:

&nbsp;  - analogous to the LCRD v1 default (G = 12.5, C\_coh = −12.5),

&nbsp;    but now in terms of (G\_phase, G\_density, G\_coh).



4\. A plan for implementing tests CG-T8–CG-T11,

&nbsp;  to be executed in FT Step-8.



This document closes when:

\- the v2 update equations and parameters are chosen,

\- the test definitions are locked,

\- and no further conceptual design changes are needed.



Implementation details and numerical tuning are deferred to the next step.



