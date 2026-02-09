\# FT Candidate Algebra 02 — Numerical Experiments

Local Spinor–Density Algebra (LSDA)

Last updated: 2025-11-27



Aligned with:

\- ft\_candidate\_algebra\_02\_local\_spinor\_density.md

\- ft\_candidate\_algebra\_02\_dynamics.md

\- CRFT equation\_inventory\_final.md

\- CRFT state\_of\_the\_theory.md



---



\# 1. Purpose



This document defines the \*\*numerical evaluation program\*\* for LSDA.  

The goal is to determine whether the LSDA microscopic model:



\- reproduces CRFT dispersion,  

\- yields emergent continuity,  

\- produces CRFT nonlinearities and coherence penalty,  

\- supports solitons, turbulence, and coherent structures,  

\- matches CRFT phenomenology in all validated sections.



This evaluates LSDA as a viable fundamental-theory candidate.



---



\# 2. Simulation Setup



Lattice: 1D, spacing \\(\\epsilon\\), periodic boundaries.



Site variable:



\\\[

\\psi\_j(t) \\in \\mathbb{C}^2.

\\]



Time integrator:



\- prototype: Euler / RK2  

\- production: RK4 or symplectic schemes



Block mapping:



\\\[

\\phi(x) = \\Phi\_B = |B|^{-1}\\sum\_{j\\in B}\\langle w,\\psi\_j\\rangle.

\\]



Measured coarse-grained diagnostics:



\- \\(\\rho = |\\phi|^2\\)  

\- \\(\\theta = \\arg\\phi\\)  

\- \\(v = \\theta\_x\\)  

\- spectra \\(|\\hat\\phi(k)|^2\\)  

\- coherence metrics (CRFT Section 12)  

\- soliton metrics (Section 11)  

\- turbulence metrics (Sections 12–13)



---



\# 3. Test 1 — Linear Dispersion



\## Goal

Confirm emergence of:



\\\[

\\omega^2(k)=\\left(\\frac{k^2}{2}\\right)^2 + g\\rho\_0 k^2 + \\lambda k^4 + \\beta k^6.

\\]



\## Procedure

1\. Initialize uniform \\(\\psi\_j = \\psi\_0\\).  

2\. Add small sinusoidal perturbation in the projected scalar \\(\\zeta\_j\\).  

3\. Track oscillations of coarse-grained \\(\\phi(x,t)\\).  

4\. Fourier-analyze for \\(\\omega(k)\\).  

5\. Fit polynomial.



\## Passing Criteria

\- Coefficients match CRFT values.  

\- No extraneous branches.



---



\# 4. Test 2 — Continuity Emergence



\## Goal

Recover macroscopic:



\\\[

\\rho\_t + (\\rho v)\_x = 0.

\\]



\## Procedure

1\. Prepare localized density bump in \\(n\_j\\).  

2\. Evolve under LSDA dynamics.  

3\. Compute coarse-grained \\(\\rho\\), \\(v\\).  

4\. Evaluate residual:



\\\[

R = \\rho\_t + (\\rho v)\_x.

\\]



\## Passing Criteria

\- \\(R\\to 0\\) under refinement of \\(\\epsilon\\) and \\(\\Delta t\\).



---



\# 5. Test 3 — Nonlinearity Recovery



\## Goal

Confirm LSDA reproduces cubic nonlinearity:



\\\[

-i g|\\phi|^2\\phi.

\\]



\## Procedure

1\. Prepare multi-amplitude wave packets.  

2\. Measure frequency shifts vs amplitude.  

3\. Fit effective nonlinearity.



\## Passing Criteria

\- Nonlinearity matches cubic form.  

\- Sign corresponds to defocusing/focusing CRFT regimes.



---



\# 6. Test 4 — Coherence Penalty Emergence



\## Goal

Recover:



\\\[

\\lambda\_{\\rm coh}(|\\phi|^2-\\rho\_0)\\phi.

\\]



\## Procedure

1\. Prepare density deviations in blocks.  

2\. Track relaxation rates.  

3\. Fit effective coherence penalty.



\## Passing Criteria

\- Restoration toward \\(\\rho\_0\\) matches CRFT rates.



---



\# 7. Test 5 — Soliton Emergence



\## Goal

Determine whether LSDA supports soliton structures under coarse-graining.



\## Procedure

1\. Initialize soliton-like defects in \\(\\psi\_j\\).  

2\. Evolve.  

3\. Compute \\(\\phi(x,t)\\).  

4\. Compare with CRFT soliton solutions (Section 11).



\## Passing Criteria

\- Long-lived, shape-preserving envelopes.  

\- Speeds consistent with CRFT dispersion.



---



\# 8. Test 6 — Turbulence and Spectral Behavior



\## Goal

Confirm spinor micro-dynamics yield CRFT-compatible turbulence.



\## Procedure

1\. Initialize random \\(\\psi\_j\\).  

2\. Evolve to steady turbulent regime.  

3\. Measure:

&nbsp;  - spectral centroid

&nbsp;  - roughness

&nbsp;  - coherence energy

&nbsp;  - structure factor \\(S(k)\\)



\## Passing Criteria

\- Qualitative match to CRFT turbulence signatures.  

\- Smooth convergence with grid refinement.



---



\# 9. Test 7 — Coherence Metrics



\## Goal

Compare LSDA emergent fields to CRFT coherence metrics.



\## Procedure

Compute:



\- \\(g\_1(r)\\)  

\- correlation length \\(\\xi\\)  

\- spectral coherence length \\(\\xi\_k\\)  

\- PCI, SCI  

\- variance metrics



\## Passing Criteria

\- Consistent monotonicity with CRFT parameter variations.  

\- Agreement with CRFT’s invariant-scan behavior.



---



\# 10. Stability Studies



Vary:



\- \\(\\epsilon, \\Delta t\\)  

\- coupling strengths \\(G, C\_{\\rm coh}\\)  

\- spinor-rotation parameters \\(\\Omega\_1,\\Omega\_2\\)



Check:



\- conservation of total density  

\- stability of soliton propagation  

\- robustness of turbulence steady state  

\- spectral regularity



---



\# 11. Summary



This document provides the full \*\*numerical validation framework\*\* for Candidate Algebra 02 (LSDA).  

All tests are directly inherited from CRFT’s validated behaviors and apply identically under LSDA coarse-graining.





