\# FT Candidate Algebra 01 — Numerical Experiments

Local Complex Rotor–Density Algebra (LCRD)

Last updated: 2025-11-27



Aligned with:

\- ft\_candidate\_algebra\_01\_local\_rotor\_density.md

\- ft\_candidate\_algebra\_01\_dynamics.md

\- CRFT equation\_inventory\_final.md

\- state\_of\_the\_theory.md



---



\# 1. Purpose



This document defines the \*\*numerical experimental program\*\* for testing whether LCRD dynamics produce CRFT-consistent macroscopic behavior under coarse-graining.



The purpose is not to claim physical interpretation, but to perform:

\- structural tests,

\- dispersion tests,

\- soliton tests,

\- turbulence tests,

\- coherence-metric tests,



so that LCRD can be evaluated as a candidate microscopic substrate for CRFT.



---



\# 2. Discretization and Simulation Setup



We simulate a 1D lattice with spacing \\(\\epsilon\\) and time step \\(\\Delta t\\):



\- Variables: \\(n\_j(t)\\), \\(u\_j(t)=e^{i\\theta\_j(t)}\\), \\(z\_j=\\sqrt{n\_j}\\,u\_j\\)

\- Boundary conditions: periodic unless otherwise stated

\- Lattice size: \\(N\\sim 2^8\\) to \\(2^{14}\\)

\- Solver: explicit Euler or RK2 for prototyping; RK4 or symplectic for refinement



---



\# 3. Coarse-Graining Protocol



Define a block size \\(B\\) (e.g. 8–32 sites).  

The emergent CRFT field is:



\\\[

\\phi(x) = \\Phi\_B = \\frac{1}{|B|}\\sum\_{j\\in B} z\_j.

\\]



Diagnostics computed from \\(\\phi(x)\\):



\- density \\(\\rho = |\\phi|^2\\)

\- phase \\(\\theta = \\arg\\phi\\)

\- velocity \\(v=\\theta\_x\\)

\- spectra \\(\\hat\\phi(k)\\)

\- curvature proxies

\- coherence metrics (CRFT-style)



This ensures strict compatibility with CRFT’s hydrodynamic and spectral definitions.



---



\# 4. Test 1 — Linear Dispersion



\## Goal

Confirm that LCRD dynamics reproduce:



\\\[

\\omega^2 = (k^2/2)^2 + g\\rho\_0 k^2 + \\lambda k^4 + \\beta k^6.

\\]



\## Procedure

1\. Initialize uniform state \\(n\_j=\\rho\_0\\), \\(\\theta\_j=0\\).  

2\. Add small-amplitude sinusoidal perturbation at wavenumber \\(k\\).  

3\. Track oscillation frequency via \\(\\phi(x,t)\\).  

4\. Fit \\(\\omega(k)\\) to the CRFT polynomial.



\## Passing Criteria

\- Polynomial coefficients match \\((g,\\lambda,\\beta)\\) to within numerical error.

\- No spurious modes appear.



---



\# 5. Test 2 — Continuity and Hydrodynamics



\## Goal

Recover macroscopic:



\\\[

\\rho\_t + (\\rho v)\_x = 0.

\\]



\## Procedure

1\. Initialize localized density bump in \\(n\_j\\).  

2\. Track coarse-grained \\(\\rho(x,t)\\), \\(\\theta(x,t)\\), \\(v(x,t)\\).  

3\. Check residual of mass balance:

\\\[

R = \\rho\_t + (\\rho v)\_x.

\\]



\## Passing Criteria

\- \\(R \\rightarrow 0\\) under refinement \\((\\epsilon,\\Delta t\\rightarrow 0)\\).



---



\# 6. Test 3 — Nonlinearity Recovery



\## Goal

Identify whether cubic nonlinearity \\(g|\\phi|^2\\phi\\) emerges.



\## Procedure

1\. Initialize two superimposed waves of different amplitude.  

2\. Track frequency shift vs intensity.  

3\. Fit effective nonlinear term from \\(\\omega\_{\\rm eff}(A)\\).



\## Passing Criteria

\- Effective nonlinearity scales as \\(|\\phi|^2\\phi\\).  

\- Sign corresponds to focusing/defocusing as in CRFT.



---



\# 7. Test 4 — Soliton Emergence



\## Goal

Establish that LCRD supports soliton-like coherent structures under coarse-graining.



\## Procedure

1\. Initialize density dip or bump in \\(n\_j\\).  

2\. Evolve with LCRD dynamics.  

3\. Compute coarse-grained \\(\\phi(x,t)\\).  

4\. Compare with CRFT soliton templates:

&nbsp;  - dark soliton profile,

&nbsp;  - bright soliton profile.



\## Passing Criteria

\- Stable propagation with constant speed and preserved shape.

\- Consistent dispersion relation.



---



\# 8. Test 5 — Turbulence and Spectral Cascades



\## Goal

Determine whether small-scale rotor dynamics drive large-scale turbulence consistent with CRFT.



\## Procedure

1\. Initialize random \\(n\_j\\) and \\(\\theta\_j\\).  

2\. Evolve to statistical steady state.  

3\. Measure:

&nbsp;  - structure factor \\(S(k)\\),

&nbsp;  - spectral centroid,

&nbsp;  - roughness,

&nbsp;  - coherence energies,

&nbsp;  - temporal drift.



\## Passing Criteria

\- Spectral evolution matches CRFT diagnostics in structure (not necessarily amplitude).

\- No unphysical divergences.



---



\# 9. Test 6 — Coherence Functional Behavior



\## Goal

Check reproduction of the emergent quadratic penalty:



\\\[

C = (|\\phi|^2 - \\rho\_0)^2.

\\]



\## Procedure

1\. Initialize blocks with perturbed density.  

2\. Evolve until local densities relax.  

3\. Fit decay timescale vs amplitude.



\## Passing Criteria

\- Effective restoring term proportional to \\(n\_j - n\_0\\).

\- Emergent relaxation matches CRFT coherence-penalty scaling.



---



\# 10. Numerical Stability Exploration



Investigate:



\- CFL-type bounds (\\(\\Delta t \\lesssim \\epsilon^2\\)),

\- parameter regions where LCRD fails to coarse-grain,

\- robustness against noise,

\- dependence on block size.



---



\# 11. Summary



This document specifies the \*\*numerical evaluation framework\*\* for LCRD.  

Successful completion of these tests will determine whether LCRD is a viable microscopic substrate capable of reproducing the validated CRFT theory.





