\# FT Step 4 — Coarse-Graining Verification Harness

\_Last updated: 2025-11-27\_



Aligned with:

\- ft\_step3\_composition\_algebra.md

\- ft\_candidate\_algebra\_01\_local\_rotor\_density.md

\- ft\_candidate\_algebra\_01\_dynamics.md

\- ft\_candidate\_algebra\_01\_numerics.md

\- CRFT equation\_inventory\_final.md

\- state\_of\_the\_theory.md



---



\## 1. Purpose and Scope



This document specifies the \*\*Step-4 coarse-graining verification harness\*\* for the Fundamental Theory (FT) program.



The harness provides a \*\*candidate-agnostic test framework\*\* that:



1\. Takes a microscopic model (e.g., LCRD Candidate 01) with well-defined local dynamics.

2\. Coarse-grains its micro degrees of freedom into an emergent complex field \\(\\phi(x,t)\\).

3\. Compares the emergent dynamics against the \*\*canonical CRFT theory\*\*:

&nbsp;  - CP-NLSE and CE-NWE equations of motion.

&nbsp;  - Hydrodynamic continuity and phase dynamics.

&nbsp;  - Dispersion relation

&nbsp;    \\\[

&nbsp;    \\omega^2(k) = (k^2/2)^2 + g\\rho\_0 k^2 + \\lambda k^4 + \\beta k^6.

&nbsp;    \\]

&nbsp;  - Coherence penalty behavior.

&nbsp;  - Solitons, turbulence, and coherence metrics.



The goal is to determine whether a given microscopic algebra + dynamics can legitimately be considered a \*\*fundamental-theory candidate\*\* for CRFT.



---



\## 2. Conceptual Architecture



\### 2.1 Layers



The harness organizes the FT program into three layers:



1\. \*\*Microscopic layer (FT candidate)\*\*  

&nbsp;  - Example: LCRD (Local Complex Rotor–Density Algebra).

&nbsp;  - DOFs: \\(n\_j, u\_j = e^{i\\theta\_j}, z\_j = \\sqrt{n\_j}\\,u\_j\\).

&nbsp;  - Local dynamics: density exchange + phase update.



2\. \*\*Coarse-graining layer\*\*  

&nbsp;  - Blocks or filters micro-DOFs into a complex field:

&nbsp;    \\\[

&nbsp;    \\phi(x,t) \\approx \\Phi\_B = \\frac{1}{|B|}\\sum\_{j\\in B} z\_j.

&nbsp;    \\]

&nbsp;  - Extracts \\(\\rho = |\\phi|^2\\), \\(\\theta = \\arg\\phi\\), \\(v = \\theta\_x\\).



3\. \*\*CRFT reference layer (surface theory)\*\*  

&nbsp;  - Canonical equations: CP-NLSE, CE-NWE, hydrodynamics, dispersion, coherence functionals.

&nbsp;  - Provides analytic and numerical reference for all tests.



\### 2.2 Components



The harness is defined around four core components:



1\. \*\*Micro Model API\*\* (per candidate)  

2\. \*\*Coarse-Graining Operator\*\* (candidate-agnostic)  

3\. \*\*Diagnostics and Metrics\*\* (CRFT-aligned)  

4\. \*\*Test Suite\*\* (Step-4 verification tests)



---



\## 3. Micro Model API Specification



Any microscopic FT candidate must implement the following conceptual interface.



\### 3.1 Configuration Object



`MicroConfig` should contain:



\- Lattice parameters:

&nbsp; - `N` (number of sites),

&nbsp; - `epsilon` (lattice spacing),

&nbsp; - `dt` (time step),

&nbsp; - `boundary\_condition` (typically periodic).

\- Physical parameters (mapped to CRFT params where possible):

&nbsp; - `g, lambda, beta, rho0, lambda\_coh, hbar, m, c, xi`.

\- Candidate-specific internal parameters:

&nbsp; - e.g., flux coefficients \\((A\_1, A\_2, A\_3)\\),

&nbsp; - nonlinear coefficients \\((G, C\_coh)\\),

&nbsp; - any spinor or internal-symmetry parameters (for other candidates).



\### 3.2 Micro State



`MicroState` must encode all DOFs needed to evolve the system:



\- For LCRD:

&nbsp; - arrays `n\[j]`, `theta\[j]`, derived `u\[j] = exp(i\*theta\[j])`, `z\[j] = sqrt(n\[j])\*u\[j]`.



For other candidates, the analogous micro arrays (e.g., spinors, graph states) must be exposed.



\### 3.3 Required Functions



Each candidate must supply functions with the following semantics:



1\. `initialize\_state(config, mode, seed) -> MicroState`  

&nbsp;  - `mode` selects the initial condition:

&nbsp;    - `"uniform"` (background state),

&nbsp;    - `"single\_mode"` (single sinusoidal perturbation),

&nbsp;    - `"bump"` (localized density feature),

&nbsp;    - `"random"` (turbulent initial condition),

&nbsp;    - `"soliton\_like"` (approximate soliton seed).



2\. `step\_micro(state, config, dt) -> MicroState`  

&nbsp;  - Performs one micro time step using the candidate’s dynamics.

&nbsp;  - Must preserve total density (up to numerical error).



3\. `coarse\_grain(state, config, B) -> FieldSnapshot`  

&nbsp;  - `B` is block size (number of sites per block).

&nbsp;  - Returns:

&nbsp;    - `phi(x)` (complex field on a coarse grid),

&nbsp;    - `rho(x) = |phi|^2`,

&nbsp;    - `theta(x) = arg(phi)`,

&nbsp;    - `v(x) = d(theta)/dx` (e.g., spectral or finite-difference derivative).



4\. `compute\_micro\_invariants(state, config) -> dict`  

&nbsp;  - Returns quantities like:

&nbsp;    - total density \\(\\sum\_j n\_j\\),

&nbsp;    - mean phase or circulation,

&nbsp;    - any candidate-specific invariants.



These functions are conceptual; implementations can be in Python/NumPy or other languages as long as they obey these semantics.



---



\## 4. Coarse-Graining Operator



The harness defines a candidate-agnostic coarse-graining operator that:



1\. Partitions the lattice into blocks \\(B\\) of size \\(|B|\\).

2\. Computes block-averaged complex amplitude:

&nbsp;  \\\[

&nbsp;  \\Phi\_B = \\frac{1}{|B|}\\sum\_{j\\in B} z\_j.

&nbsp;  \\]

3\. Defines emergent field values:

&nbsp;  - \\(\\phi(x) = \\Phi\_B\\),

&nbsp;  - \\(\\rho(x) = |\\phi(x)|^2\\),

&nbsp;  - \\(\\theta(x) = \\arg\\phi(x)\\),

&nbsp;  - \\(v(x) = \\theta\_x(x)\\).



This is consistent with the LCRD coarse-graining map and the CRFT hydrodynamic interpretation.



---



\## 5. CRFT Reference Diagnostics



The harness uses CRFT as the reference theory. Key diagnostics:



1\. \*\*Dispersion\*\*  

&nbsp;  - Measured \\(\\omega(k)\\) vs predicted:

&nbsp;    \\\[

&nbsp;    \\omega^2(k) = (k^2/2)^2 + g\\rho\_0 k^2 + \\lambda k^4 + \\beta k^6.

&nbsp;    \\]



2\. \*\*Continuity Residual\*\*  

&nbsp;  - For coarse-grained fields:

&nbsp;    \\\[

&nbsp;    R\_{\\text{cont}} = \\rho\_t + (\\rho v)\_x.

&nbsp;    \\]



3\. \*\*Nonlinearity\*\*  

&nbsp;  - Extract effective nonlinear term from amplitude-dependent frequency shift and compare to \\(g|\\phi|^2\\phi\\).



4\. \*\*Coherence Penalty\*\*  

&nbsp;  - Measure relaxation of deviations \\(|\\phi|^2 - \\rho\_0\\) and fit effective restoring term consistent with \\(\\lambda\_{\\text{coh}}(|\\phi|^2 - \\rho\_0)\\phi\\).



5\. \*\*Soliton Metrics\*\*  

&nbsp;  - Shape, speed, and stability of localized structures vs CRFT soliton templates.



6\. \*\*Turbulence \& Spectral Metrics\*\*  

&nbsp;  - Structure factor \\(S(k)\\), spectral centroid, roughness, coherence energy.



7\. \*\*Coherence Metrics \& Correlation Lengths\*\*  

&nbsp;  - \\(g\_1(r)\\), \\(\\xi\\), \\(\\xi\_k\\), PCI, SCI, variance metrics.



These diagnostics are borrowed directly from the CRFT equation inventory and state-of-the-theory documents.



---



\## 6. Step-4 Test Suite (Candidate-Agnostic)



Each test is identified as CG-Tn and is defined at the level of the harness. Candidate-specific details (e.g., LCRD, LSDA) are plugged into the same templates.



\### CG-T1 — Linear Dispersion Recovery



\*\*Goal\*\*  

Verify that the emergent field \\(\\phi(x,t)\\) exhibits the CRFT dispersion relation in the small-amplitude, near-uniform regime.



\*\*Setup\*\*



\- Use `mode = "single\_mode"` with:

&nbsp; - uniform background near \\(\\rho\_0\\),

&nbsp; - small sinusoidal perturbation at selected wavenumber \\(k\\).

\- Simulate micro dynamics for many oscillation periods.



\*\*Procedure\*\*



1\. Initialize `state = initialize\_state(config, "single\_mode", seed)`.

2\. For each time step:

&nbsp;  - Evolve: `state = step\_micro(state, config, dt)`.

&nbsp;  - At selected intervals, coarse-grain: `phi = coarse\_grain(state, config, B)`.

3\. Extract \\(|\\phi(x,t)|\\) at each time and perform a temporal Fourier transform at the mode \\(k\\).

4\. Fit \\(\\omega(k)\\) from the oscillation.



\*\*Diagnostics\*\*



\- Compare measured \\(\\omega^2(k)\\) with:

&nbsp; \\\[

&nbsp; \\omega^2\_{\\text{CRFT}}(k) = (k^2/2)^2 + g\\rho\_0 k^2 + \\lambda k^4 + \\beta k^6.

&nbsp; \\]



\*\*Pass Criteria\*\*



\- Relative error in each coefficient \\((g,\\lambda,\\beta)\\) within tolerances under refinement of \\(\\epsilon\\) and \\(\\Delta t\\).

\- No spurious branches or unstable modes in the linear regime.



---



\### CG-T2 — Continuity and Hydrodynamic Structure



\*\*Goal\*\*  

Confirm that emergent \\(\\rho\\) and \\(v\\) satisfy the CRFT continuity equation.



\*\*Setup\*\*



\- `mode = "bump"`: localized density enhancement on a uniform background.

\- Track the evolution of the density bump.



\*\*Procedure\*\*



1\. Initialize a localized bump in `n\_j`.

2\. Evolve micro dynamics and coarse-grain at regular intervals.

3\. Compute \\(\\rho\_t\\) from finite differences in time.

4\. Compute \\((\\rho v)\_x\\) from spatial derivatives.

5\. Evaluate residual:

&nbsp;  \\\[

&nbsp;  R\_{\\text{cont}} = \\rho\_t + (\\rho v)\_x.

&nbsp;  \\]



\*\*Pass Criteria\*\*



\- Norm of \\(R\_{\\text{cont}}\\) decreases under refinement of \\(\\epsilon, \\Delta t\\).

\- Global density conservation holds to numerical accuracy.



---



\### CG-T3 — Nonlinearity Emergence



\*\*Goal\*\*  

Demonstrate that the emergent dynamics produce an effective cubic nonlinearity consistent with \\(g|\\phi|^2\\phi\\).



\*\*Setup\*\*



\- `mode = "single\_mode"` but with varying amplitudes.

\- Same wavenumber \\(k\\), multiple amplitude levels.



\*\*Procedure\*\*



1\. For each amplitude \\(A\\):

&nbsp;  - Initialize perturbation with amplitude \\(A\\).

&nbsp;  - Run micro simulation and measure effective frequency \\(\\omega\_{\\text{eff}}(A)\\).

2\. Fit the dependence of \\(\\omega\_{\\text{eff}}\\) on amplitude.



\*\*Diagnostics\*\*



\- Compare fitted nonlinear contribution with CRFT expectation for focusing/defocusing regimes.



\*\*Pass Criteria\*\*



\- Effective nonlinearity scales as \\(|\\phi|^2\\phi\\) within tolerance.

\- Sign and rough magnitude match CRFT parameter \\(g\\).



---



\### CG-T4 — Coherence Penalty Emergence



\*\*Goal\*\*  

Check whether deviations from uniform density relax according to an effective coherence penalty consistent with \\(\\lambda\_{\\text{coh}}(|\\phi|^2 - \\rho\_0)\\phi\\).



\*\*Setup\*\*



\- `mode = "bump"` or `"hole"`: local over- or under-density relative to \\(\\rho\_0\\).



\*\*Procedure\*\*



1\. Initialize local deviations in \\(n\_j\\).

2\. Track \\(|\\phi|^2 - \\rho\_0\\) over time in coarse-grained fields.

3\. Fit relaxation timescales and functional dependence on amplitude.



\*\*Pass Criteria\*\*



\- Relaxation is approximately exponential for small deviations.

\- Effective restoring term is proportional to \\(|\\phi|^2 - \\rho\_0\\) with coefficient compatible with \\(\\lambda\_{\\text{coh}}\\) under parameter mappings.



---



\### CG-T5 — Soliton-Like Structures



\*\*Goal\*\*  

Test whether the microscopic candidate supports coherent, localized structures whose coarse-grained behavior matches CRFT soliton templates.



\*\*Setup\*\*



\- `mode = "soliton\_like"`:

&nbsp; - dark- or bright-soliton-like profile in \\(n\_j\\) and \\(\\theta\_j\\), constructed from CRFT profiles.



\*\*Procedure\*\*



1\. Initialize approximate soliton in `MicroState`.

2\. Evolve micro dynamics and coarse-grain at many consecutive times.

3\. Measure soliton shape, speed, and stability in \\(\\phi(x,t)\\).



\*\*Diagnostics\*\*



\- Compare with analytic CRFT soliton shapes and velocities.

\- Measure amplitude and width drift over time.



\*\*Pass Criteria\*\*



\- Soliton retains shape and speed over many characteristic times.

\- Deviation in width and amplitude is bounded and decreases with refinement.



---



\### CG-T6 — Turbulence and Spectral Cascades



\*\*Goal\*\*  

Assess whether the candidate reproduces CRFT-like turbulence and spectral behavior at the coarse-grained level.



\*\*Setup\*\*



\- `mode = "random"`:

&nbsp; - random initial phases and densities within a specified range.



\*\*Procedure\*\*



1\. Initialize random configuration.

2\. Evolve micro dynamics until a statistical steady state is reached.

3\. At multiple times, coarse-grain and compute:

&nbsp;  - structure factor \\(S(k)\\),

&nbsp;  - spectral centroid,

&nbsp;  - roughness,

&nbsp;  - coherence energy,

&nbsp;  - mass drift.



\*\*Pass Criteria\*\*



\- Qualitative match of spectral shape and evolution to CRFT turbulence diagnostics.

\- No numerical pathologies or unphysical divergences.



---



\### CG-T7 — Coherence Metrics and Correlation Functions



\*\*Goal\*\*  

Compare emergent coherence metrics against CRFT definitions and behaviors.



\*\*Setup\*\*



\- Use outputs from CG-T5 and CG-T6.



\*\*Procedure\*\*



For each scenario:



1\. Compute:

&nbsp;  - \\(g\_1(r)\\),

&nbsp;  - correlation length \\(\\xi\\),

&nbsp;  - spectral coherence length \\(\\xi\_k\\),

&nbsp;  - PCI, SCI,

&nbsp;  - variance of \\(\\rho\\) and \\(\\phi\\).

2\. Compare scaling with changes in parameters (e.g., \\(\\lambda\_{\\text{coh}}\\), \\(g\\)) to CRFT expectations.



\*\*Pass Criteria\*\*



\- Monotonic and qualitative trends in coherence metrics match those of CRFT.

\- Multisoliton configurations show convergence behavior analogous to CRFT multisoliton scans, where applicable.



---



\### CG-T8 — Stability and Convergence



\*\*Goal\*\*  

Establish numerical robustness of the candidate under mesh, timestep, and parameter refinement.



\*\*Setup\*\*



\- Repeat selected tests (CG-T1, T2, T5, T6) at multiple:

&nbsp; - `epsilon` (spatial resolution),

&nbsp; - `dt` (timestep),

&nbsp; - block sizes `B`.



\*\*Procedure\*\*



1\. For each resolution set, run the chosen tests.

2\. Track:

&nbsp;  - conservation of micro invariants (e.g., total density),

&nbsp;  - stability (absence of blow-up or spurious oscillations),

&nbsp;  - convergence of diagnostics (e.g., dispersion coefficients, continuity residuals).



\*\*Pass Criteria\*\*



\- Diagnostic errors decrease with refinement.

\- Stability region is compatible with standard CFL-like constraints.

\- Coarse-graining results are robust with respect to modest changes in block size.



---



\## 7. Candidate-Specific Instantiation: LCRD (Candidate 01)



For LCRD, the Micro Model API is instantiated as:



\- `state.n\[j]` — micro density.

\- `state.theta\[j]` — rotor phase.

\- `state.u\[j] = exp(1j \* theta\[j])`.

\- `state.z\[j] = sqrt(n\[j]) \* u\[j]`.



Dynamics:



\- `step\_micro` uses:

&nbsp; - conservative density flux with coefficients \\((A\_1, A\_2, A\_3)\\) to reproduce CRFT dispersion up to \\(k^6\\),

&nbsp; - phase update including gradient terms, nonlinear term \\(-G n\_j\\), and coherence-like term \\(-C\_coh(n\_j - n\_0)\\).



Coarse-graining:



\- `coarse\_grain` uses block average of `z\[j]` to produce \\(\\phi(x)\\), then derives \\(\\rho, \\theta, v\\).



LCRD is therefore directly pluggable into CG-T1…CG-T8 without modification.



---



\## 8. Output, Logging, and Reproducibility



The harness should:



\- Record:

&nbsp; - micro configuration (seed, parameters),

&nbsp; - configuration of coarse-graining (block size, resolution),

&nbsp; - all diagnostics and residuals for each test.

\- Use deterministic random seeds to ensure reproducibility.

\- Store outputs in structured formats (e.g., JSON + HDF5/NPZ) for later analysis.



---



\## 9. Summary



The Step-4 coarse-graining harness defined here:



\- Provides a \*\*candidate-independent test suite\*\* grounded in the canonical CRFT theory.

\- Specifies \*\*clear interfaces\*\* that any microscopic algebra + dynamics must satisfy.

\- Supplies \*\*concrete tests\*\* for dispersion, continuity, nonlinearity, coherence penalty, solitons, turbulence, and coherence metrics.

\- Enables a disciplined decision: whether a given FT candidate can be regarded as a valid microscopic realization of the CRFT scalar field theory.



This document is intended to be the central reference for all subsequent \*\*fundamental-theory validation work\*\* in the CRFT program.



