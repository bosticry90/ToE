\# FT Step-7 — LCRD v2 Test Plan

Document: ft\_step7\_lcrd\_v2\_test\_plan.md  

Status: DESIGN ONLY (no code yet)



Purpose:

\- Define the complete numerical validation suite for LCRD v2.

\- Confirm whether the candidate micro-dynamics F\_n and F\_theta

&nbsp; (as defined in ft\_step7\_lcrd\_v2\_dynamics.md) provide a

&nbsp; coarse-grained model consistent with CRFT across small-k,

&nbsp; moderate-k, and long-time regimes.

\- These tests determine whether LCRD v2 should proceed to Step-8

&nbsp; implementation and calibration, or be revised.



All tests below assume:

&nbsp;   - periodic boundary conditions,

&nbsp;   - microscopic update rules exactly as defined in Step-7,

&nbsp;   - coarse-graining operator identical to Step-5/Step-6,

&nbsp;   - comparison against CRFT’s dispersion and continuity structure.



--------------------------------------------------------------------

\# 0. Inputs and Parameters

--------------------------------------------------------------------



Microscopic LCRD v2 parameters to be scanned or fixed:



&nbsp;   G\_phase

&nbsp;   G\_density

&nbsp;   G\_coh

&nbsp;   nu\_n

&nbsp;   rho0      (default = 1.0)

&nbsp;   epsilon, dt, block\_size

&nbsp;   N, L = N \* epsilon



Initial conditions:

&nbsp;   - low-k sinusoidal phase modes,

&nbsp;   - superpositions of two low-k phase modes,

&nbsp;   - small-amplitude density perturbations,

&nbsp;   - noise-injected density patterns for coherence testing.



Coarse-grained quantities:

&nbsp;   ρ\_I, θ\_I obtained by block averaging over block\_size = 4 (baseline).



CRFT comparison:

&nbsp;   - effective nonlinearity g\_eff\_IR ≈ 0.1666456 (from Step-6),

&nbsp;   - baseline CRFT dispersion in the IR: ω(k) ≈ |k| \* sqrt(g\_eff\_IR),

&nbsp;     since lam = beta = 0 in the current working regime.



--------------------------------------------------------------------

\# 1. Test CG-T8 — Bandwise Dispersion Mapping (Small-k Uniformity)

--------------------------------------------------------------------



Goal:

\- Measure whether g\_eff(k) is more uniform across the first several

&nbsp; lattice modes than in LCRD v1.

\- This is the primary diagnostic for LCRD v2.



Procedure:

1\. For mode\_index m = 1, 2, 3, 4, 5, 6:

&nbsp;      θ\_j(0) = A \* sin(2π m j / N)

&nbsp;      n\_j(0) = rho0

&nbsp;  with A = 0.01 (small amplitude).



2\. Evolve microscopic dynamics using Step-7 F\_n and F\_theta.



3\. Coarse-grain to obtain φ\_I(t), extract ω\_measured(m) from

&nbsp;  time-series φ\_I(t) via FFT or phase-tracking.



4\. Fit effective g\_eff(m) by solving:

&nbsp;      ω\_measured(m) = |k\_m| \* sqrt( g\_eff(m) )

&nbsp;  given k\_m = 2π m / L.



5\. Compute:

&nbsp;      Δg\_eff = max\_m g\_eff(m)  −  min\_m g\_eff(m)



Acceptance criteria (Step-7 design target):

&nbsp;   Δg\_eff < 0.05 \* g\_eff\_IR       # significantly better than v1

&nbsp;   rel\_err(k=1)  < 1e−2           # baseline IR accuracy



Outputs:

\- Table of {m, k\_m, ω\_measured(m), g\_eff(m)}.

\- Δg\_eff summary.

\- pass/fail flag.



--------------------------------------------------------------------

\# 2. Test CG-T9 — Nonlinear Spectral Transfer (Mode Coupling)

--------------------------------------------------------------------



Goal:

\- Examine spectral redistribution under nonlinear LCRD v2 dynamics.

\- Compare strength and pattern of mode coupling to expectations:

&nbsp; subtle, controlled nonlinear interactions without pathological

&nbsp; broadband cascades.



Initial condition:

&nbsp;   θ\_j(0) = A1 \* sin(2π k1 j / N) + A2 \* sin(2π k2 j / N)

&nbsp;   n\_j(0) = rho0

Typical values:

&nbsp;   k1 = 1, k2 = 2

&nbsp;   A1 = A2 = 0.01



Procedure:

1\. Evolve microscopically for t\_final = 10–15 units.



2\. At t = 0 and t = t\_final:

&nbsp;      - coarse-grain n\_j and θ\_j,

&nbsp;      - compute spectral power P(k) over coarse φ\_I.



3\. Compute transfer ratios:

&nbsp;      T(k) = P(k, t\_final) / P(k, 0)



Key diagnostics:

\- Nonzero P(k1±k2) emergence indicates nonlinear coupling.

\- The pattern should be smooth, not explosive.

\- Total spectral power Σ\_k P(k) should remain nearly constant.



Acceptance criteria:

&nbsp;   |Σ\_k P(k,T) − Σ\_k P(k,0)|  < 1e−3 relative

&nbsp;   No runaway high-k modes

&nbsp;   Coupling amplitudes consistent with soft nonlinear structure



Outputs:

\- Table of P(k) at early and late times for first ~8 modes.

\- Total power drift.

\- pass/fail flag.



--------------------------------------------------------------------

\# 3. Test CG-T10 — Coherence Sensitivity Scan

--------------------------------------------------------------------



Goal:

\- Probe how LCRD v2 handles initial density noise.

\- Tests whether the G\_coh term (plus nu\_n) properly suppresses

&nbsp; short-scale density deviations while preserving mass.



Initial condition:

&nbsp;   n\_j(0) = rho0 + ε\_noise \* ξ\_j

&nbsp;       with ξ\_j ∈ \[−1, +1] random

&nbsp;   θ\_j(0) = A \* sin(2π j / N)

Parameters:

&nbsp;   ε\_noise = 0.001, 0.005, 0.01

&nbsp;   A = 0.01

&nbsp;   k\_noise = N/4, N/8 injected implicitly via noise spectrum



Procedure:

1\. Evolve microscopically for t\_final = 10.



2\. Coarse-grain n\_j(t) → ρ\_I(t), compute:

&nbsp;      noise\_power(t) = Σ\_k≠0 |ρ̂\_I(k,t)|²



3\. Fit exponential damping rate γ\_coh:

&nbsp;      noise\_power(t) ∼ exp(−2 γ\_coh t)



4\. Ensure γ\_coh increases with G\_coh, decreases with lowering G\_coh.



Acceptance criteria:

&nbsp;   γ\_coh > 0 for all ε\_noise

&nbsp;   noise\_power bounded and decaying

&nbsp;   mass drift < 1e−3 relative



Outputs:

\- noise\_power(t) curves

\- extracted γ\_coh values

\- pass/fail flag



--------------------------------------------------------------------

\# 4. Test CG-T11 — Long-Time Invariant Drift (v2 Edition)

--------------------------------------------------------------------



Goal:

\- Stress stability and invariant preservation over longer times

&nbsp; than CG-T3 and CG-T7 for v1.

\- Assess whether LCRD v2 produces stable coarse invariants 

&nbsp; without introducing secular drift.



Initial condition:

&nbsp;   n\_j(0) = rho0

&nbsp;   θ\_j(0) = A \* sin(2π j / N)

Amplitude A = 0.01

Integration time: t\_final = 40



Diagnostics:

&nbsp;   M(t) = Σ\_I ρ\_I(t)

&nbsp;   E(t) = Σ\_I \[0.5 ρ\_I (∂x θ\_I)² + (g\_eff\_IR/2)\*(ρ\_I − rho0)²]



Procedure:

1\. Evolve for t = 0…40.

2\. Coarse-grain each output frame.

3\. Compute mass and energy drift:

&nbsp;      rel\_drift\_M = |M(T) − M(0)| / M(0)

&nbsp;      rel\_drift\_E = |E(T) − E(0)| / E(0)



Acceptance criteria:

&nbsp;   rel\_drift\_M < 5e−3

&nbsp;   rel\_drift\_E < 1e−2

&nbsp;   No high-k instability or phase unwrapping blow-up.



Outputs:

\- M(t) and E(t) curves

\- drift values

\- pass/fail flag



--------------------------------------------------------------------

\# 5. Combined Pass/Fail Logic for LCRD v2

--------------------------------------------------------------------



LCRD v2 is accepted only if:



&nbsp;   (1) CG-T8 → PASS (bandwise dispersion consistency)

&nbsp;   (2) CG-T9 → PASS (nonlinear spectral structure acceptable)

&nbsp;   (3) CG-T10 → PASS (coherence suppression + mass preservation)

&nbsp;   (4) CG-T11 → PASS (long-time invariants in acceptable drift)



A single failure indicates:

&nbsp;   - revise G\_phase, G\_density, G\_coh, nu\_n

&nbsp;   - revise discrete stencils if necessary

&nbsp;   - or return to Step-7 dynamics design.



--------------------------------------------------------------------

\# 6. Transition to Step-8

--------------------------------------------------------------------



If all tests pass for a candidate parameter set:



1\. LCRD v2 update rules become “frozen”.

2\. Proceed to Step-8:

&nbsp;      - implement v2 in the simulation engine,

&nbsp;      - conduct the full CG-T8–T11 suite numerically,

&nbsp;      - tune parameters for best agreement with CRFT.



This completes the Step-7 theoretical test planning.



