\# FT Step-5 Status — LCRD v1 Calibration Against CRFT



Updated: 2025-11-27



\## 1. Purpose



FT Step-5 has two roles:



1\. Implement a concrete microscopic dynamics candidate (LCRD v1) consistent with

&nbsp;  the local rotor–density algebra defined in FT Step-3.

2\. Calibrate and test LCRD v1 against the CRFT layer (CP-NLSE / CE-NWE) in the

&nbsp;  long-wavelength, low-amplitude regime using a small but focused set of

&nbsp;  micro→macro tests.



This document summarizes what has been implemented and verified so far.



---



\## 2. Engine and Mapping



The LCRD v1 simulation engine lives under:



\- `fundamental\_theory/simulators/lcrd/`



and consists of:



\- `backend.py` — CPU/GPU abstraction (CuPy-ready).

\- `config.py` — `SimulationConfig` with N, dt, t\_final, micro coefficients, etc.

\- `state.py` — initialization of rotor–density micro states.

\- `stepper.py` — time-stepping for LCRD v1 dynamics.

\- `coarse\_grain.py` — block-averaging map from micro to coarse-grained φ(x,t).

\- `diagnostics.py` — routines for measuring ω(k), etc.

\- `runners.py` — helper routines for one-shot tests (e.g. single-mode runs).



The micro → macro mapping is:



\- local rotor–density variables → coarse φ(x,t),

\- from which ρ(x,t) = |φ|² and θ(x,t) = arg φ are inferred.



---



\## 3. CG-T1 — IR Dispersion Calibration



\*\*Script:\*\* `fundamental\_theory/tests/cg\_t1\_dispersion\_test.py`



\- Configuration:

&nbsp; - N = 512, ε = 1, L = 512, dt = 10⁻³, t\_final = 10.

&nbsp; - mode\_index = 1 (lowest nonzero k).

&nbsp; - G = 12.5, C\_coh = −12.5, A₁ = A₂ = A₃ = 0.



\- Procedure:

&nbsp; - Excite a single mode at k₁ with a small amplitude.

&nbsp; - Evolve under LCRD v1.

&nbsp; - Coarse-grain to φ(x,t) and extract ω\_measured(k₁).

&nbsp; - Fit an effective CRFT nonlinearity g\_eff under the CP-NLSE/CE-NWE

&nbsp;   dispersion ansatz with (λ = β = 0).



\- Result:

&nbsp; - At mode\_index = 1 (IR regime) the fit yields:

&nbsp;   \\\[

&nbsp;   g\_\\mathrm{eff} \\approx 0.1666,

&nbsp;   \\]

&nbsp;   defining the IR mapping between LCRD v1 and CRFT.

&nbsp; - Higher modes (mode\_index = 2,3,4) give large, k-dependent g\_eff and are

&nbsp;   explicitly treated as UV microstructure, not used for CRFT mapping.



---



\## 4. CG-T2 — Amplitude Robustness at Fixed k₁



\*\*Script:\*\* `fundamental\_theory/tests/cg\_t2\_amplitude\_scan.py`



\- Configuration:

&nbsp; - Same as CG-T1, mode\_index = 1.

&nbsp; - Amplitudes scanned over A ∈ \[1e−3, 3e−3, 1e−2, 2e−2, 5e−2].



\- Procedure:

&nbsp; - For each A, run LCRD v1, coarse-grain to φ(x,t), and measure

&nbsp;   ω\_measured(k₁; A).

&nbsp; - Compare |ω\_measured| to the IR-linear CRFT prediction at k₁ using

&nbsp;   the locked g\_eff from CG-T1.

&nbsp; - Evaluate the relative error vs the IR prediction.



\- Observation:

&nbsp; - For all tested amplitudes in the near-linear range, the relative error

&nbsp;   vs the IR-linear CRFT prediction is O(10⁻⁶) or smaller, far below a 10%

&nbsp;   tolerance for the near-linear check.



Interpretation:



> The IR dispersion mapping at k₁ remains stable across small but finite

> amplitudes; LCRD v1 behaves essentially linearly in this regime.



---



\## 5. CG-T3 — Coarse-Grained Mass Conservation



\*\*Script:\*\* `fundamental\_theory/tests/cg\_t3\_mass\_conservation.py`



\- Configuration:

&nbsp; - Same as CG-T1–T2, with amplitude A = 1e−2 at mode\_index = 1.



\- Procedure:

&nbsp; - Run LCRD v1 and coarse-grain to φ(x,t).

&nbsp; - Define the coarse-grained “mass”:

&nbsp;   \\\[

&nbsp;   M(t) \\approx \\sum\_j |\\phi\_j(t)|^2\\,\\Delta x\_\\text{coarse}.

&nbsp;   \\]

&nbsp; - Compute M(0) and M(T) and report the relative drift.



\- Observation (example run):

&nbsp; - M(0) ≈ 5.11999995 × 10²,

&nbsp; - M(T) ≈ 5.12000000 × 10²,

&nbsp; - relative drift ≈ 9.4 × 10⁻⁹ (≪ 2% tolerance).



Interpretation:



> At the LCRD→CRFT level, the coarse-grained dynamics effectively preserve a

> CP-NLSE-like norm over the CG-T3 run.



---



\## 6. CG-T4 — Coarse-Grained Energy-Like Drift



\*\*Script:\*\* `fundamental\_theory/tests/cg\_t4\_energy\_conservation.py`



\- Configuration:

&nbsp; - Same as CG-T1–T3, with amplitude A = 1e−2 at mode\_index = 1.

&nbsp; - IR effective nonlinearity g\_eff fixed to the CG-T1 value.



\- Procedure:

&nbsp; - Run LCRD v1 and coarse-grain to φ(x,t).

&nbsp; - Define a coarse-grained energy-like functional:

&nbsp;   \\\[

&nbsp;   E(t)

&nbsp;   \\approx

&nbsp;   \\sum\_j \\left\[

&nbsp;     \\tfrac12|\\partial\_x \\phi\_j(t)|^2

&nbsp;     + \\tfrac12 g\_\\mathrm{eff} |\\phi\_j(t)|^4

&nbsp;   \\right] \\Delta x\_\\text{coarse},

&nbsp;   \\]

&nbsp;   using the locked IR g\_eff from CG-T1.

&nbsp; - Compute E(0) and E(T) and report the relative drift compared to a

&nbsp;   tolerance (here 5%).



\- Observation (example run):

&nbsp; - E(0) ≈ 4.26612747 × 10¹,

&nbsp; - E(T) ≈ 4.26612739 × 10¹,

&nbsp; - relative drift ≈ 1.9 × 10⁻⁸ (≪ 5% tolerance).



Interpretation:



> The LCRD v1 dynamics, when coarse-grained using the current mapping, respect

> a CP-NLSE-like Hamiltonian structure to numerical precision in the tested

> regime.



---



\## 7. Step-5 Conclusion



With CG-T1–T4 implemented and tested:



1\. LCRD v1 reproduces the IR CRFT dispersion at k₁ with a well-defined

&nbsp;  effective nonlinearity g\_eff.

2\. This mapping is stable across small but finite amplitudes at k₁.

3\. The coarse-grained dynamics preserve a CP-NLSE-like norm to high

&nbsp;  numerical accuracy in the tested regime.

4\. A coarse-grained energy-like functional is conserved to near machine

&nbsp;  precision over the CG-T4 run.



This set of tests is sufficient to regard FT Step-5 as \*\*functionally

complete for the LCRD v1 → CRFT IR mapping\*\*. Further refinements

(e.g., multi-mode tests, soliton-like profiles) can be treated as

extensions or Step-5B, but are not prerequisites for moving on to

FT Step-6 (invariants and symmetries).



