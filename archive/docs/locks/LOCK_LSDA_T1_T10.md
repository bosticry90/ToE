LOCK: LSDA T1–T10 — IMPLEMENTATION + PYTEST ENFORCEMENT + DIAGNOSTIC RUNNER

===========================================================================



Status

------

This document locks the LSDA (“LSDA”; acronym expansion is not locked by this document) baseline

code surface and the tests T1–T10 as implemented and executed in the repository.



This lock is intended to serve as an authoritative replacement reference for LSDA coverage that is

otherwise summarized in higher-level roadmap documents.



Scope

-----

This lock applies to all of the following, as they exist in the repository:



1\. LSDA core implementation files (importable code under fundamental\_theory/lsda).

2\. LSDA diagnostic scripts (T1–T10) located under fundamental\_theory/tests when present.

&nbsp;  These are Python scripts that can be executed as modules and/or loaded by pytest wrappers.

3\. LSDA pytest enforcement wrappers (T1–T10) that assert invariants, dispersion agreement,

&nbsp;  convergence expectations, CPU/GPU consistency, stress behavior, and spectral structure.

4\. The LSDA core diagnostic runner script that executes a defined subset of diagnostic scripts.



This lock does NOT:

\- assert global physical correctness beyond what is explicitly computed and asserted by the

&nbsp; locked tests,

\- assert uniqueness of interpretation,

\- assert behavior outside the parameter ranges and runtime horizons exercised by the locked tests.



Locked Equations / Numerical Form (as implemented)

--------------------------------------------------

LSDA time evolution is implemented in two distinct right-hand-side (RHS) variants. These variants:



\- share the same continuity equation,

\- share the same advective, pressure, and viscous momentum terms,

\- differ in (i) the derivative-operator implementation (finite-difference vs spectral/FFT) and

&nbsp; (ii) the sign convention of the dispersive momentum term.



Continuity (both RHS variants):

&nbsp;   ∂t ρ = -∂x(ρ u)



Momentum (shared additive decomposition; dispersive sign differs by path):

&nbsp;   ∂t u = (-u ∂x u) + (-g ∂x ρ) + (ν ∂xx u) + (dispersive term)



Dispersive term sign by implementation path

------------------------------------------

A. Finite-difference RHS (default exported integration path: lsda/rk4.py → lsda/dynamics.py):

&nbsp;      dispersive = -(λ ∂xxx ρ)



&nbsp;  Implementation structure in lsda/dynamics.py is an explicit term decomposition:

&nbsp;      - du\_adv  = -u \* ∂x u

&nbsp;      - du\_pres = -g \* ∂x ρ

&nbsp;      - du\_visc =  ν \* ∂xx u

&nbsp;      - du\_disp = -λ \* ∂xxx ρ



B. Spectral RHS (alternate stepper path: lsda/stepper.py → lsda/eom.py):

&nbsp;      dispersive = +(λ ∂xxx ρ)



&nbsp;  Implementation structure in lsda/eom.py is likewise an explicit term decomposition, with:

&nbsp;      dispersive = +λ \* ρ\_xxx



Important divergence note:

--------------------------

The sign difference in the dispersive term between the finite-difference RHS and the spectral RHS

is a real, implementation-level divergence. This lock records that divergence explicitly.

This lock does not assert equivalence between the two RHS variants.



Integration APIs and execution paths (as implemented)

-----------------------------------------------------

Package-level default integration API:

\- The package exposes an integrate() entry point as:

&nbsp;     fundamental\_theory.lsda.integrate

\- This integrate() is implemented in:

&nbsp;     fundamental\_theory/lsda/rk4.py

&nbsp; and re-exported at package level by:

&nbsp;     fundamental\_theory/lsda/\_\_init\_\_.py

\- The default integrate() path calls the finite-difference RHS in:

&nbsp;     fundamental\_theory/lsda/dynamics.py

&nbsp; and uses finite-difference derivative stencils on a periodic 1D grid.



Alternate spectral integration path:

\- An RK4 evolution path using FFT-based (spectral) spatial derivatives exists in:

&nbsp;     fundamental\_theory/lsda/stepper.py  (time integration / RK4 wrapper)

&nbsp;     fundamental\_theory/lsda/eom.py      (spectral derivative operators and RHS assembly)

\- This spectral path exists in the codebase but is not the default integrate() path unless

&nbsp; invoked directly via the stepper/eom stack.



Parameter containers and hooks (as implemented)

-----------------------------------------------

There are two distinct parameter dataclasses named LSDAParams in different modules:



A. Baseline exported parameter class (default API):

\- Module-qualified name:

&nbsp;     fundamental\_theory.lsda.params.LSDAParams

\- Fields:

&nbsp;     g, nu, lam

\- This class is the baseline parameter container used by the default integrate() path.



B. Spectral-path parameter class (alternate path):

\- Module-qualified name:

&nbsp;     fundamental\_theory.lsda.eom.LSDAParams

\- Fields:

&nbsp;     g, nu, lam, alpha, beta

\- The additional fields alpha and beta are placeholders/hooks for future higher-order terms and

&nbsp; are part of the spectral-path implementation surface only. They are not used by the default

&nbsp; integrate() path unless the spectral stepper is invoked explicitly.



Files Covered by This Lock

--------------------------

LSDA implementation (core, importable):

\- fundamental\_theory/lsda/\_\_init\_\_.py

\- fundamental\_theory/lsda/backend.py

\- fundamental\_theory/lsda/grid.py

\- fundamental\_theory/lsda/state.py

\- fundamental\_theory/lsda/params.py

\- fundamental\_theory/lsda/eom.py

\- fundamental\_theory/lsda/stepper.py

\- fundamental\_theory/lsda/rk4.py

\- fundamental\_theory/lsda/invariants.py

\- fundamental\_theory/lsda/io.py

\- fundamental\_theory/lsda/diagnostics.py

\- fundamental\_theory/lsda/coarse\_grain.py

\- fundamental\_theory/lsda/dynamics.py



LSDA diagnostic scripts (located under fundamental\_theory/tests in this repository snapshot):

These scripts are used as the diagnostic implementations for T1–T10 and may be executed directly

as modules (see Execution Commands).

\- fundamental\_theory/tests/lsda\_t1\_smoke.py

\- fundamental\_theory/tests/lsda\_t2\_dispersion.py

\- fundamental\_theory/tests/lsda\_t3\_nonlinear.py

\- fundamental\_theory/tests/lsda\_t3b\_structure.py

\- fundamental\_theory/tests/lsda\_t4\_crft\_compare.py

\- fundamental\_theory/tests/lsda\_t5\_long\_time\_drift.py

\- fundamental\_theory/tests/lsda\_t6\_dt\_convergence.py

\- fundamental\_theory/tests/lsda\_t7\_nonlinear\_long\_time\_drift.py

\- fundamental\_theory/tests/lsda\_t8\_gpu\_cpu\_consistency.py

\- fundamental\_theory/tests/lsda\_t9\_param\_stress.py

\- fundamental\_theory/tests/lsda\_t10\_spectral\_structure.py



Pytest enforcement wrappers (T1–T10):

These wrappers load and execute the diagnostic scripts and enforce test pass/fail conditions via

explicit assertions and thresholds.

\- fundamental\_theory/tests/conftest.py

\- fundamental\_theory/tests/test\_lsda\_t1\_smoke.py

\- fundamental\_theory/tests/test\_lsda\_t2\_dispersion.py

\- fundamental\_theory/tests/test\_lsda\_t3\_nonlinear.py

\- fundamental\_theory/tests/test\_lsda\_t3b\_structure.py

\- fundamental\_theory/tests/test\_lsda\_t4\_crft\_compare.py

\- fundamental\_theory/tests/test\_lsda\_t5\_long\_time\_drift.py

\- fundamental\_theory/tests/test\_lsda\_t6\_dt\_convergence.py

\- fundamental\_theory/tests/test\_lsda\_t7\_nonlinear\_long\_time\_drift.py

\- fundamental\_theory/tests/test\_lsda\_t8\_gpu\_cpu\_consistency.py

\- fundamental\_theory/tests/test\_lsda\_t9\_param\_stress.py

\- fundamental\_theory/tests/test\_lsda\_t10\_spectral\_structure.py



Runner (diagnostic execution driver):

\- fundamental\_theory/run\_lsda\_core\_suite.py



Runner behavior (locked)

------------------------

The runner executes the core diagnostic subset:

\- lsda\_t1\_smoke

\- lsda\_t2\_dispersion

\- lsda\_t3\_nonlinear

\- lsda\_t3b\_structure



When invoked as:

&nbsp;   python fundamental\_theory\\run\_lsda\_core\_suite.py

the runner imports these diagnostics as:

&nbsp;   tests.lsda\_t1\_smoke, tests.lsda\_t2\_dispersion, tests.lsda\_t3\_nonlinear, tests.lsda\_t3b\_structure

because the script directory (fundamental\_theory) is on sys.path for that invocation, making the

fundamental\_theory/tests directory importable as a top-level package named "tests".



The runner does not execute T4–T10. T4–T10 are locked via pytest enforcement wrappers and, where

desired, direct module execution of their diagnostic scripts.



Locked Test Claims (T1–T10)

---------------------------

This section is a high-level summary of what each test is intended to enforce. The exact numerical

thresholds, tolerances, and assertion logic are defined in the pytest wrappers listed above.



T1 — Smoke / invariants sanity:

\- Integrates LSDA forward for a short time horizon and requires finite (non-NaN, non-inf) outputs.

\- Enforces extremely small (tolerance-level) drift in mass and energy over that horizon for the

&nbsp; baseline regime used by the diagnostic.



T2 — Linear dispersion calibration:

\- Measures frequency versus the theoretical small-amplitude expectation ω ≈ c k for multiple modes

&nbsp; under small perturbations.

\- Enforces bounded relative error against the diagnostic’s reference model and thresholds.



T3 — Nonlinear envelope / shock-onset diagnostic:

\- Runs multiple nonlinear amplitudes and checks:

&nbsp; - bounded drift in tracked invariants within the test’s tolerances,

&nbsp; - sanity of nonlinear behavior metrics (including density contrast behavior) under the diagnostic

&nbsp;   horizon.



T3b — Nonlinear structure metrics:

\- Evaluates structure metrics (including contrast, gradient norms, and effective spectral width) at

&nbsp; multiple times for moderate and strong nonlinear regimes.

\- Requires metrics remain finite and within the bounds defined by the diagnostic and wrapper.



T4 — CRFT-limit dispersion comparison:

\- Measures dispersion agreement in a CRFT-limit regime and enforces near-zero or very small error

&nbsp; consistent with the diagnostic’s stated intent and thresholds.



T5 — Long-time drift:

\- Enforces that long-horizon drift of tracked invariants remains within defined tolerances for the

&nbsp; baseline regimes used in the diagnostic.



T6 — dt convergence:

\- Enforces that time-step refinement improves or controls specified error metrics in a manner

&nbsp; consistent with convergence expectations, using the wrapper-defined thresholds.



T7 — Nonlinear long-time drift:

\- Enforces that long-horizon behavior in nonlinear regimes remains within defined tolerances for the

&nbsp; metrics and invariants selected by the diagnostic and wrapper.



T8 — GPU/CPU consistency:

\- If no GPU backend is available, the pytest wrapper skips this test.

\- If a GPU backend is available, enforces numerical agreement between CPU and GPU results within

&nbsp; defined tolerances for selected invariants and comparison metrics.



T9 — Parameter stress:

\- Executes a suite of stressed parameter combinations and enforces the defined pass conditions.

\- Observed behavior in stressed regimes may include RuntimeWarnings (overflow encountered in

&nbsp; multiply, invalid value encountered in subtract/add/reduce, and related warnings). These warnings

&nbsp; are permitted by this lock provided the test assertions still pass.



T10 — Spectral structure:

\- Enforces that spectral and/or coherent-structure metrics behave as specified by the diagnostic and

&nbsp; thresholds in the pytest wrapper.



Execution Commands (authoritative)

----------------------------------

All commands below are run from the repository root (PowerShell).



1\) Run all LSDA pytest wrappers (T1–T10):

&nbsp;   pytest -q `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t1\_smoke.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t2\_dispersion.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t3\_nonlinear.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t3b\_structure.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t4\_crft\_compare.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t5\_long\_time\_drift.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t6\_dt\_convergence.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t7\_nonlinear\_long\_time\_drift.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t8\_gpu\_cpu\_consistency.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t9\_param\_stress.py `

&nbsp;     fundamental\_theory\\tests\\test\_lsda\_t10\_spectral\_structure.py



2\) Run the LSDA core diagnostic runner:

&nbsp;   python fundamental\_theory\\run\_lsda\_core\_suite.py



3\) Run individual diagnostics as modules (scripts listed above are module-executable):

&nbsp;   python -m fundamental\_theory.tests.lsda\_t1\_smoke

&nbsp;   python -m fundamental\_theory.tests.lsda\_t2\_dispersion

&nbsp;   python -m fundamental\_theory.tests.lsda\_t3\_nonlinear

&nbsp;   python -m fundamental\_theory.tests.lsda\_t3b\_structure

&nbsp;   python -m fundamental\_theory.tests.lsda\_t4\_crft\_compare

&nbsp;   python -m fundamental\_theory.tests.lsda\_t5\_long\_time\_drift

&nbsp;   python -m fundamental\_theory.tests.lsda\_t6\_dt\_convergence

&nbsp;   python -m fundamental\_theory.tests.lsda\_t7\_nonlinear\_long\_time\_drift

&nbsp;   python -m fundamental\_theory.tests.lsda\_t8\_gpu\_cpu\_consistency

&nbsp;   python -m fundamental\_theory.tests.lsda\_t9\_param\_stress

&nbsp;   python -m fundamental\_theory.tests.lsda\_t10\_spectral\_structure



Known Warnings / Non-fatal Signals

----------------------------------

\- The parameter-stress enforcement (T9) may emit RuntimeWarnings such as overflow encountered in

&nbsp; multiply and invalid value encountered in subtract/add/reduce. These warnings occur in stressed

&nbsp; regimes and are permitted by this lock provided the T9 assertions still pass.



Lock Integrity Notes

--------------------

\- This lock is enforced by pytest passing for T1–T10 under the authoritative command above and by

&nbsp; successful runner execution for the core subset (T1–T3b).

\- Any change to the covered files that alters test assertions, tolerances, diagnostic behaviors, or

&nbsp; the exported integration surface requires updating this lock document and re-running the full

&nbsp; suite.



End of Lock

-----------



