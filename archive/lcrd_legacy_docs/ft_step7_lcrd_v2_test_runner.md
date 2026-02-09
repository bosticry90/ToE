\# FT Step-7 — LCRD v2 Test Runner Design

Document: ft\_step7\_lcrd\_v2\_test\_runner.md  

Status: DESIGN ONLY (no code yet)



Purpose:

\- Specify how CG-T8–CG-T11 will be executed as scripts.

\- Define a minimal, consistent test harness layout for LCRD v2.

\- Ensure tests can be run individually and as a bundled suite,

&nbsp; similar in spirit to CG-T1–CG-T7 for LCRD v1.



Scope:

\- This document does not change CRFT or LCRD v2 dynamics.

\- It specifies script names, expected inputs, outputs, and run patterns.



Assumed directory structure (analogous to existing FT tests):



&nbsp;   fundamental\_theory/

&nbsp;     simulators/

&nbsp;       lcrd/

&nbsp;         backend.py

&nbsp;         config.py

&nbsp;         state.py

&nbsp;         stepper.py      # will later contain v1 and v2 update modes

&nbsp;         coarse\_grain.py

&nbsp;         diagnostics.py

&nbsp;         runners.py

&nbsp;     tests/

&nbsp;       cg\_t1\_dispersion\_test.py

&nbsp;       cg\_t2\_amplitude\_scan.py

&nbsp;       cg\_t3\_mass\_conservation.py

&nbsp;       cg\_t4\_energy\_conservation.py

&nbsp;       cg\_t5\_nonlinear\_dispersion.py

&nbsp;       cg\_t6\_mode\_coupling.py

&nbsp;       cg\_t7\_long\_time\_drift.py

&nbsp;       cg\_t8\_v2\_band\_dispersion.py          # NEW

&nbsp;       cg\_t9\_v2\_mode\_coupling.py            # NEW

&nbsp;       cg\_t10\_v2\_coherence\_scan.py          # NEW

&nbsp;       cg\_t11\_v2\_long\_time\_invariants.py    # NEW

&nbsp;       run\_lcrd\_v2\_suite.py                 # NEW (suite runner)



LCRD v2 is treated as an additional “engine” selectable via config or a

flag, not as a replacement for v1.



--------------------------------------------------------------------

\# 1. Common Harness Requirements for CG-T8–CG-T11

--------------------------------------------------------------------



All CG-T8–CG-T11 scripts will share:



1\. Import structure:



&nbsp;   from simulators.lcrd.config     import SimulationConfig

&nbsp;   from simulators.lcrd.backend    import get\_backend

&nbsp;   from simulators.lcrd.state      import initialize\_state

&nbsp;   from simulators.lcrd.stepper    import step\_lcrd\_v2    # v2 entry point

&nbsp;   from simulators.lcrd.coarse\_grain import coarse\_grain\_fields

&nbsp;   from simulators.lcrd.diagnostics import (

&nbsp;       measure\_frequency,

&nbsp;       compute\_spectral\_power,

&nbsp;       compute\_mass\_energy

&nbsp;   )



2\. Backend selection:

&nbsp;  - Support at least "cpu" backend.

&nbsp;  - Later allow "gpu" via CuPy, same as existing LCRD v1 tests.



3\. Configuration:

&nbsp;  - SimulationConfig extended to include:

&nbsp;        engine = "lcrd\_v2"

&nbsp;        G\_phase, G\_density, G\_coh, nu\_n

&nbsp;  - Scripts will construct a config instance and override parameters

&nbsp;    as needed for each test.



4\. Output:

&nbsp;  - Human-readable console prints (mode, amplitude, measured ω, g\_eff,

&nbsp;    drift metrics).

&nbsp;  - Optional numpy arrays or CSV dumps via a common helper if needed later

&nbsp;    (not required at Step-7).



5\. Run pattern:

&nbsp;  Each script:



&nbsp;  - Prints a descriptive header:

&nbsp;        "=== CG-T8 (LCRD v2): Bandwise Dispersion Mapping ==="

&nbsp;  - Shows key configuration values.

&nbsp;  - Runs one or more test cases.

&nbsp;  - Summarizes results and indicates PASS/FAIL according to thresholds

&nbsp;    defined in ft\_step7\_lcrd\_v2\_test\_plan.md.



--------------------------------------------------------------------

\# 2. CG-T8 Runner — `cg\_t8\_v2\_band\_dispersion.py`

--------------------------------------------------------------------



Purpose:

\- Probe small-k dispersion and extract g\_eff(k) for the first few modes.



Entry point:

\- Executable via:

&nbsp;     python cg\_t8\_v2\_band\_dispersion.py

&nbsp; from fundamental\_theory/tests.



High-level steps:



1\. Define a list of modes and amplitude:



&nbsp;      mode\_list = \[1, 2, 3, 4, 5, 6]

&nbsp;      A = 0.01



2\. For each mode m in mode\_list:

&nbsp;  - Build SimulationConfig with:

&nbsp;        engine     = "lcrd\_v2"

&nbsp;        mode\_index = m

&nbsp;        rho0       = 1.0

&nbsp;        G\_phase, G\_density, G\_coh, nu\_n set to candidate v2 values

&nbsp;        N, L, dt, t\_final, block\_size chosen analogous to v1 IR tests

&nbsp;  - Initialize state with:

&nbsp;        n\_j = rho0

&nbsp;        theta\_j = A \* sin(2π m j / N)

&nbsp;  - Run simulation to t\_final.

&nbsp;  - Coarse-grain to ρ\_I, θ\_I, φ\_I.

&nbsp;  - Use measure\_frequency to get ω\_measured(m).

&nbsp;  - Compute g\_eff(m) from ω\_measured using the IR relation.



3\. After looping:

&nbsp;  - Compute Δg\_eff = max(g\_eff) − min(g\_eff).

&nbsp;  - Print a summary table.

&nbsp;  - Indicate PASS/FAIL based on:

&nbsp;        Δg\_eff < 0.05 \* g\_eff\_IR

&nbsp;        rel\_err(k=1) < 1e−2



Optional:

\- Accept a command-line option to change mode\_list or A.



--------------------------------------------------------------------

\# 3. CG-T9 Runner — `cg\_t9\_v2\_mode\_coupling.py`

--------------------------------------------------------------------



Purpose:

\- Test nonlinear spectral transfer for v2 using a two-mode initial condition.



Entry point:

\- Executable via:

&nbsp;     python cg\_t9\_v2\_mode\_coupling.py



High-level steps:



1\. Set:

&nbsp;      k1\_index = 1

&nbsp;      k2\_index = 2

&nbsp;      A1 = 0.01

&nbsp;      A2 = 0.01

&nbsp;      t\_final = 10–15



2\. Build SimulationConfig:

&nbsp;      engine     = "lcrd\_v2"

&nbsp;      rho0       = 1.0

&nbsp;      G\_phase, G\_density, G\_coh, nu\_n as chosen for v2

&nbsp;      N, L, dt, block\_size matching CG-T8 settings



3\. Initialize state:

&nbsp;      n\_j = rho0

&nbsp;      theta\_j = A1 \* sin(2π k1 j / N) + A2 \* sin(2π k2 j / N)



4\. Run to t\_final.



5\. Coarse-grain and compute spectral power P(k) at:

&nbsp;      t = 0  and  t = t\_final



6\. Compute:

&nbsp;      T(k) = P(k, t\_final) / P(k, 0)

&nbsp;      total power drift: Σ\_k P(k,t\_final) vs Σ\_k P(k,0)



7\. Print a table of P(k) and T(k) for the first few modes (e.g., k=0–8),

&nbsp;  total power drift, and PASS/FAIL according to:

&nbsp;      |Σ\_k P(k,T) − Σ\_k P(k,0)| / Σ\_k P(k,0) < 1e−3

&nbsp;      No runaway high-k growth.



Optional:

\- Provide CLI flags for different (k1, k2) pairs.



--------------------------------------------------------------------

\# 4. CG-T10 Runner — `cg\_t10\_v2\_coherence\_scan.py`

--------------------------------------------------------------------



Purpose:

\- Study the effect of G\_coh and nu\_n on density noise suppression.



Entry point:

\- Executable via:

&nbsp;     python cg\_t10\_v2\_coherence\_scan.py



High-level steps:



1\. Choose a baseline parameter set and a small list of (G\_coh, nu\_n)

&nbsp;  pairs to test.



2\. For each pair (G\_coh, nu\_n):

&nbsp;  - Build SimulationConfig with:

&nbsp;        engine   = "lcrd\_v2"

&nbsp;        rho0     = 1.0

&nbsp;        G\_phase, G\_density fixed

&nbsp;        G\_coh, nu\_n varying

&nbsp;  - Initialize state:

&nbsp;        n\_j = rho0 + ε\_noise \* ξ\_j

&nbsp;        θ\_j = A \* sin(2π j / N)

&nbsp;    with:

&nbsp;        ε\_noise ∈ {0.001, 0.005, 0.01}

&nbsp;        A = 0.01

&nbsp;        ξ\_j uniform random in \[−1, +1]



3\. Run to t\_final = 10.



4\. At multiple times t\_n:

&nbsp;  - Coarse-grain n\_j → ρ\_I.

&nbsp;  - Compute noise\_power(t\_n) = Σ\_k≠0 |ρ̂\_I(k,t\_n)|².



5\. For each (G\_coh, nu\_n, ε\_noise):

&nbsp;  - Fit an exponential decay:

&nbsp;        noise\_power(t) ~ exp(−2 γ\_coh t)

&nbsp;  - Record γ\_coh and mass drift.



6\. Print:

&nbsp;  - Table of (G\_coh, nu\_n, ε\_noise, γ\_coh, mass drift).

&nbsp;  - PASS/FAIL if:

&nbsp;        γ\_coh > 0

&nbsp;        mass drift < 1e−3



Optional:

\- Provide CLI options to select only one (G\_coh, nu\_n) pair.



--------------------------------------------------------------------

\# 5. CG-T11 Runner — `cg\_t11\_v2\_long\_time\_invariants.py`

--------------------------------------------------------------------



Purpose:

\- Test long-time stability and invariant drift for LCRD v2.



Entry point:

\- Executable via:

&nbsp;     python cg\_t11\_v2\_long\_time\_invariants.py



High-level steps:



1\. Select:

&nbsp;      mode\_index = 1

&nbsp;      A = 0.01

&nbsp;      t\_final = 40

&nbsp;      rho0 = 1.0



2\. Build SimulationConfig:

&nbsp;      engine     = "lcrd\_v2"

&nbsp;      N, L, dt, block\_size as in CG-T8

&nbsp;      G\_phase, G\_density, G\_coh, nu\_n as candidate v2 parameters



3\. Initialize state:

&nbsp;      n\_j = rho0

&nbsp;      theta\_j = A \* sin(2π mode\_index j / N)



4\. Evolve from t=0 to t\_final, recording fields at regular time intervals.



5\. For each recorded time:

&nbsp;  - Coarse-grain to ρ\_I, θ\_I.

&nbsp;  - Compute:

&nbsp;        M(t) = Σ\_I ρ\_I(t)

&nbsp;        E(t) = Σ\_I \[0.5 ρ\_I (∂x θ\_I)² + (g\_eff\_IR/2)\*(ρ\_I − rho0)²]



6\. Compute:

&nbsp;      rel\_drift\_M = |M(T) − M(0)| / M(0)

&nbsp;      rel\_drift\_E = |E(T) − E(0)| / E(0)



7\. Print:

&nbsp;  - M(0), M(T), rel\_drift\_M

&nbsp;  - E(0), E(T), rel\_drift\_E

&nbsp;  - PASS/FAIL if:

&nbsp;        rel\_drift\_M < 5e−3

&nbsp;        rel\_drift\_E < 1e−2



Optional:

\- Record minimal diagnostics to file if needed later.



--------------------------------------------------------------------

\# 6. Combined Suite Runner — `run\_lcrd\_v2\_suite.py`

--------------------------------------------------------------------



Purpose:

\- Provide a single entry point to run CG-T8–CG-T11 in sequence.



Entry point:

\- Executable via:

&nbsp;     python run\_lcrd\_v2\_suite.py



Behavior:



1\. Print header:

&nbsp;      "=== LCRD v2 Validation Suite: CG-T8–CG-T11 ==="



2\. Internally import and call main() or run() functions from:

&nbsp;      cg\_t8\_v2\_band\_dispersion

&nbsp;      cg\_t9\_v2\_mode\_coupling

&nbsp;      cg\_t10\_v2\_coherence\_scan

&nbsp;      cg\_t11\_v2\_long\_time\_invariants



3\. Aggregate PASS/FAIL results from each test.



4\. At the end, print a concise summary:



&nbsp;      CG-T8: PASS/FAIL

&nbsp;      CG-T9: PASS/FAIL

&nbsp;      CG-T10: PASS/FAIL

&nbsp;      CG-T11: PASS/FAIL



&nbsp;      Overall: PASS if all individual tests passed, otherwise FAIL.



5\. Exit code:

&nbsp;  - Return 0 if all tests passed.

&nbsp;  - Return nonzero (e.g. 1) if any failed.



--------------------------------------------------------------------

\# 7. Transition to Step-8

--------------------------------------------------------------------



Once this runner design is accepted:



1\. Step-8 will implement `step\_lcrd\_v2` in the stepper and the CG-T8–CG-T11

&nbsp;  scripts in `fundamental\_theory/tests`.



2\. Running:

&nbsp;      python run\_lcrd\_v2\_suite.py

&nbsp;  will become the standard way to validate any proposed LCRD v2 parameter set

&nbsp;  against CRFT-based criteria.



This completes the Step-7 test harness design for LCRD v2.



