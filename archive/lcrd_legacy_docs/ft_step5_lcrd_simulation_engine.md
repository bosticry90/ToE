\# FT Step 5 — LCRD Simulation Engine Design

Local Complex Rotor–Density Algebra (LCRD)

Last updated: 2025-11-27



Aligned with:

\- ft\_candidate\_algebra\_01\_local\_rotor\_density.md

\- ft\_candidate\_algebra\_01\_dynamics.md

\- ft\_candidate\_algebra\_01\_numerics.md

\- ft\_step4\_coarse\_graining\_harness.md

\- CRFT equation\_inventory\_final.md

\- state\_of\_the\_theory.md



Primary GPU backend:

\- CuPy (NumPy-compatible GPU array library)

CPU reference backend:

\- NumPy



---



\## 1. Purpose of Step 5



This document specifies the \*\*implementation design\*\* for the LCRD simulation engine:



\- A \*\*backend-agnostic\*\* micro-simulator (NumPy/CuPy),

\- Compatible with the \*\*Step-4 coarse-graining harness\*\*,

\- Capable of running all initial Step-4 tests (CG-T1–T3, and later T4–T8),

\- Suitable for both CPU debugging and GPU-accelerated runs.



The engine is intended as a \*\*reference implementation\*\*:

\- simple enough to audit against equations,

\- structured enough to extend (e.g., to LSDA or 2D lattices later).



No new physics is introduced here; this is purely a numerical realization of the previously defined LCRD dynamics.



---



\## 2. High-Level Architecture



Directory placement (suggested):



```text

fundamental\_theory/

&nbsp; ft\_candidate\_algebra\_01\_local\_rotor\_density.md

&nbsp; ft\_candidate\_algebra\_01\_dynamics.md

&nbsp; ft\_candidate\_algebra\_01\_numerics.md

&nbsp; ft\_step4\_coarse\_graining\_harness.md

&nbsp; ft\_step5\_lcrd\_simulation\_engine.md  ← this file

&nbsp; simulators/

&nbsp;   lcrd/

&nbsp;     \_\_init\_\_.py

&nbsp;     backend.py

&nbsp;     config.py

&nbsp;     state.py

&nbsp;     stepper.py

&nbsp;     coarse\_grain.py

&nbsp;     diagnostics.py

&nbsp;     runners.py

&nbsp;     tests/  (optional, or reuse project-wide pytest)



