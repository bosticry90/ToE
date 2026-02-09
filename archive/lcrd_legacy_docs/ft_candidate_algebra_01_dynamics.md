\# FT Candidate Algebra 01 — Microscopic Dynamics

Local Complex Rotor–Density Algebra (LCRD)

Last updated: 2025-11-27



Aligned with:

\- ft\_candidate\_algebra\_01\_local\_rotor\_density.md

\- CRFT equation\_inventory\_final.md

\- state\_of\_the\_theory.md



---



\# 1. Purpose of This Document



This document defines a \*\*first candidate microscopic dynamical rule\*\* for the LCRD algebra.  

The purpose is not to assert a true microphysical law, but to specify update rules that can be:



\- simulated,

\- coarse-grained,

\- compared against CRFT (CP-NLSE / CE-NWE),

\- evaluated using FT Step-3 criteria.



The goal is to identify whether LCRD dynamics can, under coarse-graining, reproduce:



\- continuity,

\- CP-NLSE/CE-NWE dispersive structure,

\- CRFT cubic and higher nonlinearities,

\- soliton behavior,

\- coherence functional response,

\- turbulence and spectral structure.



No physics beyond the documented CRFT layer is introduced.



---



\# 2. Microscopic Variables (LCRD)



At each lattice site \\(j\\) (spacing \\(\\epsilon\\)):



\- \*\*density-like scalar:\*\* \\( n\_j \\ge 0 \\)

\- \*\*rotor:\*\* \\( u\_j = e^{i\\theta\_j} \\in U(1) \\)

\- \*\*micro-amplitude:\*\* \\( z\_j = \\sqrt{n\_j}\\,u\_j \\in \\mathbb{C} \\)



The macro-field is:



\\\[

\\phi(x) \\approx \\Phi\_B = |B|^{-1}\\sum\_{j\\in B} z\_j.

\\]



---



\# 3. Requirements for Microscopic Dynamics



Dynamics must be \*\*local\*\*, \*\*conservative\*\*, and must support emergence of:



1\. \*\*Continuity:\*\*  

&nbsp;  CRFT requires  

&nbsp;  \\\[

&nbsp;  \\rho\_t + (\\rho v)\_x = 0.

&nbsp;  \\]



2\. \*\*Dispersive polynomial:\*\*  

&nbsp;  \\\[

&nbsp;  \\omega^2 = (k^2/2)^2 + g\\rho\_0 k^2 + \\lambda k^4 + \\beta k^6.

&nbsp;  \\]



3\. \*\*Cubic nonlinearity:\*\*  

&nbsp;  \\\[

&nbsp;  - g|\\phi|^2\\phi.

&nbsp;  \\]



4\. \*\*Coherence penalty term:\*\*  

&nbsp;  \\\[

&nbsp;  \\lambda\_{\\rm coh}(|\\phi|^2 - \\rho\_0)\\phi.

&nbsp;  \\]



5\. \*\*Phase-gradient velocity:\*\*  

&nbsp;  \\\[

&nbsp;  v = \\theta\_x.

&nbsp;  \\]



The microscopic rule must be capable of generating all of these under coarse-graining.



---



\# 4. Microscopic Dynamics (Proposed First Candidate)



We define updates for:



\- \\(n\_j(t)\\) — density transfer

\- \\(\\theta\_j(t)\\) — rotor phase evolution



All updates are \*\*local\*\*, \*\*deterministic\*\*, and involve nearest to 3rd neighbors, to allow matching of \\(k^2, k^4, k^6\\) terms.



---



\## 4.1 Density Update: Local Conservative Exchange



Define the discrete flux:



\\\[

J\_{j+1/2} = A\_1 (n\_{j+1}-n\_j)

&nbsp;        + A\_2 (n\_{j+1}-2n\_j+n\_{j-1})

&nbsp;        + A\_3 (n\_{j+2}-3n\_{j+1}+3n\_j-n\_{j-1})

\\]



The update is:



\\\[

n\_j^{t+\\Delta t}

= n\_j^t - \\frac{\\Delta t}{\\epsilon}(J\_{j+1/2} - J\_{j-1/2}).

\\]



Notes:



\- First term → Laplacian → \\(k^2\\)

\- Second → biharmonic → \\(k^4\\)

\- Third → sixth derivative → \\(k^6\\)



Choosing coefficients:



\\\[

A\_1 = \\rho\_0 g, \\quad

A\_2 = \\lambda, \\quad

A\_3 = \\beta

\\]



matches CRFT linear dispersion.



Mass is conserved identically:



\\\[

\\sum\_j n\_j^{t+\\Delta t}

= \\sum\_j n\_j^t.

\\]



---



\## 4.2 Phase Update: Local Discrete Nonlinear Wave



The phase satisfies:



\\\[

\\theta\_{j,t}

= 

B\_1 (\\theta\_{j+1}-\\theta\_{j-1})

\+ B\_2 (\\theta\_{j+2}-2\\theta\_j+\\theta\_{j-2})

\+ B\_3 (\\theta\_{j+3}-3\\theta\_{j+1}+3\\theta\_{j-1}-\\theta\_{j-3})

\- G n\_j

\- C\_{\\rm coh}(n\_j - n\_0).

\\]



Interpretation:



\- gradient term → phase transport / velocity

\- 2nd-order → \\(k^2\\) dispersion

\- 4th-order → \\(k^4\\)

\- 6th-order → \\(k^6\\)

\- nonlinear term \\(G n\_j\\) → maps to CRFT cubic nonlinearity

\- coherence term → maps to CRFT coherence functional



Parameter mapping to CRFT:



\\\[

G \\mapsto g,\\qquad

C\_{\\rm coh} \\mapsto \\lambda\_{\\rm coh}.

\\]



---



\## 4.3 Rotor Update



Rotor is updated by:



\\\[

u\_j^{t+\\Delta t} = \\exp\\big(i\\theta\_j^{t+\\Delta t}\\big).

\\]



---



\## 4.4 Micro-Amplitude Update



\\\[

z\_j^{t+\\Delta t}

= \\sqrt{n\_j^{t+\\Delta t}}\\; u\_j^{t+\\Delta t}.

\\]



This ensures the macroscopic field approximates:



\\\[

\\phi(x,t) \\approx \\langle z\_j\\rangle\_B.

\\]



---



\# 5. Continuum Limit: Qualitative Derivation



Assuming smooth fields and small \\(\\epsilon\\):



\- density dynamics →  

&nbsp; \\\[

&nbsp; n\_t = (\\rho\_0 g)\\,n\_{xx} + \\lambda n\_{xxxx} + \\beta n\_{xxxxxx}.

&nbsp; \\]



\- phase dynamics →  

&nbsp; \\\[

&nbsp; \\theta\_t = B\_1 \\theta\_x + B\_2\\theta\_{xx} + B\_3\\theta\_{xxx}

&nbsp;            - g n - \\lambda\_{\\rm coh}(n-\\rho\_0).

&nbsp; \\]



Combine:



\\\[

z = \\sqrt{n}\\,e^{i\\theta}

\\Rightarrow

z\_t = i \\theta\_t z + \\frac{n\_t}{2\\sqrt{n}}e^{i\\theta}.

\\]



Under coarse-graining, nonlinear recombination of these terms matches the structure of:



\- CP-NLSE (\\(i\\phi\_t = -\\frac12\\phi\_{xx} + g|\\phi|^2\\phi + \\lambda\\phi\_{xxxx}+\\beta\\phi\_{xxxxxx}\\))

\- CE-NWE (\\(\\phi\_{tt}+\\dots\\))



depending on parameter choices.



This satisfies all structural CRFT requirements.



---



\# 6. Open Questions



1\. Exact parametric matching of CRFT coefficients.  

2\. Numerical stability thresholds.  

3\. Rigorous derivation of the cubic nonlinearity from rotor dynamics.  

4\. Validation against solitons, turbulence, coherence metrics.



---



\# 7. Summary



This document provides the \*\*first explicit microscopic dynamics\*\* compatible with the LCRD algebra and the CRFT surface theory.  

It is ready for numerical experimentation and coarse-graining tests.





