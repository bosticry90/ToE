\# FT Candidate Algebra 01 — Discrete Mapping for LCRD v1



Document: `ft\_candidate\_algebra\_01\_discrete\_mapping.md`  

Parents:  

\- `ft\_candidate\_algebra\_01\_local\_rotor\_density.md`  

\- `ft\_candidate\_algebra\_01\_dispersion\_calibration.md`  

\- `ft\_candidate\_algebra\_01\_dispersion\_matching\_derivation.md`  



Status: Draft (continuum ↔ discrete mapping plan for LCRD v1)



---



\## 1. Purpose and Scope



The previous FT candidate algebra documents established:



1\. A \*\*local complex rotor–density (LCRD)\*\* micro model as a candidate fundamental description beneath CRFT.

2\. A \*\*continuum linearized model\*\* for LCRD v1, with effective operators

&nbsp;  \\(\\alpha(k^2), \\beta(k^2), \\gamma(k^2), \\eta(k^2)\\) controlling the dispersion.

3\. A \*\*dispersion matching derivation\*\*, showing how these operators must be tuned to approximate the CRFT dispersion

&nbsp;  \\\[

&nbsp;  \\omega^2\_{\\text{CRFT}}(k)

&nbsp;  = \\left(\\frac{k^2}{2}\\right)^2

&nbsp;  + g\\rho\_0 k^2

&nbsp;  + \\lambda k^4

&nbsp;  + \\beta k^6

&nbsp;  \\]

&nbsp;  at low \\(k\\).



This document defines a \*\*clean, explicit mapping\*\* between:



\- the \*\*continuum coefficients\*\* \\(\\alpha\_i, \\beta\_i, \\gamma\_i, \\eta\_i\\) used in the dispersion analysis, and  

\- the \*\*discrete LCRD v1 update scheme\*\* (finite-difference stencils and coupling terms).



The goal is to specify, at the level of design:



1\. Which discrete stencils will be used in LCRD v1, and  

2\. How their small-\\(k\\) expansions yield the continuum parameters that appear in the dispersion relations.



Actual numerical choices of coefficients (i.e., the final calibration) will be done in a later step; here we only establish the analytic relationships.



---



\## 2. Discrete Lattice Setup



We consider a 1D periodic lattice with:



\- number of micro sites: \\(N\\),

\- lattice spacing: \\(\\Delta x \\equiv \\epsilon\\),

\- physical length: \\(L = N \\epsilon\\).



Discrete fields:



\- \\(n\_j(t) \\approx n(x\_j, t)\\),  

\- \\(\\theta\_j(t) \\approx \\theta(x\_j, t)\\),  

\- \\(u\_j = e^{i\\theta\_j}\\),  

\- \\(z\_j = \\sqrt{n\_j}\\,u\_j\\),



with grid points \\(x\_j = j\\epsilon\\), \\(j = 0,\\dots,N-1\\).



Discrete Fourier modes (with periodic boundary conditions) are:



\\\[

\\hat{f}\_k

= \\frac{1}{N} \\sum\_{j=0}^{N-1} f\_j\\, e^{-i k x\_j}, \\quad

k\_m = \\frac{2\\pi m}{L},\\ m = 0,\\dots,N-1.

\\]



At small \\(k\\) (i.e., long wavelengths compared to \\(\\epsilon\\)), the discrete finite-difference operators approximate continuum derivatives with \\(k\\)-dependent prefactors that can be expanded in powers of \\(k\\epsilon\\).



---



\## 3. Discrete Operators and Their Small-k Expansions



We outline the canonical stencils to be used in LCRD v1 for:



\- spatial derivatives of order 1, 2, 4, 6;

\- local coupling between \\(n\\) and \\(\\theta\\).



The actual implementation in `stepper.py` will be aligned with these stencils.



\### 3.1 First derivative: central difference



Discrete operator:



\\\[

(\\partial\_x f)\_j

\\approx \\frac{f\_{j+1} - f\_{j-1}}{2\\epsilon}.

\\]



Fourier symbol:



\\\[

\\widehat{\\partial\_x}(k)

= \\frac{i}{\\epsilon}\\,\\sin(k\\epsilon)

= i k\\left\[1 - \\frac{(k\\epsilon)^2}{6} + O((k\\epsilon)^4)\\right].

\\]



Thus, at small \\(k\\):



\- Leading order: \\(i k\\),

\- Next correction: \\(O(k^3)\\).



\### 3.2 Second derivative: central difference Laplacian



Discrete operator:



\\\[

(\\partial\_{xx} f)\_j

\\approx \\frac{f\_{j+1} - 2 f\_j + f\_{j-1}}{\\epsilon^2}.

\\]



Fourier symbol:



\\\[

\\widehat{\\partial\_{xx}}(k)

= \\frac{e^{ik\\epsilon} - 2 + e^{-ik\\epsilon}}{\\epsilon^2}

= \\frac{2\\cos(k\\epsilon)-2}{\\epsilon^2}.

\\]



Using \\(\\cos(k\\epsilon) = 1 - \\tfrac{(k\\epsilon)^2}{2} + \\tfrac{(k\\epsilon)^4}{24} - \\dots\\):



\\\[

\\widehat{\\partial\_{xx}}(k)

= -k^2 + \\frac{k^4\\epsilon^2}{12} + O(k^6\\epsilon^4).

\\]



So, for small \\(k\\):



\\\[

\\widehat{\\partial\_{xx}}(k)

= -k^2\\left\[1 - \\frac{k^2\\epsilon^2}{12} + O(k^4\\epsilon^4)\\right].

\\]



\### 3.3 Fourth and sixth derivatives via repeated Laplacian



For simplicity and stability, LCRD v1 can construct higher-order derivatives from repeated application of the discrete Laplacian:



\- Fourth derivative:

&nbsp; \\\[

&nbsp; \\partial\_{xxxx} f \\approx \\partial\_{xx}(\\partial\_{xx} f),

&nbsp; \\]

\- Sixth derivative:

&nbsp; \\\[

&nbsp; \\partial\_{xxxxxx} f \\approx \\partial\_{xx}(\\partial\_{xxxx} f) = \\partial\_{xx}^3 f.

&nbsp; \\]



In Fourier space:



\- Fourth derivative symbol:

&nbsp; \\\[

&nbsp; \\widehat{\\partial\_{xxxx}}(k)

&nbsp; = \[\\widehat{\\partial\_{xx}}(k)]^2

&nbsp; \\approx k^4\\left\[1 + O(k^2\\epsilon^2)\\right].

&nbsp; \\]

\- Sixth derivative symbol:

&nbsp; \\\[

&nbsp; \\widehat{\\partial\_{xxxxxx}}(k)

&nbsp; = \[\\widehat{\\partial\_{xx}}(k)]^3

&nbsp; \\approx -k^6\\left\[1 + O(k^2\\epsilon^2)\\right].

&nbsp; \\]



Thus, to leading order:



\- \\(\\partial\_{xx}\\) provides a \\(-k^2\\) factor,

\- \\(\\partial\_{xxxx}\\) provides a \\(+k^4\\) factor,

\- \\(\\partial\_{xxxxxx}\\) provides a \\(-k^6\\) factor,



with controlled \\(O(k^2\\epsilon^2)\\) corrections.



---



\## 4. Proposed LCRD v1 Discrete Update Scheme (Linear Part)



We now specify a linearized version of the LCRD v1 update rules in terms of these discrete operators. The final nonlinear scheme may add additional terms, but for dispersion calibration we focus on the linear part.



\### 4.1 Variables



We consider perturbations around a uniform background:



\\\[

n\_j(t) = \\rho\_0 + \\delta n\_j(t),\\qquad

\\theta\_j(t) = 0 + \\delta\\theta\_j(t).

\\]



The micro field is:



\\\[

z\_j(t) \\approx \\sqrt{\\rho\_0}\\,\\Bigl(

1 + \\frac{\\delta n\_j}{2\\rho\_0} + i\\,\\delta\\theta\_j

\\Bigr).

\\]



The CG-T1 dispersion test extracts the time dependence of the coarse-grained complex field mode \\(\\phi(k)\\) and measures its oscillation frequency.



\### 4.2 Discrete linearized equations



We propose the following \*\*discrete linearized v1 update\*\*:



\\\[

\\delta n\_t

= L\_n\[\\delta n] + C\_{n\\theta}\[\\delta\\theta],

\\]

\\\[

\\delta\\theta\_t

= L\_\\theta\[\\delta\\theta] + C\_{\\theta n}\[\\delta n],

\\]



where:



1\. \*\*Density self-operator\*\* \\(L\_n\\):

&nbsp;  \\\[

&nbsp;  L\_n\[\\delta n]

&nbsp;  = A\_2\\,\\partial\_{xxxx}\\delta n

&nbsp;  + A\_3\\,\\partial\_{xxxxxx}\\delta n,

&nbsp;  \\]

&nbsp;  implemented via repeated discrete Laplacians (no \\(A\_1\\) term to avoid leading \\(k^3\\) odd behaviour).



2\. \*\*Phase self-operator\*\* \\(L\_\\theta\\):

&nbsp;  \\\[

&nbsp;  L\_\\theta\[\\delta\\theta]

&nbsp;  = B\_2\\,\\partial\_{xx}\\delta\\theta,

&nbsp;  \\]

&nbsp;  implementing a Laplacian-driven phase dispersion.



3\. \*\*Phase→density coupling\*\* \\(C\_{n\\theta}\\):

&nbsp;  \\\[

&nbsp;  C\_{n\\theta}\[\\delta\\theta]

&nbsp;  = E\_2\\,\\partial\_{xx}\\delta\\theta,

&nbsp;  \\]

&nbsp;  representing a gradient-mediated feedback of phase curvature into density.



4\. \*\*Density→phase coupling\*\* \\(C\_{\\theta n}\\):

&nbsp;  \\\[

&nbsp;  C\_{\\theta n}\[\\delta n]

&nbsp;  = -G\_0\\,\\delta n,

&nbsp;  \\]

&nbsp;  a local, constant-strength coupling that produces the acoustic-like term in the dispersion.



In Fourier space, with the small-\\(k\\) approximations from §3, these become:



\- Density equation:

&nbsp; \\\[

&nbsp; \\partial\_t \\hat{\\delta n}

&nbsp; = -\\alpha(k^2)\\,\\hat{\\delta n} - \\eta(k^2)\\,\\hat{\\delta\\theta},

&nbsp; \\]

\- Phase equation:

&nbsp; \\\[

&nbsp; \\partial\_t \\hat{\\delta\\theta}

&nbsp; = -\\gamma(k^2)\\,\\hat{\\delta n} - \\beta(k^2)\\,\\hat{\\delta\\theta},

&nbsp; \\]



with:



\\\[

\\begin{aligned}

\\alpha(k^2)

\&\\approx -A\_2 k^4 + A\_3 k^6 + O(k^8), \\\\

\\beta(k^2)

\&\\approx -B\_2 k^2 + O(k^4), \\\\

\\eta(k^2)

\&\\approx -E\_2 k^2 + O(k^4), \\\\

\\gamma(k^2)

\&\\approx G\_0 + O(k^2).

\\end{aligned}

\\]



By comparing to the abstract continuum notation in the dispersion derivation, we identify:



\\\[

\\alpha\_2 = 0,\\quad

\\alpha\_4 \\approx -A\_2,\\quad

\\alpha\_6 \\approx A\_3,

\\]



\\\[

\\beta\_2 \\approx -B\_2,\\quad

\\beta\_4 \\approx 0,

\\]



\\\[

\\eta\_2 \\approx -E\_2,\\quad

\\gamma\_0 \\approx G\_0.

\\]



Higher-order terms can be added later as needed, but this minimal mapping already provides control over:



\- the density \\(k^4\\) and \\(k^6\\) contributions (\\(A\_2, A\_3\\)),

\- the phase \\(k^2\\) dispersion (\\(B\_2\\)),

\- the crucial density–phase couplings (\\(E\_2, G\_0\\)).



---



\## 5. Mapping Summary: Continuum ↔ Discrete Coefficients



Collecting the identifications:



\- \*\*Density self-operator\*\*:

&nbsp; - Discrete:

&nbsp;   \\\[

&nbsp;   L\_n\[\\delta n]

&nbsp;   = A\_2\\,\\partial\_{xxxx}\\delta n + A\_3\\,\\partial\_{xxxxxx}\\delta n.

&nbsp;   \\]

&nbsp; - Continuum small-k:

&nbsp;   \\\[

&nbsp;   \\alpha(k^2) = \\alpha\_4 k^4 + \\alpha\_6 k^6 + \\dots,

&nbsp;   \\]

&nbsp;   with

&nbsp;   \\\[

&nbsp;   \\alpha\_4 \\approx -A\_2,\\quad

&nbsp;   \\alpha\_6 \\approx A\_3.

&nbsp;   \\]



\- \*\*Phase self-operator\*\*:

&nbsp; - Discrete:

&nbsp;   \\\[

&nbsp;   L\_\\theta\[\\delta\\theta]

&nbsp;   = B\_2\\,\\partial\_{xx}\\delta\\theta.

&nbsp;   \\]

&nbsp; - Continuum small-k:

&nbsp;   \\\[

&nbsp;   \\beta(k^2) = \\beta\_2 k^2 + \\dots,

&nbsp;   \\]

&nbsp;   with

&nbsp;   \\\[

&nbsp;   \\beta\_2 \\approx -B\_2.

&nbsp;   \\]



\- \*\*Phase→density coupling\*\*:

&nbsp; - Discrete:

&nbsp;   \\\[

&nbsp;   C\_{n\\theta}\[\\delta\\theta]

&nbsp;   = E\_2\\,\\partial\_{xx}\\delta\\theta.

&nbsp;   \\]

&nbsp; - Continuum small-k:

&nbsp;   \\\[

&nbsp;   \\eta(k^2) = \\eta\_2 k^2 + \\dots,

&nbsp;   \\]

&nbsp;   with

&nbsp;   \\\[

&nbsp;   \\eta\_2 \\approx -E\_2.

&nbsp;   \\]



\- \*\*Density→phase coupling\*\*:

&nbsp; - Discrete:

&nbsp;   \\\[

&nbsp;   C\_{\\theta n}\[\\delta n]

&nbsp;   = -G\_0\\,\\delta n.

&nbsp;   \\]

&nbsp; - Continuum small-k:

&nbsp;   \\\[

&nbsp;   \\gamma(k^2) = \\gamma\_0 + \\dots,

&nbsp;   \\]

&nbsp;   with

&nbsp;   \\\[

&nbsp;   \\gamma\_0 \\approx G\_0.

&nbsp;   \\]



These identifications allow us to rewrite the key calibration conditions from the dispersion analysis in terms of the discrete coefficients \\((A\_2, A\_3, B\_2, E\_2, G\_0)\\).



---



\## 6. Discrete Calibration Conditions from CRFT



From the dispersion-matching derivation, the low-k CRFT matching conditions are:



1\. \*\*Acoustic slope (k² term)\*\*:

&nbsp;  \\\[

&nbsp;  \\omega^2(k) \\sim g\\rho\_0 k^2

&nbsp;  \\quad \\Rightarrow\\quad

&nbsp;  \\eta\_2\\gamma\_0 \\approx g\\rho\_0.

&nbsp;  \\]



&nbsp;  Using the discrete mapping:

&nbsp;  \\\[

&nbsp;  (-E\_2) G\_0 \\approx g\\rho\_0

&nbsp;  \\quad\\Rightarrow\\quad

&nbsp;  -E\_2 G\_0 \\approx g\\rho\_0.

&nbsp;  \\]



&nbsp;  This provides a direct relationship between the phase→density coupling strength \\(E\_2\\), the density→phase coupling \\(G\_0\\), and the CRFT parameters.



2\. \*\*Quartic curvature (k⁴ term)\*\* and \*\*sextic correction (k⁶ term)\*\*:

&nbsp;  - Controlled by \\(\\alpha\_4, \\alpha\_6, \\beta\_2\\) and subleading corrections in \\(\\eta, \\gamma\\).

&nbsp;  - In discrete terms, primarily controlled by \\(A\_2, A\_3, B\_2\\), and any higher-order coupling corrections that may be added.



&nbsp;  At the level of design, we note:



&nbsp;  - \\(B\_2\\) primarily sets the \*\*baseline phase diffusion/dispersion\*\* and can be adjusted for stability and subleading corrections.

&nbsp;  - \\(A\_2\\) and \\(A\_3\\) set the \*\*shape of the density contribution\*\* to the dispersion curve at \\(k^4\\) and \\(k^6\\).



In practice, calibration will proceed as:



\- Choose a reasonable pair \\((E\_2, G\_0)\\) satisfying the acoustic slope condition.

\- Adjust \\(A\_2, A\_3, B\_2\\) to fine-tune the shape of the dispersion curve (quartic and sextic behaviour) against the CRFT analytic formula, using CG-T1 and possibly additional dispersion tests.



---



\## 7. Implementation Notes for LCRD v1 Stepper



When implementing LCRD v1 in `stepper.py`, the linear part of the update can be written schematically as:



```python

\# Pseudocode structure for LCRD v1 linear update



def step\_density\_v1(xp, state, config):

&nbsp;   n = state.n

&nbsp;   theta = state.theta

&nbsp;   eps = config.epsilon



&nbsp;   # Discrete Laplacian

&nbsp;   lap\_n = laplacian\_1d(n, eps, xp)

&nbsp;   lap2\_n = laplacian\_1d(lap\_n, eps, xp)     # ~ ∂xxxx n

&nbsp;   lap3\_n = laplacian\_1d(lap2\_n, eps, xp)    # ~ ∂xxxxxx n



&nbsp;   lap\_theta = laplacian\_1d(theta, eps, xp)



&nbsp;   # Linear part (plus any nonlinear corrections later)

&nbsp;   n\_t = config.A2 \* lap2\_n + config.A3 \* lap3\_n + config.E2 \* lap\_theta

&nbsp;   n\_new = n + config.dt \* n\_t

&nbsp;   return n\_new



def step\_phase\_v1(xp, state, config):

&nbsp;   n = state.n

&nbsp;   theta = state.theta

&nbsp;   eps = config.epsilon



&nbsp;   lap\_theta = laplacian\_1d(theta, eps, xp)



&nbsp;   theta\_t = config.B2 \* lap\_theta - config.G0 \* (n - config.rho0)

&nbsp;   theta\_new = theta + config.dt \* theta\_t

&nbsp;   return theta\_new



