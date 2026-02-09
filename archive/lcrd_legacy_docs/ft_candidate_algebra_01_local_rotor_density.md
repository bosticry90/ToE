\# FT Candidate Algebra 01 — Local Complex Rotor–Density Algebra (LCRD)



\_Last updated: 2025-11-26\_  

\_Aligned with: `ft\_step3\_composition\_algebra.md`, CRFT equation inventory, and state\_of\_the\_theory.md\_ 



---



\## 1. Purpose and Status of Candidate 01



This document specifies \*\*Candidate Algebra 01\*\* for the Fundamental Theory (FT) program:



> \*\*LCRD: Local Complex Rotor–Density Algebra\*\*



The goal is to define a \*\*local, composable microscopic structure\*\* whose coarse-grained limit can plausibly reproduce the CRFT scalar field \\(\\phi(x,t)\\), with density \\(\\rho = |\\phi|^2\\), phase \\(\\theta = \\arg(\\phi)\\), and dynamics given by CP-NLSE / CE-NWE and their hydrodynamic forms.   



This is \*\*not\*\* a claim that LCRD is the true fundamental theory. It is a \*\*first mathematically explicit candidate\*\* to be tested against the FT Step-3 requirements:



\- locality and composability,  

\- support for emergent U(1)-like phases,  

\- density-like magnitude,  

\- continuity and CRFT dispersion structure,  

\- coherence functional behavior,  

\- computational simulability. :contentReference\[oaicite:2]{index=2}  



---



\## 2. Micro Degrees of Freedom (DOFs)



We consider a \*\*1D lattice\*\* (spacing \\(\\epsilon\\)) indexed by sites \\(j \\in \\mathbb{Z}\\), with optional generalization to higher dimensions later.



\### 2.1 Site Variables



At each lattice site \\(j\\), we define \*\*two microscopic DOFs\*\*:



1\. \*\*Micro-density:\*\*  

&nbsp;  \\\[

&nbsp;  n\_j \\in \[0,\\infty)

&nbsp;  \\]

&nbsp;  (dimensionless “occupancy” or weight)



2\. \*\*Micro-rotor (phase):\*\*  

&nbsp;  \\\[

&nbsp;  u\_j \\in U(1), \\quad u\_j = e^{i\\theta\_j}, \\quad \\theta\_j \\in \[0,2\\pi)

&nbsp;  \\]



Thus, each site carries a pair:

\\\[

a\_j = (n\_j, u\_j).

\\]



This pair is the local analogue of CRFT’s emergent density and phase, which combine into \\(\\phi = \\sqrt{\\rho}\\,e^{i\\theta}\\). :contentReference\[oaicite:3]{index=3}  



\### 2.2 Local Complex Amplitude at the Micro Level



We define a \*\*micro-complex amplitude\*\* at each site:

\\\[

z\_j = \\sqrt{n\_j}\\,u\_j = \\sqrt{n\_j}\\,e^{i\\theta\_j} \\in \\mathbb{C}.

\\]



In the emergent limit, blocks of \\(\\{z\_j\\}\\) will be coarse-grained into the CRFT field \\(\\phi(x,t)\\).



---



\## 3. Algebraic Composition Law



We need a \*\*composition algebra\*\* describing how local DOFs combine when regions are merged. The key requirement is that composition respects:



\- \*\*locality,\*\*  

\- \*\*density additivity/extensivity,\*\*  

\- \*\*U(1) phase behavior,\*\*  

\- \*\*a well-defined coarse-grained complex amplitude.\*\* :contentReference\[oaicite:4]{index=4}  



We define composition at the level of \*\*single sites first\*\*, then extend to regions.



\### 3.1 Single-Site Composition



Given two micro-states at the same lattice site \\(j\\):



\\\[

a\_j^{(1)} = (n\_j^{(1)}, u\_j^{(1)}),\\quad 

a\_j^{(2)} = (n\_j^{(2)}, u\_j^{(2)}),

\\]



we define their \*\*composed state\*\* at that site:



\\\[

a\_j^{(1)} \\star a\_j^{(2)} = (n\_j^{\\text{tot}}, u\_j^{\\text{eff}}),

\\]



with:



1\. \*\*Density additivity (extensive):\*\*

&nbsp;  \\\[

&nbsp;  n\_j^{\\text{tot}} = n\_j^{(1)} + n\_j^{(2)}.

&nbsp;  \\]



2\. \*\*Weighted rotor (phase) averaging on the unit circle:\*\*

&nbsp;  - Represent each rotor as a complex unit:

&nbsp;    \\\[

&nbsp;    u\_j^{(1)} = e^{i\\theta\_j^{(1)}},\\quad

&nbsp;    u\_j^{(2)} = e^{i\\theta\_j^{(2)}}.

&nbsp;    \\]

&nbsp;  - Compute a \*\*weighted complex sum\*\*:

&nbsp;    \\\[

&nbsp;    s\_j = n\_j^{(1)} u\_j^{(1)} + n\_j^{(2)} u\_j^{(2)}.

&nbsp;    \\]

&nbsp;  - If \\(s\_j \\neq 0\\), define:

&nbsp;    \\\[

&nbsp;    u\_j^{\\text{eff}} = \\frac{s\_j}{|s\_j|} \\in U(1).

&nbsp;    \\]

&nbsp;  - If \\(s\_j = 0\\) (exact destructive interference), define \\(u\_j^{\\text{eff}}\\) arbitrarily (e.g., \\(1\\))—only density matters in that case.



This gives:



\- \*\*extensive density:\*\* the total “mass-like” quantity adds,  

\- \*\*phase averaging:\*\* the effective phase interpolates between input phases, weighted by density,  

\- \*\*U(1) structure:\*\* phases live on the circle and combine via complex addition + normalization.



This is analogous to composing many microscopic contributions into an effective coarse-grained phase and density.



\### 3.2 Algebraic Properties



At a single site, composition \\(\\star\\) satisfies:



\- \*\*Commutativity:\*\*  

&nbsp; \\\[

&nbsp; a\_j^{(1)} \\star a\_j^{(2)} = a\_j^{(2)} \\star a\_j^{(1)}

&nbsp; \\]

&nbsp; (symmetric in arguments)



\- \*\*Associativity (almost everywhere):\*\*  

&nbsp; Because density addition is associative and the weighted vector sum in \\(\\mathbb{C}\\) is associative, \\(\\star\\) is associative except for measure-zero degenerate cases where the total complex sum vanishes and a phase convention is needed.



\- \*\*Identity:\*\*  

&nbsp; The state \\((0, u\_0)\\) for any \\(u\_0\\in U(1)\\) acts as an identity:

&nbsp; \\\[

&nbsp; (n\_j, u\_j) \\star (0, u\_0) = (n\_j, u\_j).

&nbsp; \\]



Thus, at each site, we have a \*\*commutative, essentially associative, unital algebra\*\* over the DOFs.



\### 3.3 Composition Over Regions



Given two configurations \\(A\\) and \\(B\\) over the lattice:



\- \\(A = \\{a\_j^{(A)}\\}\\),  

\- \\(B = \\{a\_j^{(B)}\\}\\),



we define \*\*regional composition\*\*:



\\\[

(A \\circledast B)\_j 

:= a\_j^{(A)} \\star a\_j^{(B)}.

\\]



That is, composition is \*\*local and factorizes per site\*\*.



This satisfies the FT requirement that interactions and composition are local and composable. :contentReference\[oaicite:5]{index=5}  



---



\## 4. Coarse-Graining Map to CRFT Field \\(\\phi(x,t)\\)



We define a coarse-graining map from microscopic LCRD configurations to the CRFT field \\(\\phi(x,t)\\). The map should satisfy:



\- emergent density \\(\\rho\\) from \\(n\_j\\),  

\- emergent phase \\(\\theta\\) from \\(u\_j\\),  

\- coherent limit \\(\\phi \\approx \\sqrt{\\rho\_0}\\,e^{i\\theta}\\) for homogeneous states. :contentReference\[oaicite:6]{index=6}  



\### 4.1 Block Coarse-Graining



Let \\(B\\) be a block of sites \\(j\\) corresponding to a small macroscopic interval around position \\(x\\). Define:



1\. \*\*Block density:\*\*

&nbsp;  \\\[

&nbsp;  \\rho\_B = \\frac{1}{|B|}\\sum\_{j \\in B} n\_j.

&nbsp;  \\]



2\. \*\*Block complex amplitude:\*\*

&nbsp;  \\\[

&nbsp;  \\Phi\_B = \\frac{1}{|B|}\\sum\_{j \\in B} \\sqrt{n\_j}\\,u\_j = \\frac{1}{|B|}\\sum\_{j \\in B} z\_j.

&nbsp;  \\]



3\. \*\*Emergent CRFT field value at \\(x\\):\*\*

&nbsp;  \\\[

&nbsp;  \\phi(x) \\approx \\Phi\_B.

&nbsp;  \\]



For sufficiently fine blocks and many micro-DOFs per block:



\- \\(|\\Phi\_B|^2 \\approx \\rho\_B\\) in the coherent regime,  

\- \\(\\arg(\\Phi\_B)\\) defines an emergent phase \\(\\theta(x)\\),  

\- \\(\\rho(x) = |\\phi(x)|^2\\), \\(\\theta(x) = \\arg\\phi(x)\\), \\(v(x) = \\theta\_x(x)\\) become the CRFT hydrodynamic variables. :contentReference\[oaicite:7]{index=7}  



\### 4.2 Continuum Limit



As:



\- lattice spacing \\(\\epsilon \\to 0\\),  

\- block size \\(|B|\\) grows while remaining small on macroscopic scales,



we obtain a \*\*continuum field\*\*:



\\\[

\\phi(x,t) = \\lim\_{\\epsilon \\to 0}\\Phi\_B(x,t),

\\]



which is the candidate emergent CRFT field.



---



\## 5. CRFT-Compatibility Checklist



We now compare LCRD against the FT Step-3 requirements and CRFT constraints.   



\### 5.1 Continuity and Conservation (CRFT-HYD-2)



CRFT requires:

\\\[

\\rho\_t + (\\rho v)\_x = 0.

\\]



In LCRD:



\- \*\*Local density:\*\* \\(\\rho(x) \\sim \\rho\_B \\sim \\text{average}(n\_j)\\).  

\- \*\*Total density:\*\* \\(\\sum\_j n\_j\\) is naturally \*\*additive\*\* under composition \\(\\circledast\\).



By choosing microscopic dynamics that \*\*conserve \\(\\sum\_j n\_j\\)\*\* (e.g., pairwise exchanges, local flows), we can enforce a continuity structure at the micro level. Under coarse-graining, this becomes the macroscopic continuity equation.



The algebra itself (density additivity + locality) is structurally compatible with continuity; the \*\*dynamics\*\* will determine whether the CRFT continuity equation emerges exactly.



\### 5.2 Emergent U(1) Phase and Velocity \\(v=\\theta\_x\\)



Because each site carries a rotor \\(u\_j \\in U(1)\\), and block-averaged complex amplitudes \\(\\Phi\_B\\) define a phase \\(\\theta(x)\\), LCRD supports:



\- emergent phase \\(\\theta(x) = \\arg\\phi(x)\\),  

\- emergent velocity \\(v(x) = \\theta\_x(x)\\), consistent with the CRFT hydrodynamic mapping. :contentReference\[oaicite:9]{index=9}  



\### 5.3 Dispersion Compatibility



CRFT dispersion (linearized):  

\\\[

\\omega^2(k)

= (k^2/2)^2 + g\\rho\_0 k^2 + \\lambda k^4 + \\beta k^6. :contentReference\[oaicite:10]{index=10}

\\]



LCRD, as an algebra, does not yet specify dynamics. However, it is compatible with implementing \*\*local update rules\*\* on \\(\\{n\_j, u\_j\\}\\) that, in Fourier space and small-amplitude linearization, produce this dispersion under coarse-graining:



\- nearest-neighbor couplings → \\(k^2\\) terms,  

\- multi-site couplings (up to three or more sites) → \\(k^4, k^6\\) terms.



Thus, \*\*LCRD does not block\*\* the required dispersion; it provides a natural discrete substrate to implement it.



\### 5.4 Coherence Functional and Uniform Background



CRFT coherence functional:  

\\\[

C = (|\\phi|^2 - \\rho\_0)^2.

\\]



In LCRD:



\- uniform configurations \\(n\_j = n\_0\\), \\(u\_j = u\_0\\) produce a block field with \\(|\\phi|^2 \\approx n\_0\\),  

\- deviations \\(n\_j \\neq n\_0\\), disordered phases \\(u\_j\\), etc., can generate an effective penalization term when coarse-graining and summing local “disorder” contributions.



We can define \*\*micro-coherence measures\*\* such as:

\\\[

C\_B^{\\text{micro}} = \\left(\\frac{1}{|B|}\\sum\_{j\\in B}n\_j - n\_0\\right)^2

\\]

or local phase-variance terms, which under appropriate dynamics can approximate CRFT’s coherence functional at the field level.



\### 5.5 Solitons and Coherent Structures



CRFT supports:



\- dark and bright solitons,  

\- vortices (in higher D),  

\- coherent turbulent structures. :contentReference\[oaicite:11]{index=11}  



In LCRD, coherent blocks with:



\- spatially varying density \\(n\_j\\),  

\- phase gradients \\(\\theta\_j\\),



can form \*\*stable localized patterns\*\* that coarse-grain to soliton-like profiles in \\(\\phi(x)\\). Existence and stability of such patterns is a \*\*dynamical question\*\*, but the DOF structure and composition law do not prevent soliton-like emergent patterns.



---



\## 6. Computational Representation



LCRD is deliberately chosen to be \*\*computationally simple\*\*:



\- A configuration is an array \\(\\{(n\_j,u\_j)\\}\_{j=1}^N\\) on a lattice.  

\- Composition \\(\\circledast\\) is site-wise and trivial to implement.  

\- Coarse-graining to \\(\\phi(x)\\) is simple block averaging in complex space.



This aligns with the FT requirement that any candidate be simulable and compatible with numerical experiments.



---



\## 7. Open Questions and Next Steps



LCRD is a \*\*structurally plausible\*\* candidate but requires further work in three areas:



1\. \*\*Microscopic Dynamics Specification\*\*  

&nbsp;  - Define explicit local update rules for \\((n\_j,u\_j)\\) that:

&nbsp;    - conserve total density \\(\\sum\_j n\_j\\),  

&nbsp;    - approximate CRFT dispersion in linear regime,  

&nbsp;    - generate CRFT-like nonlinear terms (e.g., cubic in \\(|\\phi|^2\\)).  



2\. \*\*Coarse-Graining Analysis\*\*  

&nbsp;  - Derive analytically (or numerically) the effective equation for \\(\\phi(x,t)\\) from the microscopic dynamics and LCRD composition.  

&nbsp;  - Check whether CRFT-EOM-1 / CRFT-EOM-2 emerge in a suitable limit. :contentReference\[oaicite:12]{index=12}  



3\. \*\*Stability and Soliton Tests\*\*  

&nbsp;  - Simulate LCRD with candidate dynamics and observe whether:

&nbsp;    - soliton-like patterns are supported,  

&nbsp;    - turbulence and spectral cascades echo CRFT behavior,  

&nbsp;    - coherence functionals and metrics match CRFT scaling.



These steps will be documented separately in:



\- `ft\_candidate\_algebra\_01\_dynamics.md`  

\- `ft\_candidate\_algebra\_01\_coarse\_graining\_tests.md`  

\- `ft\_candidate\_algebra\_01\_numerics.md`



---



\## 8. Summary



\*\*LCRD (Local Complex Rotor–Density Algebra)\*\* defines:



\- a local, composable pair of micro-DOFs \\((n\_j, u\_j)\\) at each lattice site,  

\- a commutative, essentially associative composition law \\(\\star\\) with additive density and weighted phase combination,  

\- a natural coarse-graining map to a complex field \\(\\phi(x,t)\\) that matches the CRFT representation,  

\- structural compatibility with CRFT continuity, dispersion, coherence, and soliton behavior as documented in the state-of-the-theory and equation inventory.   



LCRD is therefore a \*\*viable first candidate algebra\*\* for the FT program. Its adequacy will ultimately be decided by whether explicit microscopic dynamics on this algebra can reproduce the validated CRFT equations under coarse-graining.





