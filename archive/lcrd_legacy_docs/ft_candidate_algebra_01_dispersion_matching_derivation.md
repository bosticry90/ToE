\# FT Candidate Algebra 01 — Dispersion Matching Derivation



Document: `ft\_candidate\_algebra\_01\_dispersion\_matching\_derivation.md`  

Parent: `ft\_candidate\_algebra\_01\_dispersion\_calibration.md`  

Status: Draft (LCRD v1 low-k dispersion derivation)



---



\## 1. Scope and Relation to Previous Work



This document takes the next step after  

`ft\_candidate\_algebra\_01\_dispersion\_calibration.md`.



There we:



\- identified that LCRD v0 cannot reproduce the CRFT dispersion,

\- introduced a \*\*generic linearized model\*\* for an improved LCRD (v1),

\- defined a Fourier-space 2×2 dispersion matrix \\(M(k)\\) for the linearized \\((\\delta n, \\delta\\theta)\\) dynamics.



Here we:



1\. Choose a \*\*minimal, physically motivated subset of coefficients\*\* for LCRD v1.

2\. Derive the \*\*eigenvalues\*\* of the linearized system in terms of those coefficients.

3\. Expand the leading eigenfrequency \\(\\omega\_+(k)\\) in powers of \\(k\\) (up to \\(O(k^6)\\) in structure).

4\. Identify which micro-coefficients must be tuned to match the CRFT dispersion



\\\[

\\omega^2\_{\\text{CRFT}}(k)

=

\\left(\\frac{k^2}{2}\\right)^2

\+ g\\rho\_0\\,k^2

\+ \\lambda k^4

\+ \\beta k^6

\\]



in the low-k regime.



The result is a \*\*calibration map\*\*: which LCRD v1 coefficients control which orders in the CRFT dispersion.



This is an analytic planning document; concrete numerical choices for the coefficients are left for a later calibration pass.



---



\## 2. Minimal LCRD v1 Linear Model



We start from the generic linearized model defined previously:



\\\[

\\begin{aligned}

\\delta n\_t

\&= -\\alpha(k^2)\\,\\delta n - \\eta(k^2)\\,\\delta\\theta, \\\\

\\delta\\theta\_t

\&= -\\gamma(k^2)\\,\\delta n - \\beta(k^2)\\,\\delta\\theta.

\\end{aligned}

\\]



with



\- \\(\\alpha(k^2)\\) — density self-operator (from density flux / diffusion),

\- \\(\\beta(k^2)\\) — phase self-operator (from phase Laplacians),

\- \\(\\gamma(k^2)\\) — density → phase coupling,

\- \\(\\eta(k^2)\\) — phase → density coupling.



All are real polynomials in \\(k^2\\). We enforce:



\- \*\*no constant rotation\*\* for CG-T1 calibration: \\(\\gamma\_0 = 0\\),

\- \*\*no explicit constant phase damping\*\* at k=0: \\(\\alpha(0) = \\beta(0) = 0\\),

\- \*\*even-in-k structure\*\*: only powers of \\(k^2\\).



\### 2.1 Low-k polynomial truncation



We keep terms up to \\(O(k^6)\\) in each operator, but use a minimal subset of nonzero coefficients to avoid overparameterization.



Write:



\\\[

\\alpha(k^2) = \\alpha\_2 k^2 + \\alpha\_4 k^4 + \\alpha\_6 k^6 + \\dots,

\\]

\\\[

\\beta(k^2) = \\beta\_2 k^2 + \\beta\_4 k^4 + \\beta\_6 k^6 + \\dots,

\\]

\\\[

\\gamma(k^2) = \\gamma\_2 k^2 + \\gamma\_4 k^4 + \\dots,

\\]

\\\[

\\eta(k^2) = \\eta\_2 k^2 + \\eta\_4 k^4 + \\dots.

\\]



For the \*\*minimal LCRD v1 dispersion model\*\* we choose:



\- Allow only \*\*one n→θ coupling term\*\* at leading order: \\(\\gamma\_2 \\neq 0\\), higher \\(\\gamma\_4,\\dots\\) optional.

\- Allow only \*\*one θ→n coupling term\*\* at leading order: \\(\\eta\_2 \\neq 0\\), higher \\(\\eta\_4,\\dots\\) optional.

\- Allow density and phase self-terms to start at \\(k^2\\): \\(\\alpha\_2, \\beta\_2\\) free; higher \\(\\alpha\_4,\\beta\_4,\\dots\\) encode higher-order corrections.



Thus we adopt:



\\\[

\\begin{aligned}

\\alpha(k^2) \&= \\alpha\_2 k^2 + \\alpha\_4 k^4 + O(k^6), \\\\

\\beta(k^2)  \&= \\beta\_2 k^2 + \\beta\_4 k^4 + O(k^6), \\\\

\\gamma(k^2) \&= \\gamma\_2 k^2 + O(k^4), \\\\

\\eta(k^2)   \&= \\eta\_2 k^2 + O(k^4).

\\end{aligned}

\\]



We will see that:



\- \\(\\gamma\_2 \\eta\_2\\) controls the \*\*leading \\(k^2\\) slope\*\* of \\(\\omega^2(k)\\),

\- \\(\\alpha\_2, \\beta\_2\\) primarily control damping and subleading corrections,

\- \\(\\alpha\_4, \\beta\_4, \\eta\_4, \\gamma\_4\\) affect \\(k^4\\) and \\(k^6\\) terms.



---



\## 3. Dispersion Matrix and Eigenvalues



In vector form:



\\\[

\\partial\_t

\\begin{pmatrix}

\\delta n \\\\\[4pt]

\\delta\\theta

\\end{pmatrix}

=

M(k)

\\begin{pmatrix}

\\delta n \\\\

\\delta\\theta

\\end{pmatrix},

\\quad

M(k) =

\\begin{pmatrix}

-\\alpha(k^2) \& -\\eta(k^2) \\\\\[4pt]

-\\gamma(k^2) \& -\\beta(k^2)

\\end{pmatrix}.

\\]



The eigenvalues \\(\\lambda\_\\pm(k)\\) satisfy:



\\\[

\\det\\left(M(k) - \\lambda I\\right) = 0,

\\]



which gives:



\\\[

\\lambda^2

\+ \\lambda (\\alpha + \\beta)

\+ \\alpha \\beta - \\eta\\gamma = 0.

\\]



Thus:



\\\[

\\lambda\_\\pm(k)

= -\\frac{\\alpha(k^2) + \\beta(k^2)}{2}

\\pm \\frac{1}{2}\\sqrt{

\\left(\\alpha(k^2) - \\beta(k^2)\\right)^2

\+ 4\\eta(k^2)\\gamma(k^2)

}.

\\tag{3.1}

\\]



We write:



\\\[

\\lambda\_\\pm(k) = -\\Gamma\_\\pm(k) - i\\omega\_\\pm(k),

\\]



so that \\(\\omega\_\\pm(k)\\) is the oscillation frequency (up to sign), and \\(\\Gamma\_\\pm(k)\\) the damping.



The \*\*CG-T1 observable\*\* \\(\\omega\_{\\text{micro}}(k)\\) is associated with the imaginary part of the eigenvalue(s) that dominate the coarse-grained field \\( \\phi \\).



---



\## 4. Low-k Expansion of the Eigenvalues



We now expand the square root in (3.1) for small \\(k\\), using the minimal polynomials from §2.1.



\### 4.1 Structure of the discriminant



Define:



\\\[

D(k^2) = 

\\left(\\alpha(k^2) - \\beta(k^2)\\right)^2

\+ 4\\eta(k^2)\\gamma(k^2).

\\]



To leading orders:



\- \\(\\alpha(k^2) - \\beta(k^2)

&nbsp;= (\\alpha\_2 - \\beta\_2)k^2 + (\\alpha\_4 - \\beta\_4)k^4 + O(k^6)\\),

\- \\(\\left(\\alpha - \\beta\\right)^2

&nbsp;= (\\alpha\_2 - \\beta\_2)^2 k^4 + O(k^6)\\),

\- \\(\\eta(k^2)\\gamma(k^2)

&nbsp;= (\\eta\_2 k^2)(\\gamma\_2 k^2) + O(k^6)

&nbsp;= \\eta\_2\\gamma\_2 k^4 + O(k^6)\\).



Therefore:



\\\[

D(k^2)

= \\left\[(\\alpha\_2 - \\beta\_2)^2 + 4\\eta\_2\\gamma\_2\\right]k^4

\+ O(k^6).

\\]



The key observation:



\- For small \\(k\\), the discriminant starts at \\(O(k^4)\\).  

\- The \*\*sign\*\* of the coefficient

&nbsp; \\\[

&nbsp; C\_4 = (\\alpha\_2 - \\beta\_2)^2 + 4\\eta\_2\\gamma\_2

&nbsp; \\]

&nbsp; determines whether the eigenvalues are purely real or form complex conjugate pairs.



To obtain oscillatory modes (and hence a nonzero \\(\\omega(k)\\)), we want:



\- \\(D(k^2) < 0\\) at some k, which requires the effective expression under the square root to be negative, or

\- more realistically, we treat the eigenvalues as \*\*complex due to cross-coupling\*\* between \\(\\delta n\\) and \\(\\delta\\theta\\) and interpret \\(\\omega(k)\\) from the argument of the complex exponentials in the z-field.



For a conservative, hydrodynamic-like model, a natural choice is to have:



\- small \\(\\alpha\_2, \\beta\_2\\),

\- nonzero \\(\\eta\_2, \\gamma\_2\\) with a sign pattern that produces underdamped behaviour.



Here, we focus on matching the scale of \\(\\omega^2(k)\\) to CRFT, and we treat the damping separately.



\### 4.2 Leading-order approximation of \\(\\lambda\_\\pm\\)



For small k, we approximate:



\\\[

\\alpha(k^2) + \\beta(k^2)

\\approx (\\alpha\_2 + \\beta\_2)k^2 + O(k^4),

\\]

\\\[

\\sqrt{D(k^2)}

\\approx \\sqrt{C\_4}\\,k^2 + O(k^3) \\quad \\text{(formal series)}.

\\]



Then:



\\\[

\\lambda\_\\pm(k)

\\approx -\\frac{(\\alpha\_2 + \\beta\_2)}{2}k^2

\\pm \\frac{1}{2}\\sqrt{C\_4}\\,k^2

\+ O(k^3).

\\]



At this level, \\(\\lambda\_\\pm(k)\\) are both proportional to \\(k^2\\). If \\(\\sqrt{C\_4}\\) is \*\*imaginary\*\*, we get complex eigenvalues whose imaginary parts scale as \\(k^2\\); if \\(\\sqrt{C\_4}\\) is real, we get purely diffusive behaviour. However, the \*\*CRFT dispersion\*\* behaves as:



\\\[

\\omega(k) \\sim \\sqrt{g\\rho\_0}\\,|k| \\quad (k \\to 0),

\\]



which is \*\*linear in |k|\*\*, not in \\(k^2\\).



This tells us that the minimal model above (with both couplings \\(\\eta\\), \\(\\gamma\\) of order \\(k^2\\)) is still too symmetric to capture the desired \\(O(k)\\) scaling. We need one of the couplings to have a nonzero \\(k^0\\) component.



---



\## 5. Refined Minimal Model for Linear-in-k Behaviour



To obtain \\(\\omega(k) \\propto |k|\\) at small k, we adjust the ansatz:



\- Allow \*\*one coupling to be constant\*\* at leading order,

\- Keep the other coupling as \\(k^2\\).



A natural choice is:



\\\[

\\gamma(k^2) = \\gamma\_0 + O(k^2), \\quad \\gamma\_0 \\neq 0,

\\]

\\\[

\\eta(k^2) = \\eta\_2 k^2 + O(k^4).

\\]



Density → phase coupling has a nonzero constant piece (like a “pressure” term), and phase → density coupling is gradient-driven.



We still keep:



\\\[

\\alpha(k^2) = \\alpha\_2 k^2 + O(k^4),\\quad

\\beta(k^2) = \\beta\_2 k^2 + O(k^4),

\\]



and set \\(\\gamma\_0\\) to be \*\*sign-consistent\*\* with the CRFT acoustic-like term \\(g\\rho\_0\\).



\### 5.1 Discriminant with \\(\\gamma\_0 \\neq 0\\)



Now:



\\\[

\\gamma(k^2) = \\gamma\_0 + \\gamma\_2 k^2 + \\dots,\\quad

\\eta(k^2) = \\eta\_2 k^2 + \\dots.

\\]



Then:



\\\[

\\eta\\gamma

= (\\eta\_2 k^2)(\\gamma\_0 + \\gamma\_2 k^2 + \\dots)

= \\eta\_2\\gamma\_0 k^2 + O(k^4).

\\]



Meanwhile:



\\\[

\\left(\\alpha - \\beta\\right)^2

= (\\alpha\_2 - \\beta\_2)^2 k^4 + O(k^6).

\\]



So:



\\\[

D(k^2)

= (\\alpha - \\beta)^2 + 4\\eta\\gamma

= 4\\eta\_2\\gamma\_0 k^2

\+ (\\alpha\_2 - \\beta\_2)^2 k^4

\+ O(k^6).

\\]



For sufficiently small k, the leading piece is:



\\\[

D(k^2) \\approx 4\\eta\_2\\gamma\_0 k^2.

\\]



If \\(\\eta\_2\\gamma\_0 > 0\\), we get:



\\\[

\\sqrt{D(k^2)}

\\approx 2\\sqrt{\\eta\_2\\gamma\_0}\\,|k|\\left\[1 + O(k^2)\\right].

\\]



\### 5.2 Leading-order eigenvalues



Plugging into (3.1):



\\\[

\\lambda\_\\pm(k)

= -\\frac{\\alpha(k^2) + \\beta(k^2)}{2}

\\pm \\frac{1}{2}\\sqrt{D(k^2)}.

\\]



To leading orders:



\\\[

\\alpha(k^2) + \\beta(k^2)

\\approx (\\alpha\_2 + \\beta\_2)k^2,

\\]

\\\[

\\sqrt{D(k^2)} \\approx 2\\sqrt{\\eta\_2\\gamma\_0}\\,|k|.

\\]



Thus:



\\\[

\\lambda\_\\pm(k)

\\approx -\\frac{\\alpha\_2 + \\beta\_2}{2}k^2

\\pm \\sqrt{\\eta\_2\\gamma\_0}\\,|k|

\+ O(k^2).

\\tag{5.1}

\\]



If \\(\\alpha\_2, \\beta\_2\\) are relatively small, and \\(\\eta\_2\\gamma\_0 > 0\\), then:



\- One eigenmode has dominant behaviour

&nbsp; \\\[

&nbsp; \\lambda\_+(k) \\approx -\\Gamma(k) - i\\omega(k),

&nbsp; \\]

&nbsp; with \\(\\omega(k) \\approx \\sqrt{\\eta\_2\\gamma\_0}\\,|k|\\).

\- The other is more heavily damped or less strongly excited.



Hence, the \*\*leading-order frequency\*\* satisfies:



\\\[

\\omega^2(k) \\approx \\eta\_2\\gamma\_0 k^2,

\\]



which matches the CRFT constraint:



\\\[

\\omega^2(k) \\approx g\\rho\_0 k^2 \\quad (k \\to 0)

\\]



if we set:



\\\[

\\eta\_2\\gamma\_0 \\approx g\\rho\_0.

\\tag{5.2}

\\]



This is the key calibration relation for the \*\*acoustic slope\*\*.



---



\## 6. Higher-Order Terms: k⁴ and k⁶



To match the full CRFT polynomial up to k⁶:



\\\[

\\omega^2\_{\\text{CRFT}}(k)

= g\\rho\_0 k^2 + \\left(\\frac{1}{4} + \\lambda\\right)k^4 + \\beta k^6,

\\]



we must expand \\(\\lambda\_\\pm(k)\\) to higher orders.



From (5.1), the next corrections arise from:



\- higher terms in \\(\\sqrt{D(k^2)}\\) (coming from \\((\\alpha - \\beta)^2\\) and \\(\\gamma\_2, \\eta\_4\\)),

\- higher terms in \\(\\alpha, \\beta\\) (i.e. \\(\\alpha\_4, \\beta\_4\\)).



Symbolically, expand:



\\\[

\\sqrt{D(k^2)}

= 2\\sqrt{\\eta\_2\\gamma\_0}\\,|k|

\\left\[1 + d\_2 k^2 + d\_4 k^4 + O(k^6)\\right],

\\]



for some coefficients \\(d\_2, d\_4\\) determined by \\(\\alpha\_2, \\alpha\_4, \\beta\_2, \\beta\_4, \\gamma\_2, \\eta\_4\\).



Then:



\\\[

\\lambda\_\\pm(k)

= -\\frac{\\alpha\_2 + \\beta\_2}{2}k^2

\\pm \\sqrt{\\eta\_2\\gamma\_0}\\,|k|

\\left\[1 + d\_2 k^2 + d\_4 k^4 + \\dots\\right]

\+ O(k^2).

\\]



The corresponding \\(\\omega(k)\\) for the primary mode can be written as:



\\\[

\\omega(k)

\\approx \\sqrt{\\eta\_2\\gamma\_0}\\,|k|

\\bigl\[1 + e\_2 k^2 + e\_4 k^4 + \\dots\\bigr],

\\]



with \\(e\_2, e\_4\\) combinations of the underlying coefficients.



Squaring:



\\\[

\\omega^2(k)

\\approx \\eta\_2\\gamma\_0 k^2

\\left\[

1 + 2e\_2 k^2 + (2e\_4 + e\_2^2)k^4 + \\dots

\\right].

\\]



Matching term by term to CRFT gives:



\\\[

\\begin{aligned}

\\eta\_2\\gamma\_0 \&= g\\rho\_0, \\\\

2\\eta\_2\\gamma\_0 e\_2 \&= \\frac{1}{4} + \\lambda, \\\\

\\eta\_2\\gamma\_0(2e\_4 + e\_2^2) \&= \\beta.

\\end{aligned}

\\tag{6.1}

\\]



Here:



\- \\(e\_2, e\_4\\) are functions of \\(\\alpha\_2, \\alpha\_4, \\beta\_2, \\beta\_4, \\gamma\_2, \\eta\_4\\),

\- (6.1) is an \*\*algebraic system\*\* for these coefficients.



We do not solve this system in closed form here; instead we identify which combinations of LCRD micro-coefficients control:



\- the \*\*acoustic slope\*\* (k² term),

\- the \*\*quartic curvature\*\* (k⁴ term),

\- the \*\*sextic correction\*\* (k⁶ term).



---



\## 7. Mapping to Discrete LCRD Coefficients



At the discrete level, the micro-update rules are encoded in `stepper.py` through:



\- density flux coefficients \\(A\_1, A\_2, A\_3\\),

\- phase Laplacian coefficients \\(B\_1, B\_2,\\dots\\),

\- and any explicit n–θ couplings (e.g. a term \\(-G n\\) or a gradient-based coupling).



In the small-k, small-\\(\\Delta x\\) limit, these coefficients determine the continuum-level parameters:



\- \\(\\alpha\_2, \\alpha\_4,\\dots\\) (from density stencil, \\(A\_2, A\_3\\)),

\- \\(\\beta\_2, \\beta\_4,\\dots\\) (from phase stencil, \\(B\_2\\)),

\- \\(\\gamma\_0, \\gamma\_2\\) (from direct n→θ forcing),

\- \\(\\eta\_2, \\eta\_4\\) (from θ→n forcing via gradients).



At this stage, we treat \\(\\alpha\_2, \\alpha\_4, \\beta\_2, \\beta\_4, \\gamma\_0, \\gamma\_2, \\eta\_2, \\eta\_4\\) as \*\*effective parameters\*\*, to be mapped back to \\((A\_i, B\_i)\\) later via finite-difference analysis.



The key calibration relations from the low-k expansion are:



1\. \*\*Acoustic slope match\*\* (k² term):

&nbsp;  \\\[

&nbsp;  \\eta\_2\\gamma\_0 \\approx g\\rho\_0.

&nbsp;  \\]



2\. \*\*Quartic curvature match\*\* (k⁴ term):

&nbsp;  \\\[

&nbsp;  2\\eta\_2\\gamma\_0 e\_2 \\approx \\frac{1}{4} + \\lambda.

&nbsp;  \\]



3\. \*\*Sextic correction match\*\* (k⁶ term):

&nbsp;  \\\[

&nbsp;  \\eta\_2\\gamma\_0(2e\_4 + e\_2^2) \\approx \\beta.

&nbsp;  \\]



Where \\(e\_2, e\_4\\) are functions of the self-operators \\(\\alpha, \\beta\\) and higher-order couplings \\(\\gamma\_2, \\eta\_4\\).



Practically, one will:



\- choose a \*\*modest subset\*\* of these parameters to vary (e.g. \\(\\gamma\_0, \\eta\_2, \\beta\_2, \\alpha\_2\\)),

\- treat the remaining degrees of freedom as either zero or small,

\- solve (or numerically fit) the low-k dispersion coefficients to CRFT.



---



\## 8. Practical Calibration Strategy for LCRD v1



From the derivation, a conservative, staged calibration approach is:



1\. \*\*Stage 1: acoustic slope only (k² term)\*\*



&nbsp;  - Turn off most higher-order corrections:

&nbsp;    - set \\(\\alpha\_4 = \\beta\_4 = \\gamma\_2 = \\eta\_4 = 0\\),

&nbsp;  - keep only \\(\\gamma\_0\\) and \\(\\eta\_2\\) nonzero (plus small \\(\\alpha\_2, \\beta\_2\\) for stability),

&nbsp;  - tune \\(\\eta\_2\\gamma\_0\\) to satisfy

&nbsp;    \\\[

&nbsp;    \\eta\_2\\gamma\_0 \\approx g\\rho\_0.

&nbsp;    \\]

&nbsp;  - Implement corresponding discrete couplings (n→θ, θ→n) and verify via CG-T1 that the measured \\(\\omega(k)\\) has the correct linear-in-k slope.



2\. \*\*Stage 2: quartic curvature (k⁴ term)\*\*



&nbsp;  - Introduce \\(\\alpha\_4, \\beta\_4\\) (or \\(\\gamma\_2, \\eta\_4\\)) and compute the induced correction \\(e\_2\\).

&nbsp;  - Adjust these coefficients so that

&nbsp;    \\\[

&nbsp;    2\\eta\_2\\gamma\_0 e\_2 \\approx \\frac{1}{4} + \\lambda.

&nbsp;    \\]

&nbsp;  - Check that the CG-T1 measured \\(\\omega(k)\\) fits the CRFT curve up to k⁴.



3\. \*\*Stage 3: sextic correction (k⁶ term)\*\*



&nbsp;  - Introduce further corrections (e.g. via higher-order stencils or additional coupling terms).

&nbsp;  - Fit the sextic coefficient by adjusting the remaining free parameters such that

&nbsp;    \\\[

&nbsp;    \\eta\_2\\gamma\_0(2e\_4 + e\_2^2) \\approx \\beta.

&nbsp;    \\]



Throughout, we ensure:



\- stability of the discrete scheme (no blow-up of modes at high k),

\- small damping for the physical branch in the low-k regime,

\- consistency with the CRFT parameters used in the white paper/state-of-the-theory.



---



\## 9. Summary and Next Steps



This derivation demonstrates:



\- LCRD v1 must include \*\*one constant n→θ coupling\*\* (\\(\\gamma\_0\\)) and \*\*one gradient-driven θ→n coupling\*\* (\\(\\eta\_2 k^2\\)) to produce the correct \*\*linear-in-k\*\* acoustic behaviour.

\- Higher-order self-terms and couplings \\((\\alpha\_2, \\beta\_2, \\alpha\_4, \\beta\_4, \\gamma\_2, \\eta\_4)\\) control the \*\*k⁴\*\* and \*\*k⁶\*\* corrections.

\- Matching to the CRFT dispersion is implemented through the low-k expansion of \\(\\omega\_+^2(k)\\) and identifying the relationships (6.1) between micro-coefficients and CRFT parameters.



The immediate next technical steps are:



1\. Derive the explicit mapping from discrete LCRD stencils (`step\_density`, `step\_phase`) to the continuum coefficients \\(\\alpha\_i, \\beta\_i, \\gamma\_i, \\eta\_i\\).

2\. Propose a \*\*concrete LCRD v1 stepper\*\* (updated `stepper.py`) with:

&nbsp;  - a minimal set of tuned coefficients satisfying the k² slope constraint,

&nbsp;  - simple higher-order terms for exploratory k⁴, k⁶ matching.

3\. Implement LCRD v1, run CG-T1 again, and empirically validate the dispersion matching against the CRFT analytic curve.



This will provide a mathematically transparent path from the CRFT field-theoretic dispersion down to a concrete micro-dynamics candidate in the LCRD family.



