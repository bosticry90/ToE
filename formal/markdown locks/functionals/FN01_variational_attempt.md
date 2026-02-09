\# FN01\_variational\_attempt.md



“This document attempts to construct the minimal action S\[ψ] reproducing EQ-02 while incorporating FN-01. Failure is an acceptable and intended outcome.”



\## 0. Purpose and scope



\*\*Goal (Phase C1):\*\* Attempt variational closure for FN-01 (coherence functional) in a way that is consistent with the repository’s epistemic rules.



\*\*This document DOES:\*\*

\- Specify a minimal action principle for complex ψ that reproduces \*\*EQ-02\*\*.

\- Introduce a generic “coherence functional” FN-01 as an added term and derive the modified Euler–Lagrange equation.

\- State precise \*\*closure conditions\*\* under which FN-01 is admissible vs. obstructed.

\- Provide \*\*kill criteria\*\* (obstructions) that demote FN-01 cleanly if closure fails.



\*\*This document does NOT:\*\*

\- Claim physical correctness.

\- Assert that coherence is fundamental.

\- Commit to a unique FN-01 form unless forced.

\- Use Mathlib analytic differentiability; all calculus here is formal variational calculus (physics-style), and any formalization is deferred.



\*\*Authorities\*\*

\- Markdown role (intent authority): specify candidate actions, derivations, obstruction criteria.

\- Lean role (structural authority): (future) certify identities for the chosen FN-01 form (if any), and consistency lemmas.

\- Python role (behavioral authority): (future) probe numerical consequences once FN-01 is structurally closed.



Dependencies: EQ-02, DR-01, CT-01 (dispersion-preservation criterion).



---



\## 1. Locked target equation (must reproduce)



\*\*EQ-02 (locked):\*\*

\\\[

i \\,\\partial\_t \\psi = -\\frac{1}{2}\\Delta \\psi

\\]

in 2D with \\(\\Delta = \\partial\_{xx}+\\partial\_{yy}\\).



\*\*Hard requirement:\*\* Any “minimal action” must produce EQ-02 exactly when FN-01 is absent (λ = 0).



---



\## 2. Minimal action that reproduces EQ-02 (baseline)



Treat \\(\\psi\\) and \\(\\psi^\\\*\\) as independent fields.



Define the baseline action:

\\\[

S\_0\[\\psi,\\psi^\\\*] = \\int dt \\, d^2x \\;\\mathcal{L}\_0

\\]

with

\\\[

\\mathcal{L}\_0

=

\\frac{i}{2}\\left(\\psi^\\\*\\partial\_t\\psi - \\psi \\partial\_t\\psi^\\\*\\right)

-\\frac{1}{2}\\,|\\nabla\\psi|^2

\\]

where \\(|\\nabla\\psi|^2 = \\nabla\\psi^\\\*\\cdot\\nabla\\psi\\).



\*\*Formal Euler–Lagrange variation w.r.t. \\(\\psi^\\\*\\)\*\* yields:

\\\[

i\\,\\partial\_t\\psi = -\\frac{1}{2}\\Delta\\psi

\\]

assuming boundary terms vanish (periodic domain or sufficient decay).



This reproduces EQ-02 and serves as the reference for FN-01 coupling.



---



\## 3. Add FN-01 to the action (generic form)



Introduce FN-01 as an additive functional:

\\\[

S\[\\psi,\\psi^\\\*] = S\_0\[\\psi,\\psi^\\\*] + \\lambda \\, C\[\\psi,\\psi^\\\*]

\\]

where:

\- \\(\\lambda \\in \\mathbb{R}\\) is a tunable coupling constant (bookkeeping parameter).

\- \\(C\[\\psi,\\psi^\\\*]\\) is the hypothesized coherence functional (FN-01).



The modified Euler–Lagrange equation becomes:

\\\[

i\\,\\partial\_t\\psi

=

-\\frac{1}{2}\\Delta\\psi

+\\lambda \\,\\frac{\\delta C}{\\delta \\psi^\\\*}

\\]

So \*\*variational closure reduces to one question:\*\*

> Is \\( \\delta C/\\delta\\psi^\\\* \\) well-defined in the chosen formal calculus, and is its small-amplitude behavior consistent with DR-01 / CT-01?



---



\## 4. Closure conditions (what must be true for FN-01 to survive)



\### 4.1 Minimal closure condition (structural)

A candidate \\(C\\) is \*\*variationally closed\*\* (for this repository stage) if:

\- A formal expression for \\(\\delta C/\\delta \\psi^\\\*\\) can be written explicitly using integration by parts and the assumed boundary conditions.

\- The resulting term defines a PDE modification (local or nonlocal), with its assumptions stated.



\### 4.2 DR-01 compatibility condition (constraint pressure)

To preserve DR-01 under the ψ=0 linearization (CT-01 intent), the added term must satisfy:



\*\*CT-01-consistent requirement (variational form):\*\*

\\\[

\\left.\\frac{\\delta C}{\\delta \\psi^\\\*}\\right|\_{\\psi=0} = 0

\\quad\\text{and}\\quad

\\text{its Fréchet linearization at } \\psi=0 \\text{ contributes no linear term.}

\\]



Interpretation:

\- If \\(\\delta C/\\delta\\psi^\\\*\\) contains a term linear in \\(\\psi\\), \\(\\nabla\\psi\\), \\(\\Delta\\psi\\), etc. at ψ=0, then DR-01 is altered (Phase B forbids this if DR-01 is required unchanged).



\*\*This is the “kill switch”:\*\*

\- If every plausible coherence functional produces a nonzero linear term at ψ=0, FN-01 is not admissible under the DR-01 constraint.



\### 4.3 Explicit “iff” wording

Analytic linearization criterion (intended): DR-01 is preserved if and only if the added term’s linearization about psi=0 is identically zero (i.e., no linear component).



Structural substitute currently formalized in Lean (probe-relative): DR-01 coefficient-equality on the planeWave probe is unchanged if P(planeWave) = 0 (AdmissibleOnPlaneWave).



---



\## 5. Candidate FN-01 families (explicit templates + quick linearization check)



This section is a \*menu of candidates\*; selecting one commits the project to computing \\(\\delta C/\\delta\\psi^\\\*\\) and checking CT-01 consistency.



\### Candidate A (amplitude-weighted phase-gradient penalty)

Idea: penalize rapid phase variation where amplitude is present.



Using \\(\\psi=\\rho e^{i\\theta}\\), define:

\\\[

C\_A\[\\psi] = \\int dt\\,d^2x\\; \\rho^2 |\\nabla\\theta|^2

\\]

\*\*Issue:\*\* rewriting in ψ,ψ\* introduces \\(\\nabla\\psi\\) and \\(\\nabla\\psi^\\\*\\) divided by \\(|\\psi|^2\\), which is singular at ψ=0.



\*\*Kill test A:\*\* if the functional is not well-defined at ψ=0, it is incompatible with the project’s ψ=0 linearization anchor and should be rejected or regularized.



\### Candidate B (quartic gradient penalty; no linear term under the stated boundary assumptions)



C\_B\[psi] = integral dt d^2x of ( |psi|^2 \* |grad psi|^2 )



Under amplitude scaling psi → ε psi, this functional scales as O(ε^4).

Consequently, its variational derivative δC\_B / δpsi\* scales as O(ε^3),

and therefore contributes no linear term about psi = 0.



Variation produces only nonlinear corrections, with representative terms such as:

|psi|^2 \* Delta psi

and

psi \* (grad psi\* · grad psi)



\*\*Pass test B (CT-01):\*\* preserves DR-01 under psi = 0 linearization.



Definition (Candidate B):



C\_B\[psi] = integral over (t, x, y) of ( |psi|^2 \* |grad psi|^2 )



Interpret |psi|^2 = psi\* psi



Interpret |grad psi|^2 = grad(psi\*) · grad(psi) = (∂x psi\*)(∂x psi) + (∂y psi\*)(∂y psi)



Boundary assumptions (required for integration by parts):



Either periodic boundary conditions in x and y, or sufficient decay at spatial infinity,

so that all spatial boundary terms vanish.



Time endpoints are held fixed (δpsi\* = 0 at initial/final time) or equivalently we

ignore total time-derivative boundary terms since C\_B has no time derivatives.



Goal:



Compute δC\_B / δpsi\* such that:

δC\_B = integral dt d^2x \[ (δC\_B/δpsi\*) \* δpsi\* + (δC\_B/δpsi) \* δpsi ]



Variation with respect to psi\* (treat psi and psi\* independent):

Write the integrand:



f = (psi\* psi) \* (grad psi\* · grad psi)



Compute δf from psi\* variations:



Variation of the amplitude factor (psi\* psi):



δ(psi\* psi) = (δpsi\*) psi



Contribution:



(δpsi\*) psi \* (grad psi\* · grad psi)



Variation of grad psi\*:



δ(grad psi\*) = grad(δpsi\*)



Contribution:



(psi\* psi) \* (grad(δpsi\*) · grad psi)



Integrate the second contribution by parts in space:



integral (psi\* psi) \* (grad(δpsi\*) · grad psi)

= - integral δpsi\* \* div( (psi\* psi) \* grad psi )

(boundary term vanishes by assumptions)



Combine both contributions:



δC\_B = integral dt d^2x δpsi\* \* \[ psi \* (grad psi\* · grad psi) - div( |psi|^2 \* grad psi ) ]



Therefore the variational derivative is:



FINAL RESULT:



δC\_B / δpsi\* = psi \* (grad psi\* · grad psi) - div( |psi|^2 \* grad psi )



Equivalent expanded form (sometimes useful):



div( |psi|^2 \* grad psi ) = (grad |psi|^2) · (grad psi) + |psi|^2 \* Delta psi



grad |psi|^2 = (grad psi\*) psi + psi\* (grad psi)



So:



δC\_B / δpsi\* = psi \* (grad psi\* · grad psi)

\- (grad |psi|^2) · (grad psi)

\- |psi|^2 \* Delta psi



CT-01 / DR-01 linearization check (order counting about psi = 0):



Each term in δC\_B/δpsi\* contains at least one explicit factor of psi and at least one

additional factor of psi, grad psi, or grad psi\*.



Under scaling psi -> ε psi, δC\_B/δpsi\* scales as O(ε^3).



Therefore δC\_B/δpsi\* contributes no linear term at psi = 0 and preserves DR-01 under

the psi=0 linearization criterion.



Modified equation of motion if Candidate B is adopted:



i ∂t psi = -(1/2) Delta psi + λ \* \[ psi \* (grad psi\* · grad psi) - div( |psi|^2 \* grad psi ) ]



Status impact (Phase C1 decision rule):



This derivation is explicit and uses only standard integration by parts plus stated

boundary assumptions.



Candidate B is variationally closed and CT-01-consistent.



FN-01 may remain Hypothesis, but is now “variationally closed for Candidate B” at the

Markdown level (Lean formalization deferred).



\### Candidate C (quadratic Laplacian penalty; risky)

C\_C\[psi] = integral dt d^2x of ( |Delta psi|^2 )



This functional is quadratic in psi and produces a linear contribution to the

equation of motion. Under formal variation (with boundary terms discarded):



δC\_C / δpsi\* = − Delta^2 psi

\*\*Kill test C:\*\* violates CT-01 because it introduces a linear k^4 correction and therefore breaks DR-01.



\### Candidate D (nonlocal coherence penalty; risky)

\\\[

C\_D\[\\psi] = \\int dt\\,d^2x\\,d^2x'\\; K(x-x')\\,\\psi^\\\*(x)\\psi(x')

\\]

Variation yields a \*\*linear\*\* convolution operator:

\\\[

\\frac{\\delta C\_D}{\\delta\\psi^\\\*}(x) = \\int d^2x'\\; K(x-x')\\psi(x')

\\]



\*\*Kill test D:\*\* violates CT-01 (linear nonlocal term alters dispersion).



---



\## 6. Variational derivation workflow (what to actually do next)



\### Step 1 — Choose one candidate C (or define FN-01 explicitly)

Record:

\- Exact integrand.

\- Domain/boundary assumptions.

\- Any regularization at ψ=0.



\### Step 2 — Compute \\(\\delta C/\\delta\\psi^\\\*\\) explicitly

Use the standard identity:

\\\[

\\delta C = \\int dt\\,d^2x\\;\\left(\\frac{\\delta C}{\\delta\\psi}\\delta\\psi + \\frac{\\delta C}{\\delta\\psi^\\\*}\\delta\\psi^\\\*\\right)

\\]

and integrate by parts to isolate \\(\\delta\\psi^\\\*\\).



\### Step 3 — Write the modified equation of motion

\\\[

i\\,\\partial\_t\\psi

=

-\\frac{1}{2}\\Delta\\psi

+\\lambda\\,\\frac{\\delta C}{\\delta\\psi^\\\*}

\\]



\### Step 4 — Apply the Phase B constraint (CT-01)

\- Linearize the RHS about ψ=0 (formal series / order counting).

\- If any linear term remains, FN-01 fails under the DR-01 preservation requirement.



---



\## 7. Decision gates (success and failure are both acceptable)



\### Outcome 1 (success)

FN-01 is \*\*variationally closed\*\* and \*\*CT-01 consistent\*\*:

\- \\(\\delta C/\\delta\\psi^\\\*\\) derived explicitly.

\- No linear term at ψ=0.

\- FN-01 remains a viable hypothesis (can upgrade to Structural later if formalized).



\### Outcome 2 (clean failure)

FN-01 is \*\*killed\*\* for one of these reasons:

\- Not well-defined at ψ=0 (singular functional).

\- Cannot write \\(\\delta C/\\delta\\psi^\\\*\\) without uncontrolled assumptions.

\- Produces a linear term and violates CT-01 / breaks DR-01.

\- Requires ad hoc terms to “fix” dispersion (not allowed).



If killed, record:

\- Explicit obstruction statement.

\- Minimal counterexample (e.g., introduces \\(V\\psi\\) or \\(\\Delta^2\\psi\\) linearization).



---



\## 8. Lean hooks (placeholders; no calculus formalization required yet)



If FN-01 survives and you choose a specific algebraic candidate (e.g., Candidate B),

Lean can later support:

\- definitional expansions (no analysis),

\- order-counting lemmas (e.g., “term is ≥ cubic in ψ” in an abstract algebraic sense),

\- probe-relative admissibility (similar style to PhaseB.DispersionPreservation).



\*\*Out of scope for Lean at this stage:\*\*

\- Mathlib differentiability development for complex fields over ℝ³.

\- Fréchet derivative formalization.



---



\## 9. Minimal immediate deliverable



At minimum, to complete Phase C1 you must produce one of:



1\) A fully written \\(\\delta C/\\delta\\psi^\\\*\\) for a chosen FN-01 candidate and show CT-01 consistency, \*\*or\*\*

2\) An explicit obstruction that prevents any reasonable FN-01 from being both variationally closed and DR-01-preserving.



Either result closes Phase C1.





