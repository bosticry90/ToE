=====================================================================



EQUATION INVENTORY — MASTER



=====================================================================







=====================================================================

FOUNDATIONAL FIRST-ORDER UCFF / CRFT EVOLUTION EQUATION

=====================================================================



This entry defines the canonical first-order evolution equation for the

Unified Coherent Field Framework (UCFF) / Coherence-Regularized Field

Theory (CRFT).



This equation is foundational. All first-order dynamics, limiting cases,

reductions, numerical solvers, dispersion relations, and higher-order

extensions are defined relative to this object.



The equation is specified in residual form. Residual form is the

canonical representation used for symbolic derivation, variational

calculus, and automated verification.







---------------------------------------------------------------------

FIELD AND VARIABLES

---------------------------------------------------------------------



φ(x,t) — complex scalar field  

x — one-dimensional spatial coordinate  

t — physical time  



Density:

|φ|² = φ\* φ







---------------------------------------------------------------------

PARAMETERS (GLOBAL FIRST-ORDER LAYER)

---------------------------------------------------------------------



g — cubic nonlinear coupling constant  

lam — fourth-order dispersion coupling  

beta — sixth-order dispersion coupling  

ρ0 — homogeneous background density used for linearization and dispersion analysis  



All parameters are real-valued. No assumptions about sign are imposed at

this level.







---------------------------------------------------------------------

CANONICAL FIRST-ORDER EQUATION (RESIDUAL FORM)

---------------------------------------------------------------------



The first-order UCFF / CRFT evolution equation is defined by the vanishing

of the residual:



R₁\[φ] =

&nbsp;   i ∂t φ

&nbsp; + (1/2) ∂xx φ

&nbsp; − g |φ|² φ

&nbsp; + lam ∂xxxx φ

&nbsp; + beta ∂xxxxxx φ

&nbsp; = 0



This equation is the authoritative definition of first-order dynamics in

the theory.







---------------------------------------------------------------------

LIMITING CASES (INFORMATIONAL CONTINUITY)

---------------------------------------------------------------------



Cubic NLSE / Gross–Pitaevskii limit:



Setting:

lam = 0  

beta = 0  



yields:

i ∂t φ + (1/2) ∂xx φ − g |φ|² φ = 0







Linear Schrödinger limit:



Setting:

g = 0  

lam = 0  

beta = 0  



yields:

i ∂t φ + (1/2) ∂xx φ = 0







---------------------------------------------------------------------

STATUS

---------------------------------------------------------------------



This equation is locked as the foundational first-order UCFF / CRFT

evolution equation and is enforced by executable tests.







=====================================================================

FIRST-ORDER DISPERSION (ω² FORM)

=====================================================================



Linearizing the first-order equation about a homogeneous background

density ρ0 and considering plane-wave solutions of the form:



φ(x,t) = A exp(i (k x − ω t))



yields the first-order dispersion relation specified at the level of ω²:



ω²(k) = (k² / 2)² + (g ρ0) k² + lam k⁴



The sixth-order coupling beta does not appear in the first-order

dispersion.



This ω²(k) expression is treated as the canonical dispersion object for

the first-order layer.







=====================================================================

CANONICAL SECOND-ORDER TIME-DOMAIN UCFF / UEFM EQUATION

=====================================================================



This entry defines the canonical second-order-in-time (time-domain)

UCFF / UEFM equation family as represented in the symbolic framework.



Canonical time-domain statements use:

\- a φ\_tt-based residual-form equation, and

\- ω²(k) dispersion objects.



Operational numerical realizations are excluded from this section and

are documented separately.







---------------------------------------------------------------------

FIELD AND VARIABLES

---------------------------------------------------------------------



φ(x,t) — complex scalar field  

x — one-dimensional spatial coordinate  

t — physical time  



Density:

|φ|² = conjugate(φ) \* φ







---------------------------------------------------------------------

PARAMETERS (CANONICAL TIME-DOMAIN LAYER)

---------------------------------------------------------------------



g — cubic nonlinear coupling constant  

lam — fourth-order spatial-structure coupling  

beta — sixth-order spatial-structure coupling  

ρ0 — homogeneous background density used for linearization and dispersion analysis  



All parameters are real-valued. No assumptions about sign are imposed at

this level.







---------------------------------------------------------------------

CANONICAL SECOND-ORDER TIME-DOMAIN EQUATION (RESIDUAL FORM)

---------------------------------------------------------------------



The canonical second-order UCFF / UEFM time-domain equation is presented

in residual form as a symbolic expression with explicit dependence on x

and t, and with the following required structural ingredients present:



\- second time derivative:        ∂t² φ

\- second spatial derivative:     ∂x² φ

\- fourth spatial derivative:     ∂x⁴ φ

\- sixth spatial derivative:      ∂x⁶ φ

\- cubic nonlinearity in explicit density form:

&nbsp; g \* (conjugate(φ) \* φ) \* φ



Accordingly, the canonical residual is an expression of the form:



R₂\[φ] =

&nbsp;   ( ∂t² φ )

&nbsp; + (terms containing ∂x² φ)

&nbsp; + (terms containing ∂x⁴ φ, including lam)

&nbsp; + (terms containing ∂x⁶ φ, including beta)

&nbsp; + g \* (conjugate(φ) \* φ) \* φ

&nbsp; = 0



This is a canonical symbolic definition. It does not assert a variational

derivation or coefficient-level proof.







---------------------------------------------------------------------

CANONICAL SECOND-ORDER DISPERSION (ω² FORM)

---------------------------------------------------------------------



The canonical dispersion associated with the second-order time-domain

layer is represented as ω²(k) Equality objects with the following

structural constraints:



\- It is a symbolic equality.

\- It contains no x or t dependence.

\- Its right-hand side contains k², k⁴, and k⁶.

\- Its right-hand side contains lam and beta.



A natural-units ω²(k) dispersion object is also defined with the same

structural constraints and with explicit hbar and m removed.







---------------------------------------------------------------------

STATUS

---------------------------------------------------------------------



This entry is locked as the canonical second-order time-domain UCFF /

UEFM definition at the level of residual-form structure and ω²(k)

dispersion structure.







=====================================================================

OPERATIONAL NUMERICS LAYER (HIGHER-ORDER SPATIAL DISPERSION)

=====================================================================



This section documents the operational numerical evolution equation used

for simulation. It is not a canonical time-domain statement.



In this context, “second-order” refers to inclusion of fourth- and

sixth-order spatial derivatives, not to a second-order-in-time equation.







---------------------------------------------------------------------

OPERATIONAL EVOLUTION EQUATION (FIRST-ORDER-IN-TIME)

---------------------------------------------------------------------



The operational evolution equation stepped by numerical integrators is:



i ∂t φ = − (1/2) ∂xx φ

&nbsp;        + lam ∂xxxx φ

&nbsp;        + beta ∂xxxxxx φ

&nbsp;        + g |φ|² φ



This equation is written in solved-for form because it is advanced

directly by numerical integrators.







---------------------------------------------------------------------

OPERATIONAL LINEAR DISPERSION (ω FORM)

---------------------------------------------------------------------



In the linear regime (g = 0), plane-wave solutions yield the operational

dispersion relation:



ω(k) = 0.5 k² + lam k⁴ + beta k⁶



This ω(k) statement is operational and must not be conflated with the

canonical ω²(k) dispersion objects.







---------------------------------------------------------------------

STATUS

---------------------------------------------------------------------



The operational numerics layer is locked by executable tests and is

documented separately from the canonical time-domain theory.







=====================================================================

2D CP–NLSE LINEAR DISPERSION LOCK (CRFT C6)

=====================================================================



This entry documents the locked two-dimensional plane-wave dispersion

relation for the CP–NLSE in the linear (g = 0) regime.



Governing equation (operational form):



i ∂t ψ = − (1/2) (∂xx ψ + ∂yy ψ)



Plane-wave dispersion relation:



ω(kx, ky) = 1/2 (kx² + ky²)



Validation tolerance:



|ω\_num − ω\_th| / ω\_th < 1.0e−1



Observed validation result:



rel\_error = 5.755e−02 < 1.0e−01



This lock applies strictly to the linear Schrödinger regime and does not

assert any nonlinear or canonical second-order-in-time dispersion in two

dimensions.







=====================================================================

END EQUATION INVENTORY — MASTER

=====================================================================



