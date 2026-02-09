\# UCFF — Phase 0 Canonical Spec (Frozen)



This spec freezes the first-order, 1-D, non-relativistic core used in Phases 1–9.



\## Equations (Phase 9 freeze)



\*\*Fields and symbols:\*\* x,t; ϕ(x,t)=q+ip; ρ=|ϕ|²; θ=arg ϕ; f=|ϕ|; U(ρ); λ≥0; ħ; m; J; c; ξ.



1\) \*\*Lagrangian\*\*

\\\[

\\mathcal L = -\\frac{\\hbar^2}{2m}|\\partial\_x \\phi|^2 - \\hbar \\rho\\,\\partial\_t \\theta + \\frac{\\lambda}{4\\rho}(\\partial\_x \\rho)^2 + U(\\rho).

\\]



2\) \*\*Hamiltonian\*\*

\\\[

\\mathcal H = \\frac{\\hbar^2}{2m}|\\partial\_x \\phi|^2 + \\frac{\\lambda}{4\\rho}(\\partial\_x \\rho)^2 + U(\\rho).

\\]



3\) \*\*(EOM–ϕ)\*\* 

\\\[

\\frac{\\hbar^2}{2m}\\,\\partial\_{xx}\\phi + i\\hbar\\,\\partial\_t\\phi - \\phi\\,U'(\\rho) - \\lambda\\frac{\\phi}{|\\phi|}\\,\\partial\_{xx}|\\phi| = 0.

\\]



4\) \*\*(CONT)\*\* 

\\\[

\\partial\_t\\rho + \\partial\_x\\!\\left(\\frac{\\hbar\\rho}{m}\\,\\partial\_x\\theta\\right) = 0,\\quad J=\\frac{\\hbar\\rho}{m}\\,\\partial\_x\\theta.

\\]



5\) \*\*(DISP)\*\* 

\\\[

\\omega^2 = c^2k^2 + \\big(\\tfrac{\\hbar^2}{2m}+\\lambda\\big)k^4,\\quad

c^2=\\frac{\\rho\_0 U'(\\rho\_0)}{m},\\quad

\\xi^2=\\frac{\\tfrac{\\hbar^2}{2m}+\\lambda}{c^2}.

\\]



6\) \*\*Real–symplectic check\*\*  

\\(\\phi=q+ip,\\ \\rho=q^2+p^2\\),

\\\[

\\mathcal H(q,p)=\\frac{\\hbar^2}{2m}\\big((\\partial\_x q)^2+(\\partial\_x p)^2\\big)+\\frac{\\lambda}{4\\rho}(\\partial\_x\\rho)^2+U(\\rho),

\\quad \\partial\_t q=\\delta\\mathcal H/\\delta p,\\ \\partial\_t p=-\\delta\\mathcal H/\\delta q.

\\]



7\) \*\*Natural units\*\*: set \\(\\hbar=m=1\\) everywhere.



\## Demoted/Non-claims (Phase 8)

No relativistic covariance; no entropy–coherence duality; no alternative coherence densities; no extra Noether currents beyond continuity and energy.



\## Validation gates

All equivalence, continuity, dispersion, positivity, and unit tests in /tests must pass.



