\# Phase 1b — Calculus Shapes (no physics claims)



Scope

\- Confirm the \*\*shape\*\* of the functional derivative of the amplitude-gradient

&nbsp; coherence term with ε-regularization, treating ϕ and ϕ\* as independent.

\- Do not assert equations of motion or conservation laws. Only algebraic and

&nbsp; variational identities are checked.



Setup

\- ϕ=q+ip; ρ=|ϕ|²; f=|ϕ|; regularized amplitude: fε := sqrt(ρ+ε²), ε>0 fixed.

\- Coherence density (Phase 1 form A): Cx\[ϕ] = λ (∂x fε)².



Target identity (formal Euler–Lagrange with respect to ϕ\*):

\- Let Lc := λ (∂x fε)². Then the Euler–Lagrange operator EL\_{ϕ\*}\[Lc] equals

&nbsp; EL\_{ϕ\*}\[Lc] = − λ (ϕ / fε) ∂xx fε

up to discarded total derivatives under periodic/decaying boundary conditions.

This matches the hand derivation:

&nbsp; δC = 2λ ∫ (∂x fε) ∂x(δfε) dx = −2λ ∫ (∂xx fε) δfε dx,

with δfε/δϕ\* = ϕ/(2 fε).



Gates

\- S1: Symbolic Euler–Lagrange (ϕ\*, ε-regularized) matches −λ (ϕ/fε) fε,xx exactly.

\- S2: No phase-gradient coherence term appears (same constraint as Phase 1).



