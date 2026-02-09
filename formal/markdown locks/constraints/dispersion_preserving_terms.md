\# Dispersion-preserving vs dispersion-breaking perturbations (Phase B1)



\## Goal

Use DR-01 as a constraint on allowable extensions of EQ-01 by classifying perturbations

according to whether they preserve the EQ-02 linearization and thus preserve DR-01.



\## Rule (linearization criterion)

Let EQ-01 be modified by adding a perturbation term P\[ψ].

DR-01 is preserved (unchanged) iff the linearization of P\[ψ] about ψ=0 is identically zero.



Equivalently: P\[ψ] must start at quadratic/cubic order in ψ and its derivatives.

Any nonzero linear component changes the dispersion and is inadmissible if DR-01 is required.



\## Dispersion-preserving families (no linear component at ψ=0)

\- Cubic NLS term: g |ψ|^2 ψ

\- Higher-order nonlinearities: α |ψ|^4 ψ, etc.

\- Nonlinear gradient terms with vanishing small-amplitude limit, e.g.:

&nbsp; λ F(|ψ|,|∇ψ|,...) ψ with F(0,0,...) = 0

\- Any coherence penalty explicitly constructed so its first Frechet derivative at ψ=0 is zero.



\## Dispersion-breaking families (inadmissible if DR-01 must remain unchanged)

These introduce a linear component and therefore modify ω(k):

\- +V ψ (constant potential / mass shift)

\- +i γ ψ (linear damping or gain)

\- +v·∇ψ (advection / drift; introduces k-linear term)

\- +α Δ² ψ or other higher linear derivatives (introduces k^4, ...)

\- Anisotropic Laplacian coefficients (changes weighting of kx, ky)

\- Any nonlocal linear operator acting on ψ (kernel convolution)

\- Any “coherence penalty” whose linearization is nonzero (e.g., contains ψ, ∇ψ, Δψ linearly).



\## Evidence hooks

\- Python: tests verify coefficient-equality identity on plane waves (structural-numeric).

\- Lean: A2/A3 provide definitional equivalences and operator-level reductions; Phase B will add

&nbsp; a classification layer that marks whether a proposed P\[ψ] has a linear part.



