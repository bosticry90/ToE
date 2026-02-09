\# PHASE 2 — Symbolic Residuals, Continuity, Dispersion (ε-propagating)



\*\*Phase-1 choice carried forward:\*\* Coherence density is \*\*amplitude-gradient only\*\*  

C\_x\[ϕ] = λ (∂\_x |ϕ|)^2, with |ϕ| = f = √ρ, ρ = |ϕ|^2.



\*\*Regularization rule (propagate ε):\*\*  

Every occurrence of |ϕ| in a denominator is replaced by  

f\_ε := sqrt(ρ + ε^2), with fixed ε ≈ 1e-6 (symbolic positive).



\*\*Lagrangian (1D):\*\*

ℒ = −(ħ²/2m) |∂ₓϕ|² − ħ ρ ∂ₜθ + (λ/4ρ)(∂ₓρ)² + U(ρ)



\*\*Time term encoding (real form, no arg):\*\*  

−ħ ρ ∂ₜθ  ≡  − (ħ / 2i) (ϕ\* ∂ₜϕ − ϕ ∂ₜϕ\*) · ( ρ / (ρ + ε²) )



This equals −ħ · Im(ϕ\* ∂ₜϕ) scaled by ρ/(ρ+ε²). In the ε→0 limit, it

reduces to the standard Schrödinger time term.



\*\*Targets in Phase-2:\*\*

(i) EL residual matches:

(ħ²/2m) ϕₓₓ + iħ ϕ\_t − ϕ U\_ρ(ρ) − λ (ϕ/f\_ε) f\_ε,ₓₓ  =  0



(ii) Continuity identity:

∂ₜρ + ∂ₓ J = 0, with J := (ħ/m) Im(ϕ\* ϕₓ)



(iii) Linear dispersion near ρ₀:

ω² = c² k² + k⁴ (ħ²/2m + λ),  c² := ρ₀ U′\_ρ(ρ₀)/m



