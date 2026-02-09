\# Variation lemma (coherence) and continuity lemma



Let f=|ϕ|=√(ϕϕ\*). Then ∂f/∂ϕ\* = ϕ/(2f). For

C\_x\[ϕ] = λ ∫ (∂ₓ f)² dx

we vary and integrate by parts (periodic BC):

δC = 2λ∫(∂ₓ f)(∂ₓ δf)dx = −2λ∫(∂ₓₓ f) δf dx.

Using δf = (ϕ δϕ\* + ϕ\* δϕ)/(2f), read off

δC/δϕ\* = −λ (ϕ/f) ∂ₓₓ f = −λ (ϕ/|ϕ|) ∂ₓₓ|ϕ|.

Regularized form replaces f by f\_ε=√(|ϕ|²+ε²), giving

δC\_ε/δϕ\* = −λ (ϕ/|ϕ|\_ε) ∂ₓₓ|ϕ|\_ε,

which → the unregularized expression for H¹ fields with isolated nodes.



Write ϕ = f e^{iθ}. The imaginary part of the EL equation yields

ħ ∂ₜ(f²) + (ħ²/m) ∂ₓ(f² ∂ₓθ) = 0.

With ρ=f² and J=(ħρ/m)∂ₓθ we get the continuity law

∂ₜρ + ∂ₓJ = 0,

and ∂ₜ∫Ω ρ dx = 0 by periodic BC.



