# \# UCFF — First-Order Form (v0.1-FO)

# 

# \## Fields and parameters

# \- ϕ(x,t) ∈ ℂ, q=Reϕ, p=Imϕ, ϕ=q+ip.

# \- f=|ϕ|, ρ=|ϕ|²=f², θ=argϕ with ϕ= f e^{iθ}.

# \- U(ρ): real C² near ρ₀.

# \- ħ, m>0, λ≥0, ε≈10⁻⁶ (node regularization).

# \- c²(ρ₀)=ρ₀ U′(ρ₀)/m, ξ²=(ħ²/2m+λ)/c².

# 

# \## Densities

# \\\[

# \\mathcal L = -\\frac{\\hbar^2}{2m} |\\partial\_x \\phi|^2 - \\hbar \\rho\\, \\partial\_t \\theta + \\frac{\\lambda}{4\\rho}(\\partial\_x \\rho)^2 + U(\\rho).

# \\]

# \\\[

# \\mathcal H =  \\frac{\\hbar^2}{2m} |\\partial\_x \\phi|^2 + \\frac{\\lambda}{4\\rho}(\\partial\_x \\rho)^2 + U(\\rho).

# \\]

# 

# \## EOM (first order, complex form)

# \\\[

# \\frac{\\hbar^2}{2m}\\,\\partial\_{xx}\\phi + i\\hbar\\,\\partial\_t \\phi - \\phi\\,U'(\\rho) - \\lambda\\,\\frac{\\phi}{|\\phi|\_\\varepsilon}\\,\\partial\_{xx}|\\phi|\_\\varepsilon=0.

# \\]

# 

# \## Continuity and current

# \\\[

# J=\\frac{\\hbar\\rho}{m}\\,\\partial\_x\\theta,\\qquad \\partial\_t\\rho+\\partial\_x J=0.

# \\]

# 

# \## Linear dispersion about \\(\\rho\_0\\)

# \\\[

# \\omega^2 = c^2 k^2 + k^4\\Big(\\frac{\\hbar^2}{2m}+\\lambda\\Big),\\qquad c^2=\\frac{\\rho\_0 U'(\\rho\_0)}{m}.

# \\]

# 

# \## Units

# Physical: \\(\[x]=L, \[t]=T, \[\\hbar]=L^2/T, \[m]=1, \[\\phi]=L^{-1/2}, \[\\rho]=L^{-1}\\).

# Natural: set \\(\\hbar=m=1\\Rightarrow J=\\rho\\,\\partial\_x\\theta, \\mathcal H=\\tfrac12|\\partial\_x\\phi|^2+\\frac{\\lambda}{4\\rho}(\\partial\_x\\rho)^2+U(\\rho)\\).



