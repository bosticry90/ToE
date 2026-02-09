EXTENDED CRFT TEST FAMILY (C5–C9)
Local Sound-Density Approximation (LSDA)
and CRFT-Limit Reconstruction

All content is plain text and audit-ready.


============================================================
0. Context and Scope
============================================================

This test family extends the validated CRFT core (C1–C4) into
multi-field, multi-dimensional, diagnostic, turbulence, and
χ-coupling regimes.

The following documents are authoritative:

• equation_inventory_finalv7.md
• state_of_the_theoryv7.md
• crft_reconstruction_v2.md
• CRFT_Test_Family_v1.md (C1–C4)
• ν_eff mapping from LSDA long-run ν-lock tests
• All LSDA T1–T10 microphysics

C1–C4 validated the 1D CP–NLSE CRFT branch:

• C1 — linear dispersion (PASS)  
• C2 — invariant preservation (PASS)  
• C3 — soliton propagation stability (PASS)  
• C4 — coherence functional invariance (PASS)

C5–C9 extend this foundation to:

• C5 — multi-field hydrodynamic consistency  
• C6 — 2D CP–NLSE invariants and dispersion  
• C7 — metric diagnostics from CRFT data  
• C8 — turbulence taxonomy diagnostics  
• C9 — φ–χ coupled-field stability


============================================================
C5 — Multi-Field Hydrodynamic Reconstruction (1D)
============================================================

Purpose:
Verify that the CRFT first-order CP–NLSE branch reproduces the
hydrodynamic triplet (ρ, u, θ) and satisfies the validated CRFT
continuum system to numerical tolerance.

Fields:

• φ(x,t) — CP–NLSE field already validated in C1–C4  
• ρ(x,t)  = |φ|²  
• θ(x,t)  = unwrapped arg(φ)  
• u(x,t)  = ∂x θ  

CRFT continuum equations (authoritative from state_of_the_theoryv7):

    ρ_t = −∂x(ρ u)
    θ_t = −u θ_x − g_eff ρ
    u_t = −∂x(½u²) − ∂x(g_eff ρ)

with:

    rho0 = 1.0
    g_eff = 9.8696
    lam = 0
    beta = 0
    ν_eff ≈ 0.46 ν_code

Test configuration:

• Use 1D CRFT grid identical to C1–C4.  
• Initialize φ = √rho0 [1 + ε cos(kx)] with ε ≪ 1.  
• Integrate using validated CP–NLSE RHS and RK4 solver.

Diagnostics:

• Compute residuals R_ρ and R_u:

      R_ρ = ρ_t + ∂x(ρ u)
      R_u = u_t + ∂x(½u²) + ∂x(g_eff ρ)

• Define normalized errors:

      E_ρ = max_x |R_ρ| / max_x |ρ_t|
      E_u = max_x |R_u| / max_x |u_t|

Pass criteria (spec):

• E_ρ, E_u ≪ 1 (target 1e–2 or better depending on resolution)


============================================================
C6 — 2D CP–NLSE Invariants and Dispersion
============================================================

Purpose:
Extend CRFT to 2D and verify:

• 2D norm preservation  
• 2D dispersion relation consistent with the discrete 2D Laplacian

2D CP–NLSE prototype (consistent with equation_inventory_finalv7):

    φ_t = −i [ ½ ∇²φ − g_eff (|φ|² − rho0) φ ]

with:

    ∇² = ∂xx + ∂yy
    rho0 = 1.0
    g_eff = 9.8696

Norm:

    N_2D(t) = ∫∫ |φ|² dx dy

Test configuration:

• Periodic 2D box  
• Plane wave or localized Gaussian initial condition  
• Track N_2D(t) drift  
• Extract ω_num from time-series at a fixed grid point  
• Compare with ω_th implied by ∇² discretization

Pass criteria (spec):

• drift_N ≪ 1 (target ≤ 1e−3)  
• |ω_num − ω_th| / |ω_th| < O(1e−1) for early 2D prototypes


============================================================
C7 — Acoustic Metric Diagnostics
============================================================

Purpose:
Define a purely diagnostic, non-physical metric derived from
CRFT hydrodynamic fields, consistent with CRFT internal geometry.

Effective sound speed:

    c_s² = g_eff ρ

Diagnostic metric components:

    g_tt = −(c_s² − |u|²)
    g_tx = −u_x
    g_ty = −u_y
    g_xx = 1
    g_yy = 1

Diagnostics:

• Verify fields finite  
• Check g_tt < 0 consistent with |u| < c_s  
• Check det(g) < 0 (Lorentz-type signature diagnostic)

Pass criteria (spec):

• All diagnostic inequalities satisfied pointwise


============================================================
C8 — Turbulence Taxonomy Diagnostics
============================================================

Purpose:
Characterize nonlinear regimes of CRFT simulations using
structural descriptors without external physical exponents.

Spectral diagnostics:

    Eφ(k) = |φ̂(k)|²
    Eρ(k) = |ρ̂(k)|²
    Eu(k) = |û(k)|²

Scale partitioning:

• Track energy content across (k_low, k_mid, k_high)

Coherent structure indicators:

• Thresholded detection of localized high-ρ or high-|φ| packets  
• Count, width, and lifetimes

Use cases:

• Identify simple linear waves  
• Weak turbulence  
• Coherent turbulence (high PCI, low–mid SCI balance)

No specific external power law is enforced.


============================================================
C9 — φ–χ Coupling Stability
============================================================

Purpose:
Prototype multi-field CRFT extension and determine whether
small coupling preserves stability.

Coupled system (consistent with Extended_CRFT_v1):

    φ_t = R_φ(φ) + i γ χ
    χ_t = −i ω_χ χ + i γ φ

Diagnostics:

• Track:

      N_φ(t) = ∫ |φ|² dV
      N_χ(t) = ∫ |χ|² dV
      E_tot(t) = N_φ + N_χ

• Compare γ = 0 baseline with γ small

Pass criteria (spec):

• N_φ, N_χ, E_tot remain bounded  
• Deviations scale smoothly with γ  
• No runaway growth for small γ


============================================================
END OF EXTENDED CRFT TEST FAMILY (C5–C9 SPEC)
============================================================
