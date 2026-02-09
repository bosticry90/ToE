# FT STEP-6 (v4)
# Nonlinear and Multiscale Calibration of LCRD v1
# Fully synchronized with CG-T5, CG-T6, CG-T7

This document contains only empirical calibration.
No equations are created or modified.

--------------------------------------------------------------------
# 1. Purpose
--------------------------------------------------------------------

Step-6 extends LCRD-to-CRFT calibration beyond the IR limit:

• CG-T5 — nonlinear dispersion vs amplitude  
• CG-T6 — mode coupling / spectral transfer  
• CG-T7 — long-time drift of coarse invariants

CRFT remains unchanged; Step-6 tests only characterize LCRD v1.

--------------------------------------------------------------------
# 2. Locked Inputs
--------------------------------------------------------------------

CRFT (comparison target):
rho0 = 1  
lam = 0  
beta = 0  
g_eff_IR = 0.1666456 (from Step-5)

LCRD v1 micro-parameters:
A1 = A2 = A3 = 0  
G = 12.5  
C_coh = −12.5

Simulation:
N = 512  
ε = 1  
L = 512  
dt = 0.001  
block_size = 4  
backend = cpu

--------------------------------------------------------------------
# 3. CG-T5 — Nonlinear Dispersion vs Amplitude
--------------------------------------------------------------------

mode_index = 1  
k = 1.227185e−02  
A ∈ {1e−3, 3e−3, 1e−2, 2e−2, 5e−2, 1e−1}

All exact values:

A = 1.000e−03  
    ω_abs = 5.010210e−03  
    rel_err_IR = 1.311195e−07  
    g_eff(A) = 1.666456e−01  
    rel_dev = 2.622982e−07

A = 3.000e−03  
    g_eff(A) = 1.666456e−01  
    rel_dev = 2.465213e−07

A = 1.000e−02  
    g_eff(A) = 1.666456e−01  
    rel_dev = 6.975372e−09

A = 2.000e−02  
    g_eff(A) = 1.666455e−01  
    rel_dev = 7.825320e−07

A = 5.000e−02  
    g_eff(A) = 1.666445e−01  
    rel_dev = 6.302838e−06

A = 1.000e−01  
    g_eff(A) = 1.666413e−01  
    rel_dev = 2.597502e−05

Interpretation:
g_eff(A) remains extremely close to g_eff_IR
(≤ 2.6e−5 relative deviation).

--------------------------------------------------------------------
# 4. CG-T6 — Mode Coupling and Spectral Transfer
--------------------------------------------------------------------

k1_index = 1  
k2_index = 2  
A_θ = 0.01

Spectral results:
P0(k) and PT(k) matched exactly as recorded in Step-6 v3.

Total spectral power drift:
    ~ 9.6e−9

Interpretation:
Nonlinear redistribution occurs,
but the system remains conservative at coarse level.

--------------------------------------------------------------------
# 5. CG-T7 — Long-Time Drift of Mass and Energy
--------------------------------------------------------------------

mode_index = 1  
A = 0.01  
t_final = 20

Mass:
    rel_drift ≈ 5.1e−11

Energy:
    rel_drift ≈ 1.0e−10

Interpretation:
Invariant behavior remains stable on doubled time window.

--------------------------------------------------------------------
# 6. Completion Status
--------------------------------------------------------------------

Step-6 is complete.

LCRD v1 satisfies:
• amplitude-dependent dispersion consistency  
• nonlinear mode-coupling conservation  
• long-time mass/energy conservation  

CRFT equations remain unchanged.

--------------------------------------------------------------------
# END
