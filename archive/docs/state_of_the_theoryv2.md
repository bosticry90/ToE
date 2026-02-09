# STATE OF THE THEORY (CRFT Program)
# Fully Synchronized With Equation Inventory and LCRD Step-5

Updated: 2025-11-27

--------------------------------------------------------------------
# 1. Scope
--------------------------------------------------------------------

This document defines the *current scientific status* of the CRFT program.

It contains:
- the canonical CRFT continuum theory,
- the IR calibration extracted from LCRD v1 (Step-5),
- and the validated mapping between the micro and macro layers.

No unvalidated claims are included.

--------------------------------------------------------------------
# 2. Canonical CRFT Equations (Authoritative Layer)
--------------------------------------------------------------------

The governing equations are:

CP-NLSE:
    i φ_t
    + 1/2 φ_xx
    − g |φ|² φ
    + lam φ_xxxx
    + beta φ_xxxxxx
    = 0

CE-NWE:
    φ_tt + (1/4)φ_xxxx − g rho0 φ_xx = 0

CRFT dispersion:
    ω²(k) = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶

These define all long-wavelength physics of the CRFT layer.

--------------------------------------------------------------------
# 3. IR Calibration From LCRD v1 (Step-5)
--------------------------------------------------------------------

Step-5 quantifies how microscopic LCRD dynamics produce CRFT-like
dispersion and conservation after coarse-graining.

Only the **lowest nonzero mode** (mode 1) belongs to the hydrodynamic limit.

From CG-T1:
    g_eff = 0.1666456   (for rho0 = 1)

Therefore the *IR CRFT dispersion* for interpreting LCRD is:

    ω(k) = sqrt( 0.17 k² + (k⁴/4) )

Modes 2–4 lie in a UV regime and are not mapped to CRFT.

--------------------------------------------------------------------
# 4. Conservation and Structural Results
--------------------------------------------------------------------

All Step-5 tests passed:

CG-T2 (amplitude robustness):
    Accurate IR linear dispersion for amplitudes A ≤ 0.02.

CG-T3 (mass conservation):
    drift ~ 10⁻⁹

CG-T4 (energy conservation):
    drift ~ 10⁻⁸

These show that LCRD v1 → CRFT mapping respects the conserved quantities
in the hydrodynamic regime.

--------------------------------------------------------------------
# 5. Hydrodynamics, Soliton, and Turbulence Layers
--------------------------------------------------------------------

No changes to the hydrodynamic lift, soliton formulas, or turbulence
diagnostics were required.

Only the effective sound speed is updated when interpreting LCRD:

    c_s² = g_eff rho0 = 0.17

All other CRFT structures remain exactly as originally validated.

--------------------------------------------------------------------
# 6. Relationship Between CRFT and LCRD (Step-3 → Step-5)
--------------------------------------------------------------------

1. CRFT is the continuum theory. Its equations are unchanged.  
2. LCRD v1 is a microscopic candidate that:
   - defines a rotor-density algebra,
   - evolves via local rules implemented in stepper.py,
   - maps to CRFT via coarse-graining,
   - reproduces CRFT linear dispersion at small k,
   - preserves coarse mass and energy.

3. Step-5 simulation verifies:
   - dispersion matching (via g_eff),
   - robustness over amplitudes,
   - conservation properties.

Thus CRFT remains the correct long-wavelength theory and LCRD v1 is a proven micro-realizer *up to the IR regime*.

--------------------------------------------------------------------
# 7. Current Status
--------------------------------------------------------------------

- CRFT layer: **complete and validated**
- FT (LCRD v1): **IR calibrated, structurally validated**
- No mismatches between continuum inventory and simulation results
- All documents (inventory, FT files, Step-5 docs) are synchronized
- Safe to proceed to FT-Step-6

--------------------------------------------------------------------
# END OF DOCUMENT
