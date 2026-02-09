# State of the Theory (CRFT Program)
Updated: 2025-11-27  
Status: Fully Aligned With Equation Inventory and IR-Only Calibration

---

# 1. Purpose and Scope

This document presents the canonical mathematical description of the Coherence-Regularized Field Theory (CRFT). All statements refer strictly to:

- validated equations,
- verified implementations,
- and dispersion relations from the equation inventory.

This version incorporates the **final locked IR calibration** obtained from the LCRD CG-T1 test suite.

---

# 2. Canonical Governing Equations

## 2.1 CP-NLSE Equation

\[
i\phi_t
+ \tfrac12 \phi_{xx}
- g|\phi|^2\phi
+ \lambda\phi_{xxxx}
+ \beta\phi_{xxxxxx}
=0.
\]

## 2.2 CE-NWE Equation

\[
\phi_{tt}
+\tfrac14\phi_{xxxx}
-g\rho_0\phi_{xx}
=0.
\]

Both models include an optional coherence penalty term derived from:

\[
C=(|\phi|^2-\rho_0)^2.
\]

---

# 3. Linear CRFT Dispersion (Inventory-Verified)

Linearization around the constant background produces:

\[
\omega^2(k)
=
\left(\frac{k^2}{2}\right)^2
+
g\rho_0 k^2
+
\lambda k^4
+
\beta k^6.
\]

This is the dispersion against which coarse-grained microscopic candidates are evaluated.

---

# 4. IR-Locked CRFT Calibration (From LCRD CG-T1)

A full CG-T1 sweep of LCRD v1 reveals that:

- **mode_index = 1** is the only mode in the hydrodynamic regime  
- modes 2–4 lie in a UV regime and cannot be matched by CRFT’s even-in-k polynomial  
- therefore calibration must be based solely on **mode 1**

## 4.1 Effective nonlinearity determined from mode 1

From CG-T1:

\[
g_{\mathrm{eff}}=0.1666456\approx 0.17.
\]

This value replaces \(g\) in the CRFT IR expansion when CRFT is used as the coarse-grained effective theory of LCRD v1.

## 4.2 Updated IR dispersion

With \(\rho_0 = 1\):

\[
\omega(k)
=
\sqrt{0.17\,k^2 + \tfrac14 k^4}.
\]

This is the **IR-valid dispersion** that informs hydrodynamic, acoustic, and long-wavelength solitonic behavior.

## 4.3 Reclassification of higher modes

Modes 2–4 are:

- outside the small-k window  
- inconsistent with CE-NWE/CP-NLSE structure  
- heavily influenced by stiff micro coefficients  

Thus:

> These modes are not used in CRFT mapping and are instead categorized as UV microstructure.

---

# 5. Hydrodynamic Representation

(unchanged; fully consistent with the updated calibration)

The Madelung mapping still yields continuity, phase evolution, and quantum pressure relationships exactly consistent with the inventory.

---

# 6. Soliton and Turbulence Structures

(unchanged)

All soliton expressions and turbulence metrics remain valid, with the note that:

- low-k soliton width and sound speed now reflect \(g_\mathrm{eff}=0.17\)

---

# 7. Numerical Stability, Scaling, and Interpretation

The IR calibration does not modify any stability conditions. The relationship between physical scales is updated only by replacing:

\[
c_s^2 = g\rho_0 \quad\longrightarrow\quad c_s^2 = g_\mathrm{eff}\rho_0 = 0.17.
\]

All other content remains unchanged.

---

# 8. Summary

The CRFT model as implemented is:

- mathematically self-consistent  
- fully tied to an inventory of validated equations  
- now **IR-calibrated** to the microscopic LCRD v1 model  
- free from speculation or unverified structures

The replacement of the original nominal \(g=1\) with the empirically-determined \(g_\mathrm{eff}=0.17\) is the only substantive modification introduced by CG-T1.

This calibration is now locked and propagates forward through all FT-Step-4 and FT-Step-5 work.

