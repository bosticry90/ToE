# Part IV — Numerical Implementation (Full Expanded Replacement)

The numerical implementation of the Classical Coherence Field Theory (CCFT) depends on a consistent, reproducible, high-accuracy framework for simulating nonlinear dispersive PDE systems. This section provides a complete and explicit description of spatial discretization, time integration, subsystem-specific update rules, stability requirements, parameter extraction from LSDA microphysics, diagnostics, verification tests, and multi-field extensions. The goal is to allow any researcher to exactly reproduce all CCFT simulations.

---

## 4.1 Numerical Design Requirements

The numerical scheme is designed to satisfy the following requirements:

1. **Dispersion fidelity**

   The scheme must reproduce the analytic CRFT/CCFT dispersion relation
   \[
   \omega(k)^2 = g_{\mathrm{eff}} \rho_0 k^2 + \frac{1}{4}k^4
   \]
   and must do so across the tested range of wavenumbers and resolutions.

2. **Invariant preservation**

   Core invariants must be preserved to numerical precision in tests where they should be conserved:
   - φ-norm (mass) and quadratic energy in the CP–NLSE/CE–NWE sector,
   - rotor boundedness for \(R\) and \(K\),
   - χ-sector energy stability under weak coupling.

3. **Multi-scale capability**

   The numerical method must support multi-scale gradients and curvature in the fields
   \(\phi\), \(\rho\), \(u\), \(R\), \(K\), and \(\chi\), without artificial suppression of physically relevant small-scale structure.

4. **Periodic domain and spectral methods**

   Periodic boundaries are used for all fields, enabling Fourier spectral methods for all spatial derivatives.

5. **Explicit and deterministic time integration**

   Time integration must be explicit, deterministic, and capable of stable operation over long-time evolutions (e.g. RK4), so that diagnostic drift is attributable to known discretization errors rather than algorithmic ambiguity.

6. **Consistency with LSDA microphysics**

   All discretizations must preserve the LSDA-derived microstructural constraints that define:
   - the effective nonlinear coupling \(g_{\mathrm{eff}}\),
   - rotor energy coefficients \(c_1, c_2\),
   - χ-sector parameters such as \(c_\chi\), \(\gamma\), and \(\alpha\).

---

## 4.2 CRFT Numerical Rules (Operators, Viscosity Mapping, Stability)

This section defines the standard numerical rules inherited from the CRFT simulation suite and reused by CCFT.

### 4.2.1 Fourier-Spectral Derivative Operators

Consider a periodic grid of length \(L\) with \(N\) points.

- **Spatial samples**
  \[
  x_j = \frac{L j}{N}, \quad j = 0, 1, \dots, N-1.
  \]

- **Wavenumbers**
  \[
  k = \frac{2\pi}{L}\,\mathrm{fftfreq}(N),
  \]
  where \(\mathrm{fftfreq}(N)\) is the standard discrete frequency array.

Given a field \(f(x)\) with Fourier transform \(\hat{f}(k)\), spectral derivatives are defined as:

- **First derivative**
  \[
  D_1 f = \mathcal{F}^{-1} \big[ (i k)\,\hat{f} \big].
  \]

- **Second derivative**
  \[
  D_2 f = \mathcal{F}^{-1} \big[ -k^2\,\hat{f} \big].
  \]

- **Fourth derivative**
  \[
  D_4 f = \mathcal{F}^{-1} \big[ k^4\,\hat{f} \big].
  \]

- **Sixth derivative**
  \[
  D_6 f = \mathcal{F}^{-1} \big[ -k^6\,\hat{f} \big].
  \]

These operators are used for \(\phi\), \(\chi\), \(R\), \(K\), and hydrodynamic reductions (e.g. derivatives of \(\rho\) and \(u\)).

### 4.2.2 Numerical Viscosity Mapping

CRFT supports an optional spectral numerical viscosity to stabilize high-\(k\) modes while preserving the physical dispersion of low-\(k\) modes. The viscosity function is:

\[
\nu(k) = \nu_0 \left( \frac{|k|}{k_{\max}} \right)^p,
\]

where:
- \(\nu_0\) is a base viscosity amplitude,
- \(k_{\max}\) is the maximum resolved wavenumber,
- \(p\) is typically \(4\) or \(6\), depending on the simulation.

This viscosity is applied additively to the evolution equation. For the φ field:

\[
\phi_t \;\rightarrow\; \phi_t - \nu(k)\,\phi,
\]

applied in Fourier space. The same mapping can be used for rotor fields \(R\) and \(K\) when needed, ensuring numerical stability while preserving low-\(k\) physics.

### 4.2.3 Time-Stepping Stability

A standard fourth-order Runge–Kutta (RK4) scheme is used for time integration. For CP–NLSE and CE–NWE branches, the timestep must satisfy:

\[
dt < \frac{C}{k_{\max}^2 + g_{\mathrm{eff}}\rho_0},
\]

with \(C \in [0.1, 0.5]\) depending on the chosen resolution and the desired stability margin.

For χ-sector simulations with strong second-order dynamics, the more restrictive condition:

\[
dt < \frac{C}{c_\chi k_{\max}}
\]

may apply. These constraints ensure that the fastest linear waves and the stiffest nonlinear contributions are stably resolved.

---

## 4.3 LSDA → CRFT Parameter Extraction

The LSDA layer defines the microphysical response coefficients that CCFT must reproduce at the coarse-grained level. This subsection describes how \(g_{\mathrm{eff}}\), rotor coefficients \(c_1, c_2\), and χ-sector parameters are extracted.

### 4.3.1 Extracting \(g_{\mathrm{eff}}\)

LSDA simulations provide an empirical dispersion relation for the primary coherence channel:

\[
\omega_{\mathrm{LSDA}}^2(k) = A k^2 + B k^4.
\]

The CRFT/CCFT analytic dispersion relation is:

\[
\omega(k)^2 = g_{\mathrm{eff}} \rho_0 k^2 + \frac{1}{4} k^4.
\]

Matching LSDA to CCFT yields:

\[
g_{\mathrm{eff}} = \frac{A}{\rho_0}, \qquad B \approx \frac{1}{4}.
\]

Thus LSDA determines \(A\), and CCFT adopts:

- \(g_{\mathrm{eff}} = A/\rho_0\),
- the quartic coefficient fixed at \(1/4\) to preserve the canonical form of the CRFT dispersive term.

This procedure determines the nonlinear coupling in all φ-equations within CCFT.

### 4.3.2 Rotor Coefficients \(c_1, c_2\)

The LCRD rotor subsystem depends on two coefficients \(c_1\) and \(c_2\) that govern the energetic cost of rotor excitations:

\[
E_{\mathrm{rotor}} = \frac{c_1}{2} R^2 + \frac{c_2}{2} K^2.
\]

These are obtained as follows:

- \(R\) is fitted to LSDA-measured shear alignment decay rates, ensuring that rotor relaxation in the reduced model matches microphysical relaxation.
- \(K\) is fitted to LSDA curvature-response dynamics, such as how quickly microstructure relaxes in regions of high curvature.

The fitted values of \(c_1\) and \(c_2\) are then used throughout CCFT to maintain compatibility with LSDA microphysics.

### 4.3.3 χ-Sector Parameters

The auxiliary χ field is calibrated so that:

- the linear term \(\gamma\) reproduces LSDA-measured curvature-relaxation times,
- the wave speed \(c_\chi\) matches the propagation speed of curvature-related microstructural disturbances,
- the coupling \(\alpha\) is chosen so that χ back-reaction modulates φ dynamics without destroying coherence.

This calibration ensures that the χ field acts as a physically interpretable curvature-responsive channel, rather than an arbitrary auxiliary field.

---

## 4.4 Full PDE Systems and Numerical Updates

This subsection lists the full PDE systems used in CCFT and the associated numerical update rules.

### 4.4.1 2D CP–NLSE Implementation (Full Block)

The baseline CCFT subsystem in two spatial dimensions is the CP–NLSE:

\[
i \phi_t = -\frac{1}{2} \nabla^2 \phi + g_{\mathrm{eff}} (|\phi|^2 - \rho_0)\,\phi.
\]

On a periodic 2D grid:

1. **Laplacian via spectral operator**

   Let \(k_x, k_y\) be the 2D wavenumber components. Then
   \[
   \nabla^2 \phi = \mathcal{F}^{-1} \big[ - (k_x^2 + k_y^2)\,\hat{\phi} \big].
   \]

2. **Nonlinear term**

   Compute
   \[
   N(\phi) = g_{\mathrm{eff}} (|\phi|^2 - \rho_0)\,\phi.
   \]

3. **Right-hand side for RK4**

   Rewrite the PDE as
   \[
   \phi_t = F(\phi) = -\,i \left( -\frac{1}{2} \nabla^2 \phi + N(\phi) \right).
   \]

4. **RK4 update**

   Advance \(\phi\) using standard RK4 steps with \(F(\phi)\).

5. **Diagnostics**

   At each diagnostic step, compute:
   \[
   N(t) = \int |\phi|^2 \, dx\,dy,
   \]
   \[
   E(t) = \int \left( \frac{1}{2} |\nabla \phi|^2 + \frac{g_{\mathrm{eff}}}{2} (|\phi|^2 - \rho_0)^2 \right) dx\,dy.
   \]

These diagnostics validate numerical conservation of norm and energy where appropriate.

---

### 4.4.2 LCRD v3 Rotor Subsystem

The LCRD rotor subsystem models curvature-induced coherence dynamics. It introduces two rotor fields:

- \(R\): alignment rotor,
- \(K\): curvature rotor.

A representative form of the rotor evolution equations is:

\[
R_t = a_1 D_1(\rho u) + a_2 D_2 \rho + S_R(\phi),
\]
\[
K_t = b_1 D_2 u + b_2 D_3 \rho + S_K(\phi),
\]

where:

- \(D_1, D_2, D_3\) are spectral derivative operators,
- \(S_R(\phi)\), \(S_K(\phi)\) are φ-dependent source terms calibrated against LSDA,
- \(\rho\) and \(u\) are the hydrodynamic density and velocity derived from φ.

The rotor energy density is:

\[
E_{\mathrm{rotor}} = \frac{c_1}{2} R^2 + \frac{c_2}{2} K^2.
\]

The associated rotor pressure correction entering the momentum equation is:

\[
Q_{\mathrm{rotor}} = c_1 \partial_x R + c_2 \partial_{xx} K.
\]

This term modifies the momentum equation but does not alter the continuity equation. This design ensures that mass conservation is preserved while momentum flux receives curvature-induced corrections.

**Rotor stability diagnostics** include:

- boundedness of \(R\) and \(K\) over long times,
- decay of high-\(k\) rotor spectral components when physical conditions demand relaxation,
- consistency between rotor-induced corrections and LSDA curvature-response behavior.

The rotor subsystem is advanced using RK4 and the same spectral operators as the φ field.

---

### 4.4.3 φ–χ Extended CRFT PDE System

The φ–χ extension introduces a weakly coupled second field χ that responds to curvature and modulates φ.

The coupled system is:

- **φ-equation**:
  \[
  i \phi_t
  = -\frac{1}{2} \nabla^2 \phi
    + g_{\mathrm{eff}} (|\phi|^2 - \rho_0)\,\phi
    + \alpha \chi \phi.
  \]

- **χ-equation (second-order)**:
  \[
  \chi_{tt} - c_\chi^2 \nabla^2 \chi + \gamma \chi = \alpha |\phi|^2.
  \]

For numerical implementation, the χ equation is written as a first-order system:

- Define \(v = \chi_t\).
- Then
  \[
  \chi_t = v,
  \]
  \[
  v_t = c_\chi^2 \nabla^2 \chi - \gamma \chi + \alpha |\phi|^2.
  \]

The numerical updates proceed as follows:

1. Compute \(\nabla^2 \chi\) spectrally.
2. Form right-hand sides for \(\phi_t\), \(\chi_t\), and \(v_t\).
3. Advance the coupled system \((\phi, \chi, v)\) using RK4.

**Diagnostics**:

- χ-sector energy:
  \[
  E_\chi = \int \left[
    \frac{1}{2} v^2
    + \frac{c_\chi^2}{2} |\nabla \chi|^2
    + \frac{\gamma}{2} \chi^2
  \right] dx.
  \]

- φ–χ interaction energy:
  \[
  E_{\mathrm{int}} = \int \alpha \chi |\phi|^2 \, dx.
  \]

Weak coupling (\(\alpha\) small) ensures that the extension perturbs but does not destroy the core CRFT/CCFT structure and limits.

---

## 4.5 Acoustic-Metric Diagnostics and Curvature Scalars

CCFT admits a hydrodynamic reduction of φ. Write:

\[
\phi = \sqrt{\rho}\,e^{i\theta},
\]
\[
u = \nabla \theta.
\]

Here, \(\rho\) is the effective density and \(u\) is the phase-derived velocity. From these fields, one can construct an acoustic metric that organizes emergent geometry. A representative acoustic metric tensor is:

\[
g_{\mu\nu} =
\begin{pmatrix}
-(c^2 - u^2) & -u_j \\
-u_i & \delta_{ij}
\end{pmatrix},
\]

where \(c\) is an effective sound speed and \(\delta_{ij}\) is the Kronecker delta.

Using spectral derivative operators, one can compute:

- a Ricci-like scalar curvature \(R\) derived from the acoustic metric,
- an extrinsic curvature scalar
  \[
  K = \nabla \cdot u.
  \]

These curvature diagnostics help classify coherent structures (e.g., solitons, vortices, and curvature-localized regions) in geometric terms and test consistency between CRFT/CCFT and emergent hydrodynamic behavior.

---

## 4.6 Spectral and Coherent-Structure Turbulence Diagnostics

For φ turbulence, the following diagnostics are used.

1. **Spectral energy density**

   For a 1D or isotropically binned spectrum, define:
   \[
   E(k) = \sum_{|k'| \in \text{bin}(k)} |\hat{\phi}(k')|^2.
   \]

   This measures how energy is distributed over wavenumbers.

2. **Phase-alignment measure**

   For a spatial shift \(\Delta\), define:
   \[
   A(t) =
   \frac{\int \phi(x)\,\phi^\*(x+\Delta)\,dx}{\int |\phi(x)|^2 dx}.
   \]

   This measures average phase coherence at separation \(\Delta\).

3. **Coherence lifetime**

   The coherence lifetime is extracted by tracking the decay of \(A(t)\) over time. The decay timescale provides a quantitative measure of how long coherent structures persist in turbulent regimes.

For rotor turbulence, define rotor spectra:

\[
E_R(k) = |\hat{R}(k)|^2, \qquad
E_K(k) = |\hat{K}(k)|^2.
\]

These reveal how rotor energy is distributed across scales and how it evolves in time, providing insight into multiscale curvature dynamics.

---

## 4.7 Numerical Test Family (Explicit Definitions)

The numerical test family is organized into three groups:

- T1–T10: numerical stability and operator verification,
- C1–C13: CRFT / CCFT core verification,
- L1–L10: LCRD rotor subsystem tests.

### 4.7.1 T1–T10: Numerical Stability and Operator Verification

1. **T1: Spectral derivative exactness**

   Verify that \(D_1\), \(D_2\), \(D_4\), and \(D_6\) reproduce the derivatives of sinusoidal test functions to high precision.

2. **T2: RK4 temporal order**

   Evolve a known ODE with RK4 and confirm that the global error scales as \(O(dt^4)\).

3. **T3: Operator composition accuracy**

   Confirm that \(D_1(D_1 f) \approx D_2 f\) and similarly for higher-order compositions.

4. **T4: 2D Laplacian accuracy**

   Validate that the 2D spectral Laplacian reproduces analytic second derivatives of test functions on a periodic domain.

5. **T5: Numerical viscosity mapping**

   Apply the viscosity function \(\nu(k)\) to a narrow-band initial condition and confirm that high-\(k\) components decay at the predicted rates.

6. **T6: Grid refinement convergence**

   Repeat a simulation at multiple resolutions and verify that key diagnostics converge at the expected rate as \(N\) increases.

7. **T7: Long-time mass drift**

   Evolve a norm-conserving φ configuration and evaluate the drift in \(N(t)\) over long times, confirming it remains within prescribed tolerances.

8. **T8: High-\(k\) stability stress test**

   Initialize a spectrum peaked at high wavenumbers and verify that the scheme remains stable and behaves as expected under the chosen viscosity and timestep.

9. **T9: Nonlinear stepper stability**

   Run a strongly nonlinear test case (e.g. high-amplitude φ) and confirm that the RK4 scheme remains stable and reproduces benchmark diagnostics.

10. **T10: Full multi-field stepper**

    Simultaneously evolve \(\phi\), \(\chi\), \(R\), and \(K\) to validate that the coupled system remains stable and preserves the intended qualitative behavior.

---

### 4.7.2 C1–C13: CRFT / CCFT Core Verification Tests

1. **C1: Linear dispersion agreement**

   Confirm that the simulated dispersion relation for small-amplitude φ waves matches \(\omega(k)^2 = g_{\mathrm{eff}} \rho_0 k^2 + \tfrac{1}{4}k^4\).

2. **C2: Norm conservation**

   Show that φ norm \(N(t)\) remains nearly constant in norm-preserving regimes.

3. **C3: Energy conservation**

   Demonstrate that the energy functional \(E(t)\) exhibits minimal relative drift where energy should be conserved.

4. **C4: Quantum-pressure correctness**

   Validate that the hydrodynamic reduction of φ reproduces the correct quantum-pressure term in the effective momentum equation.

5. **C5: Multi-field consistency**

   Compare φ-only simulations against φ+χ simulations in the weak-coupling limit and show that φ dynamics remain consistent.

6. **C6: 2D dispersion convergence**

   Extend C1 to 2D simulations and confirm that dispersion is correctly reproduced.

7. **C7: Soliton stability**

   Initialize known soliton configurations and confirm that they persist and propagate stably.

8. **C8: Soliton collision symmetry**

   Simulate soliton collisions and verify that outgoing structures match incoming ones in shape and speed to within numerical tolerances.

9. **C9: Hydrodynamic reduction consistency**

   Compare hydrodynamic variables derived from φ with direct hydrodynamic simulations and confirm consistency.

10. **C10: Phase-gradient structure**

    Confirm that gradients of the phase field θ match expected patterns and are numerically well-resolved.

11. **C11: Acoustic-metric correctness**

    Construct the acoustic metric from \(\rho\) and \(u\), and validate that the geometric diagnostics are consistent with known CCFT configurations.

12. **C12: Curvature scalar test**

    Compute curvature scalars such as \(K = \nabla\cdot u\) and compare against analytic or benchmark values where available.

13. **C13: Turbulence spectrum test**

    Evolve a turbulent φ field and confirm that \(E(k)\) exhibits the expected qualitative spectral shape and scaling.

---

### 4.7.3 L1–L10: LCRD Rotor Subsystem Tests

1. **L1: Rotor decay-rate validation**

   Validate that rotor fields \(R\) and \(K\) decay at rates consistent with LSDA-calibrated relaxation.

2. **L2: Rotor boundedness**

   Demonstrate that \(R\) and \(K\) remain bounded over long-time simulations in physically relevant regimes.

3. **L3: R–φ coupling symmetry**

   Confirm that the coupling between \(R\) and φ respects the symmetry and conservation properties encoded in the CCFT equations.

4. **L4: K curvature response**

   Test how \(K\) responds to imposed curvature patterns and verify that the response matches LSDA microstructure behavior.

5. **L5: Rotor energy positivity**

   Show that \(E_{\mathrm{rotor}} = \tfrac{c_1}{2}R^2 + \tfrac{c_2}{2}K^2\) remains non-negative at all times.

6. **L6: Rotor-pressure momentum correction**

   Confirm that the rotor pressure term \(Q_{\mathrm{rotor}}\) modifies the momentum equation as intended without violating mass conservation.

7. **L7: Spectral rotor diffusion**

   Investigate how rotor energy moves across scales and verify that spectral diffusion matches expectations.

8. **L8: Rotor turbulence decay scaling**

   Simulate rotor turbulence and measure decay rates and scaling, comparing them against theoretical or empirical expectations.

9. **L9: Rotor–CRFT hydrodynamic consistency**

   Confirm that the presence of rotor fields does not contradict the hydrodynamic limit derived from φ.

10. **L10: Full rotor subsystem stability**

    Run combined φ–R–K simulations and confirm that the full rotor subsystem remains stable and behaves consistently across test scenarios.

---

## 4.8 Summary

This section provides a complete numerical specification of CCFT, including discretization rules, time-stepping schemes, subsystem PDEs, LSDA-derived parameters, diagnostics, and formal numerical test definitions. Together, these elements define a reproducible numerical framework for CCFT simulations and ensure that the theory can be systematically validated and extended.
