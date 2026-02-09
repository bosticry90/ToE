# FT Candidate Algebra 02 — Local Spinor–Density Algebra (LSDA)

_Last updated: 2025-11-26_  
_Aligned with: `ft_step3_composition_algebra.md`, CRFT equation inventory, state_of_the_theory.md, and Candidate Algebra 01 (LCRD)_ 

---

## 1. Purpose and Status of Candidate 02

This document specifies **Candidate Algebra 02** for the Fundamental Theory (FT) program:

> **LSDA: Local Spinor–Density Algebra**

The goal is to define a **richer microscopic algebra** than LCRD by introducing **two-component complex spinor-like objects** at each site. The intent is:

- to retain a clear **density + phase** interpretation compatible with CRFT’s scalar field \(\phi(x,t)\),  
- to allow **internal structure** that may better realize higher-order dispersion (\(k^4, k^6\)) and more complex nonlinear behavior in a natural way,  
- to remain strictly classical and algebraic (no quantum postulates), while structurally analogous to spinor/two-level systems used in many-body and field theories.   

As with LCRD, this is **not** claimed to be “the” fundamental theory. It is a **candidate microscopic algebra** to be evaluated against the FT Step-3 requirements and CRFT constraints:

- single emergent complex scalar field \(\phi\) with \(\rho = |\phi|^2\), \(\theta = \arg\phi\),  
- CP-NLSE / CE-NWE dynamics and hydrodynamic form,  
- validated dispersion \(\omega^2 = (k^2/2)^2 + g\rho_0 k^2 + \lambda k^4 + \beta k^6\),  
- coherence functional \(C=(|\phi|^2-\rho_0)^2\), solitons, and turbulence.   

---

## 2. Micro Degrees of Freedom (DOFs)

We again consider a **1D lattice** (spacing \(\epsilon\)), with sites \(j \in \mathbb{Z}\). Higher-dimensional generalization is reserved for later.

### 2.1 Site Variables

At each site \(j\), LSDA assigns a **two-component complex vector** (“spinor-like” object):

\[
\psi_j =
\begin{pmatrix}
a_j \\
b_j
\end{pmatrix}
\in \mathbb{C}^2.
\]

From \(\psi_j\), we define:

1. **Site density (scalar):**
   \[
   n_j = \|\psi_j\|^2 
       = |a_j|^2 + |b_j|^2
       \in [0,\infty).
   \]

2. **Normalized internal state (unit spinor):**
   \[
   s_j =
   \begin{cases}
     \psi_j / \sqrt{n_j}, & n_j > 0, \\
     s_0, & n_j = 0,
   \end{cases}
   \quad \text{with } \|s_j\|^2 = 1.
   \]

Here \(s_0\) is an arbitrary reference unit spinor for empty sites. Thus each site carries:

\[
a^{\text{(LSDA)}}_j = (n_j, s_j), \qquad n_j \ge 0,\ s_j \in S^3 \subset \mathbb{C}^2.
\]

This introduces **one scalar degree** (density) and **three internal degrees** (orientation on the unit 3-sphere), giving more structure than LCRD’s single rotor.   

### 2.2 Local “Projected” Complex Amplitude

We need LSDA to produce a **single emergent complex scalar** compatible with CRFT’s \(\phi\). To do this, we introduce a fixed complex unit vector \(w\in\mathbb{C}^2\) with \(\|w\|=1\) (a “readout axis”):

\[
\zeta_j = \langle w, \psi_j \rangle
        = \overline{w}_1 a_j + \overline{w}_2 b_j \in \mathbb{C}.
\]

\(\zeta_j\) is the **projected complex amplitude** at site \(j\). It will play the role analogous to the micro-amplitude \(z_j\) in LCRD.   

---

## 3. Algebraic Composition Law

We now define how LSDA combines local DOFs when regions are merged. The composition must satisfy: locality, density additivity, and a well-defined emergent complex amplitude, while keeping the internal spinor structure.

### 3.1 Single-Site Composition

Given two micro-states at the same site \(j\):

\[
a_j^{(1)} = (n_j^{(1)}, s_j^{(1)}),
\quad
a_j^{(2)} = (n_j^{(2)}, s_j^{(2)}),
\]

or equivalently \(\psi_j^{(1)}, \psi_j^{(2)} \in \mathbb{C}^2\), we define their **composed** LSDA state:

\[
a_j^{(1)} \star_{\text{LSDA}} a_j^{(2)}
= (n_j^{\text{tot}}, s_j^{\text{eff}}),
\]

via the following steps.

1. **Density additivity (extensive scalar):**
   \[
   n_j^{\text{tot}} = n_j^{(1)} + n_j^{(2)}.
   \]

2. **Spinor superposition (internal state composition):**
   - Form a weighted sum:
     \[
     \Psi_j^{\text{sum}} 
       = \sqrt{n_j^{(1)}}\,s_j^{(1)}
       + \sqrt{n_j^{(2)}}\,s_j^{(2)}.
     \]
   - If \(\Psi_j^{\text{sum}}\neq 0\), define:
     \[
     s_j^{\text{eff}} 
       = \frac{\Psi_j^{\text{sum}}}{\|\Psi_j^{\text{sum}}\|}.
     \]
   - If \(\Psi_j^{\text{sum}} = 0\) (exact cancellation), pick any unit spinor as a convention (e.g., \(s_0\)); only density matters in that degenerate case.

Equivalently, we can work directly in terms of spinors \(\psi_j^{(1)}, \psi_j^{(2)}\):

\[
\psi_j^{\text{tot}} 
  = \psi_j^{(1)} + \psi_j^{(2)},
\quad
n_j^{\text{tot}} = \|\psi_j^{\text{tot}}\|^2,
\quad
s_j^{\text{eff}} = 
\begin{cases}
  \psi_j^{\text{tot}} / \sqrt{n_j^{\text{tot}}}, & n_j^{\text{tot}} > 0,\\
  s_0, & n_j^{\text{tot}} = 0.
\end{cases}
\]

This structure is:

- **extensive in density**: \(n_j^{\text{tot}}\) grows with superposition,  
- **phase- and orientation-sensitive**: internal directions (phases and relative spinor orientations) affect \(s_j^{\text{eff}}\),  
- **capable of encoding more complex internal coherence** than a single U(1) rotor.

### 3.2 Algebraic Properties

At a single site, the LSDA composition \(\star_{\text{LSDA}}\) has:

- **Commutativity:**  
  \[
  a_j^{(1)} \star_{\text{LSDA}} a_j^{(2)}
  = a_j^{(2)} \star_{\text{LSDA}} a_j^{(1)}.
  \]

- **Associativity (almost everywhere):**  
  Vector addition in \(\mathbb{C}^2\) is associative, and normalization only fails to be strictly associative in measure-zero degenerate cases where the sum vanishes and we invoke a convention. Thus, the algebra is **effectively associative**.

- **Identity element:**  
  Any state with zero density, \((0,s_0)\), is an identity:
  \[
  (n_j,s_j)\star_{\text{LSDA}} (0,s_0) = (n_j,s_j).
  \]

Thus, LSDA is a **commutative, essentially associative, unital algebra** over site DOFs, analogous in spirit to LCRD but enriched by spinor structure.   

### 3.3 Composition Over Regions

Given two configurations \(A,B\) over the lattice:

\[
A = \{a_j^{(A)}\}, \quad
B = \{a_j^{(B)}\},
\]

we define **regional composition**:

\[
(A \circledast_{\text{LSDA}} B)_j
= a_j^{(A)} \star_{\text{LSDA}} a_j^{(B)}.
\]

Composition is **local and factorizable per site**, satisfying the FT requirement of locality and composability. :contentReference[oaicite:6]{index=6}  

---

## 4. Coarse-Graining Map to CRFT Field \(\phi(x,t)\)

We now define how LSDA configurations yield an emergent CRFT scalar field \(\phi(x,t)\), consistent with the equation inventory and state-of-the-theory descriptions.   

### 4.1 Block Coarse-Graining

Let \(B\) be a small lattice block around position \(x\). For LSDA we define:

1. **Block density:**
   \[
   \rho_B = \frac{1}{|B|}\sum_{j\in B} n_j
          = \frac{1}{|B|}\sum_{j\in B} \|\psi_j\|^2.
   \]

2. **Block projected complex amplitude:**

   Recall the projection \(\zeta_j = \langle w,\psi_j\rangle\in\mathbb{C}\). Define:
   \[
   \Phi_B = \frac{1}{|B|}\sum_{j\in B} \zeta_j
          = \frac{1}{|B|}\sum_{j\in B} \langle w,\psi_j\rangle.
   \]

3. **Emergent CRFT field value:**
   \[
   \phi(x) \approx \Phi_B.
   \]

For a coherent regime where the spinors within a block are aligned (or nearly so) and the projection direction \(w\) is chosen to correspond to the dominant internal component, we expect:

- \(|\Phi_B|^2 \approx \rho_B\) (up to small corrections),  
- \(\arg\Phi_B\) defines an emergent hydrodynamic phase \(\theta(x)\),  
- \(\rho(x) = |\phi(x)|^2,\ v(x) = \theta_x(x)\) recover the CRFT variables.   

### 4.2 Continuum Limit

As:

- lattice spacing \(\epsilon \to 0\),  
- block size \(|B|\) → large, but still small on the macroscopic scale,

we obtain a continuum field:

\[
\phi(x,t) = \lim_{\epsilon\to 0}\Phi_B(x,t),
\]

which must, for LSDA to be a successful FT candidate, satisfy the CRFT equations:

- CP-NLSE / CE-NWE forms,  
- CRFT dispersion relation,  
- hydrodynamic continuity \(\rho_t + (\rho v)_x = 0\),  
- coherence functional behavior.   

---

## 5. CRFT-Compatibility Checklist

We now compare LSDA against the FT Step-3 requirements and the documented CRFT structures.   

### 5.1 Continuity and Conservation

CRFT requires the continuity equation:

\[
\rho_t + (\rho v)_x = 0.
\]

In LSDA:

- local density: \(\rho(x)\sim\rho_B\sim\text{average}(n_j)\),  
- total density: \(\sum_j n_j = \sum_j \|\psi_j\|^2\) is an additive scalar.

Thus, if LSDA micro-dynamics are chosen to **conserve \(\sum_j n_j\)** (e.g., via local, norm-preserving updates), the algebra is structurally capable of generating a macroscopic continuity equation, just as LCRD is.   

### 5.2 Emergent U(1) Phase and Hydrodynamic Velocity

Because each site has a complex spinor and a fixed projection direction \(w\), the block amplitude \(\Phi_B\) is a complex scalar with:

- phase \(\theta(x) = \arg\phi(x)\),  
- velocity \(v(x) = \theta_x(x)\).

The presence of **internal spinor structure** allows richer internal rotations that still project down to a U(1)-like phase for \(\phi\). This meets the requirement for an emergent complex scalar field with phase and hydrodynamic velocity.   

### 5.3 Dispersion Compatibility

CRFT dispersion (linearized):

\[
\omega^2(k)
= \left(\frac{k^2}{2}\right)^2
+ g\rho_0 k^2
+ \lambda k^4
+ \beta k^6. 
\]

LSDA as an algebra does not fix dynamics; however, it offers **extra internal components** (\(a_j,b_j\)) that can be coupled in the microscopic evolution. For example:

- nearest-neighbor couplings in \(\psi_j\) → \(k^2\) terms,  
- higher-order finite-difference couplings or multi-site stencils on \(\psi_j\) → \(k^4\) and \(k^6\) terms,  
- internal “spinor rotations” coupling components \(a_j,b_j\) → richer dispersion structures that can be tuned to match the CRFT polynomial.

Thus LSDA is structurally well-suited for implementing the full validated dispersive polynomial.

### 5.4 Coherence Functional and Preferred Background

CRFT coherence functional:

\[
C = (|\phi|^2 - \rho_0)^2. 
\]

In LSDA:

- uniform configurations \(\psi_j = \psi_0\) for all \(j\) yield constant density \(n_j = n_0\) and block field \(|\phi|^2 \approx n_0\),  
- deviations in density (\(n_j\neq n_0\)) and/or internal spinor orientation can be used to build micro-coherence measures that, when coarse-grained, approximate CRFT’s coherence functional.

For instance, in addition to density deviations, one can define local “orientation variance” of \(s_j\) within blocks, providing more microscopic handles to reproduce the effective quadratic penalty in \( |\phi|^2 - \rho_0\).

### 5.5 Solitons, Turbulence, and Coherent Structures

CRFT supports:

- dark and bright solitons,  
- higher-dimensional vortices and coherent patterns,  
- turbulence and spectral cascades.   

In LSDA, coherent spatial patterns in both modulus \(\|\psi_j\|\) and internal orientation \(s_j\) can generate **localized, phase-coherent blocks** whose coarse-grained \(\phi(x)\) is soliton-like. The internal spinor structure may help build:

- internal “polarizations” within solitons,  
- additional channels for energy transfer in turbulence that still project onto the CRFT scalar field.

Actual existence and stability of solitons/turbulence patterns are **dynamical questions**, but the LSDA algebra does not obstruct them.

---

## 6. Computational Representation

LSDA remains computationally tractable:

- A configuration is an array \(\{\psi_j\}_{j=1}^N\) of complex 2-vectors.  
- Site-wise composition \(\star_{\text{LSDA}}\) is just vector addition + normalization.  
- Coarse-graining to \(\phi(x)\) is a block-averaged projection along \(w\).  

Compared to LCRD, LSDA doubles the complex DOFs per site but stays within a simple array-of-vectors model suitable for modern numerical methods (finite-difference, spectral, or lattice-based algorithms).   

---

## 7. Open Questions and Next Steps

To evaluate LSDA as a serious FT candidate, further work is needed:

1. **Microscopic Dynamics for \(\psi_j\)**
   - Specify local update equations for \(\psi_j\) that:
     - conserve total density \(\sum_j \|\psi_j\|^2\),  
     - implement finite-difference / spectral stencils that yield the CRFT dispersion after coarse-graining,  
     - generate nonlinearities consistent with CP-NLSE and CE-NWE (e.g., effective \(|\phi|^2\phi\) terms).   

2. **Coarse-Graining Analysis**
   - Derive (analytically or numerically) the effective macroscopic equation for \(\phi(x,t)\) induced by LSDA micro-dynamics.  
   - Check whether CP-NLSE and CE-NWE, with coherence penalties, emerge in an appropriate limit.

3. **Comparison with LCRD (Candidate 01)**
   - Evaluate whether the extra spinor DOFs:
     - make it easier to realize the full CRFT dispersive structure,  
     - provide better numerical stability or robustness,  
     - introduce unnecessary complexity relative to LCRD.   

These tasks will be documented in:

- `ft_candidate_algebra_02_spinor_density_dynamics.md`  
- `ft_candidate_algebra_02_coarse_graining_tests.md`  
- `ft_candidate_algebra_02_numerics.md`  

---

## 8. Summary

**LSDA (Local Spinor–Density Algebra)** introduces:

- per-site spinor DOFs \(\psi_j\in\mathbb{C}^2\),  
- a scalar density \(n_j = \|\psi_j\|^2\) and a unit internal state \(s_j\),  
- a commutative, essentially associative, unital composition law based on spinor addition and normalization,  
- a block-level projection map to a complex scalar field \(\phi(x,t)\) that is structurally compatible with the validated CRFT scalar field,  
- additional internal structure potentially useful for realizing CRFT’s higher-order dispersion and nonlinear behavior.   

LSDA is thus a **second viable candidate algebra** for the FT program. Its suitability will be determined by whether explicit microscopic dynamics on LSDA can, under coarse-graining, recover the mathematically fixed CRFT equations and phenomenology.

---

**Suggested filename:**

`fundamental_theory/ft_candidate_algebra_02_local_spinor_density.md`
