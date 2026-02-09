````markdown

\# Structural Preservation of Plane-Wave Dispersion in the 2D Linear Schrödinger Limit



---



\## Abstract



This paper presents a purely structural formalization of plane-wave dispersion preservation in the two-dimensional linear Schrödinger limit. Using Lean 4, we define the dispersion relation and plane-wave template, establish redundant algebraic equivalences, and prove operator-level reduction results under explicitly stated axioms. We further show that admissible perturbations—defined probe-relatively on the plane-wave family—preserve the reduced dispersion form. All results are conditional on stated axioms and definitions, make no analytic partial differential equation claims, and are confined to the linear regime and plane-wave probes.



---



\## 1. Scope and Epistemic Status



\*\*Epistemic classification:\*\* Structural-only (Lean-verified where stated).



\*\*Explicit scope:\*\*

\- Linear Schrödinger limit only.

\- Plane-wave probe family only.

\- Results are structural and conditional on axioms.



\*\*Explicit exclusions:\*\*

\- No analytic differentiation or functional analysis.

\- No physical interpretation or empirical claims.

\- No geometric or metric structures.

\- No coherence functionals.

\- No claims of universality or inevitability.

\- No Theory of Everything claims.



Empirical validation of dispersion exists elsewhere but is \*\*not used\*\* in any Lean proofs presented here.



---



\## 2. Formal Setting and Definitions



\### 2.1 Field and Plane-Wave Template



\*\*Definition (Field2D)\*\*  

\*Lean source:\* `Dispersion.lean` — `Field2D`  

```lean

abbrev Field2D : Type := ℝ → ℝ → ℝ → ℂ

````



\*\*Definition (planeWave)\*\*

\*Lean source:\* `Dispersion.lean` — `planeWave`



```lean

def planeWave (A : ℂ) (kx ky : ℝ) : Field2D := ...

```



This is a structural template; no analytic properties are assumed or derived.



---



\### 2.2 Locked Dispersion Definition (DR-01)



\*\*Definition (omega)\*\*

\*Lean source:\* `Dispersion.lean` — `omega`



```lean

def omega (kx ky : ℝ) : ℝ := (kx ^ 2 + ky ^ 2) / 2

```



\*\*Lemma (omega\_expand)\*\*

\*Lean source:\* `Dispersion.lean` — `omega\_expand`



```lean

theorem omega\_expand (kx ky : ℝ) : omega kx ky = (kx ^ 2 + ky ^ 2) / 2 := rfl

```



\*\*Status:\*\* DR-01 is \*\*defined\*\*, not derived, in Lean.



---



\## 3. Redundant Algebraic Derivations (Phase A2)



All results in this section are \*\*definitional equalities\*\* (`rfl`) with no operator or PDE machinery.



\*\*Definitions:\*\*

\*Lean source:\* `DR01\_Redundant.lean`



\* `omegaF`

\* `lambdaO`



\*\*Theorems (Definitional Equalities):\*\*



\* `omegaF\_eq\_omega`

\* `lambdaO\_eq\_omega`

\* `routeF\_equals\_routeO`



Each theorem is proven by `rfl`, establishing algebraic equivalence only.



---



\## 4. Operator-Level Structural Reduction (Phase A3)



\### 4.1 Opaque Operators



\*\*Definitions:\*\*

\*Lean source:\* `PlaneWaveOperators.lean`



\* `Dt : Field2D → Field2D`

\* `Dxx : Field2D → Field2D`

\* `Dyy : Field2D → Field2D`

\* `Delta : Field2D → Field2D`

\* `L : Field2D → Field2D`



\*\*Status:\*\* These operators are \*\*uninterpreted symbols\*\*.



---



\### 4.2 Operator Axioms on Plane Waves



\*\*Assumptions / Axioms:\*\*

\*Lean source:\* `PlaneWaveOperators.lean`



\* `Dt\_planeWave`

\* `Delta\_planeWave`



These axioms specify the action of `Dt` and `Delta` on the `planeWave` template only.



---



\### 4.3 EQ-02 Reduction on Plane Waves



\*\*Definition (EQ02Holds)\*\*

\*Lean source:\* `PlaneWaveOperators.lean`



\*\*Supporting Lemmas (Proven):\*\*



\* `iDt\_planeWave\_closed`

\* `negHalfDelta\_planeWave\_closed`



\*\*Theorem (EQ02Holds\_planeWave\_iff)\*\*

\*Lean source:\* `PlaneWaveOperators.lean`



> EQ-02 holds on a plane wave \*\*if and only if\*\* a pointwise scalar coefficient equality holds:

> \[

> \\omega(k\_x,k\_y),\\psi = \\mathrm{eigC}(k\_x,k\_y),\\psi

> ]



\*\*Notes:\*\*



\* No cancellation of `planeWave`.

\* No non-vanishing assumptions.

\* Conditional on operator axioms.



---



\## 5. Dispersion Preservation Under Admissible Perturbations (Phase B)



\### 5.1 Perturbations and Admissibility



\*\*Definition (Perturbation)\*\*

\*Lean source:\* `DispersionPreservation.lean`



\*\*Definition (AdmissibleOnPlaneWave)\*\*

\*Lean source:\* `DispersionPreservation.lean`



Admissibility is \*\*probe-relative\*\* and provides a sufficient (not necessary) condition.



---



\### 5.2 Main Preservation Lemma



\*\*Theorem (EQ02Pert\_planeWave\_reduces\_to\_same\_coeff\_equality)\*\*

\*Lean source:\* `DispersionPreservation.lean`



> If a perturbation vanishes on the plane-wave probe family, the reduced scalar coefficient form is unchanged.



\*\*Status:\*\* Proven; conditional on admissibility and operator axioms.



---



\## 6. Limitations and Non-Claims



The following are \*\*explicitly not proven\*\*:



\* No analytic linearization or derivative theory.

\* No derivation of dispersion from PDE analysis.

\* No geometric or metric structures.

\* No coherence functional.

\* No general perturbation theory.

\* No universality beyond plane-wave probes.

\* No physical interpretation or empirical validation within Lean.



---



\## 7. Summary of Formal Results



\### Definitions



\* `Field2D` → `Dispersion.lean`

\* `planeWave` → `Dispersion.lean`

\* `omega` → `Dispersion.lean`

\* `omegaF`, `lambdaO` → `DR01\_Redundant.lean`

\* `Perturbation`, `AdmissibleOnPlaneWave` → `DispersionPreservation.lean`



\### Proven Theorems / Lemmas



\* `omega\_expand` → `Dispersion.lean`

\* `omegaF\_eq\_omega`, `lambdaO\_eq\_omega`, `routeF\_equals\_routeO` → `DR01\_Redundant.lean`

\* `iDt\_planeWave\_closed`, `negHalfDelta\_planeWave\_closed` → `PlaneWaveOperators.lean`

\* `EQ02Holds\_planeWave\_iff` → `PlaneWaveOperators.lean`

\* `EQ02Pert\_planeWave\_reduces\_to\_same\_coeff\_equality` → `DispersionPreservation.lean`



\### Assumptions / Axioms



\* `Dt\_planeWave` → `PlaneWaveOperators.lean`

\* `Delta\_planeWave` → `PlaneWaveOperators.lean`



```

```



