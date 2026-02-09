\# Test Inventory Master (ToE)



Authoritative inventory of validation tests and repository-wide harness behavior.



This document is intended to be living and auditable.



Each test entry records:



(a) what it validates

(b) what code paths it exercises

(c) what a “PASS” means

(d) assumptions and limitations



Last updated: 2025-12-12 (America/Denver)



How to use this inventory



Always begin with Priority 0.

If any Priority 0 test fails, treat all downstream test results as unreliable until resolved.



Each subsequent priority layer builds on the correctness of the previous ones.

Later tests may assume earlier invariants but do not re-establish them.



When re-running tests, record:

exact command

PASS / FAIL

in the Run log line of each entry.



Priority 0 — Repository-wide harness and meta-tests



These tests establish that:



the repository imports cleanly under pytest

symbolic and numeric foundations are internally coherent

dimension and unit schemas are self-consistent

top-level numeric pipelines do not fail catastrophically



0.0 Pytest harness: tests/conftest.py



Path: tests/conftest.py

Role: Ensures repository root is placed on sys.path so imports resolve reliably.



What it does:

Inserts the project root at the front of sys.path if missing.



Assumptions / risks:

Required when running pytest from arbitrary directories.

Becomes redundant (but harmless) if the project is later installed as a package.



Action:

Keep unless switching to an editable install.



0.1 Core coherence definitions



Path: tests/test\_coherence\_core.py

Primary imports exercised: toe.coherence



Purpose:

Validates internal consistency of the coherence scalar, density, and flux definitions.



What it checks:

Finite, bounded outputs for representative signals.

Agreement between scalar coherence and its density/flux decomposition.



What it does not do:

Does not prove any physical interpretation of “coherence.”

Does not validate long-time behavior or numerical convergence beyond tested cases.



Run log:

pytest -q tests/test\_coherence\_core.py → PASS



Failure implication:

All coherence-based metrics and interpretations become unreliable.



0.2 Cross-module consistency



Path: tests/test\_consistency.py

Primary imports exercised: toe.units, toe.dims, toe.meta\_axioms



Purpose:

Ensures theory-wide invariants and shared schemas remain synchronized.



What it checks:

Dimension and unit schema agreement.

Presence and stability of declared axioms.

No silent cross-file drift.



What it does not do:

Does not validate that the axioms correspond to external physics.

Does not validate numerical solvers.



Run log:

PASS



Failure implication:

Repository-level integration break.



0.3 Dimension schema sanity



Path: tests/test\_dims.py

Purpose:

Confirms dimension registry is well-formed.



What it does not do:

Does not guarantee every equation in the repo uses the dimension system correctly.



Run log:

PASS



0.4 Algebraic / calculus identities



Path: tests/test\_identities.py

Purpose:

Verifies core analytic identities used throughout derivations.



What it does not do:

Does not validate the choice of which identities are physically relevant.



Run log:

PASS



0.5 Unit schema validity



Path: tests/test\_units\_schema.py

Purpose:

Confirms unit composition rules behave as defined.



What it does not do:

Does not guarantee units are applied consistently in every downstream model.



Run log:

PASS



0.6 Meta-axioms invariants



Path: tests/test\_meta\_axioms.py

Purpose:

Ensures invariants defined at the axiomatic level evaluate correctly.



What it does not do:

Does not establish that the meta-axioms are correct as a scientific description.



Run log:

PASS



0.7 Entropy scaling sanity



Path: tests/test\_entropy\_scaling.py

Purpose:

Confirms entropy-like quantities remain finite and well-behaved.



What it does not do:

Does not prove any thermodynamic interpretation.

Does not validate asymptotic scaling laws beyond the tested ranges.



Run log:

PASS



0.8 LR velocity sanity



Path: tests/test\_lr\_velocity.py

Purpose:

Ensures LR velocity estimators return finite, bounded values.



What it does not do:

Does not prove that LR velocity corresponds to any physically measurable speed.



Run log:

PASS



0.9 KL pipeline smoke test



Path: tests/test\_kl\_map\_smoke.py

Purpose:

Confirms Knill–Laflamme checking pipeline executes end-to-end.



What it does not do:

Does not guarantee KL conditions hold for arbitrary codes or random instances.



Run log:

PASS



0.10 KL scaling sanity



Path: tests/test\_kl\_scaling.py

Purpose:

Ensures KL checks remain numerically finite under small dimension changes.



What it does not do:

Does not assert success of KL conditions; it asserts numerical stability/finite outputs.



Run log:

PASS



Priority 1A — Foundational PDE structure (CRFT / CP–NLSE / UCFF)



These tests validate the canonical field-theoretic backbone of the project.



They establish:

continuity equations

dispersion relations

Euler–Lagrange correctness

conservation laws

dimensional admissibility

equivalence of real and complex formulations



Failure here invalidates all higher-level claims.



1A.1 Phase 2 continuity equation



Path: tests/test\_phase2\_continuity.py

Purpose:

Verifies symbolic correctness of the derived continuity equation.



What it does not do:

Does not validate boundary-condition handling in simulations.

Does not validate numerical discretization.



Run log:

PASS



1A.2 Phase 2 dispersion relation



Path: tests/test\_phase2\_dispersion.py

Purpose:

Confirms analytic ω(k) structure.



What it does not do:

Does not guarantee dispersion accuracy under all parameter regimes.



Run log:

PASS



1A.3 Phase 2 Euler–Lagrange residual



Path: tests/test\_phase2\_el\_residual.py

Purpose:

Ensures variational derivation matches implemented equations.



What it does not do:

Does not prove the Lagrangian is physically correct; it proves internal consistency.



Run log:

PASS



1A.4 Phase 3 conservation laws



Path: tests/test\_phase3\_conservation.py

Purpose:

Validates conservation of quadratic invariants.



What it does not do:

Does not guarantee conservation for all integrators/resolutions; it is limited to tested setups.



Run log:

PASS



1A.5 Phase 3 dimensional consistency



Path: tests/test\_phase3\_dimensional.py

Purpose:

Confirms dimensional admissibility of all extended terms.



What it does not do:

Does not guarantee numerical scaling correctness.



Run log:

PASS



1A.6 Phase 3 positivity



Path: tests/test\_phase3\_positivity.py

Purpose:

Ensures density- and energy-like quantities remain non-negative under tested constructions.



What it does not do:

Does not prove global well-posedness or full nonlinear stability.



Run log:

PASS



1A.7 Real vs. complex equivalence



Path: tests/test\_phase3\_symplectic\_equiv.py

Purpose:

Demonstrates equivalence between real symplectic and complex formulations.



What it does not do:

Does not select which formulation is “more physical”; it validates equivalence as implemented.



Run log:

PASS



Priority 1B — Core soliton and scattering dynamics (CRFT)



These tests validate the nonlinear regime underpinning soliton existence and interaction.



1B.1 Soliton existence and stability



Path: tests/test\_phase5\_soliton.py

Purpose:

Confirms existence and short-time stability of soliton solutions.



What it does not do:

Does not prove asymptotic stability or multi-parameter bifurcation structure beyond tested cases.



Run log:

PASS



1B.2 Soliton scattering dynamics



Path: tests/test\_phase6\_scattering.py

Purpose:

Validates controlled soliton interactions and coherence dip/recovery behavior.



What it does not do:

Does not guarantee quantitative scattering phase shifts or exact integrability properties.



Run log:

PASS



Priority 1C — High-rigor numerics and proof-assist tests



Status: PASS



Includes:

coercivity bounds

Kibble–Zurek scaling demonstrations

manufactured solutions

Noether identities

CP–NLSE numerical regressions

robustness and convergence checks

lemma-level proof harnesses



What these tests do:

Provide the strongest internal validators for the equation set and numeric routines under the project’s own definitions.



What these tests do not do:

Do not constitute external peer-reviewed proof of physical correctness.

Do not cover all parameter regimes or all solver implementations.



Priority 1D — UCFF core consistency



Status: PASS



Validates:

symbolic UCFF self-consistency

symbolic ↔ numeric round-trip integrity



What it does not do:

Does not validate extended subsystems (metrics, hydro, χ-field, etc.) unless those are explicitly included in separate test groups.



Conclusion:

UCFF core is synchronized across symbolic definitions, numerical solvers, and documented equations.



Priority 2 — Extended subsystems (validated interfaces and diagnostics)



These tests extend the core theory into multi-field coupling, emergent geometry, and qualitative coherence response.

They are explicitly layered on top of Priority 1 and do not redefine the canonical PDE backbone.



2A.1 φ–χ coupled field extension



Path: tests/test\_phase15\_coupled\_phi\_chi.py

Purpose:

Validates symbolic structure of the coupled φ–χ system.



What it checks:

Presence of required coupling and dispersion terms.

Consistent linearized mode structure.

Correct symbol inventory.



Interpretation:

This test validates structural correctness, not a derived physical dispersion law.



Run log:

PASS



2A.2 Minimal backreaction and metric response



Path: tests/test\_phase18\_backreaction.py

Purpose:

Validates a toy / minimal emergent-metric backreaction interface.



What it checks:

Stress-energy construction from φ.

Baseline metric recovery when coupling is disabled.

Algebraic trace coupling consistency.

Natural-unit reduction helper.



Interpretation:

This is a toy / minimal backreaction layer, not a full gravitational theory.



Run log:

PASS



2A.3 Coherence response diagnostics (Phase 24 / 26 / 27)



Path: tests/test\_phase33\_coherence\_response.py

Associated modules:

phase24\_dark\_soliton\_coherence

phase26\_bright\_soliton\_coherence

phase27\_vortex\_coherence



Purpose:

Demonstrates qualitative directional response of solitons and vortices under a coherence penalty.



What it checks:

Dark soliton cores fill as coherence penalty increases.

Bright soliton peaks are suppressed.

Vortex cores remain bounded.



Explicit scope and limitations:

These modules implement diagnostic / modeled coherence relaxation, not full UCFF or CP–NLSE time evolution.

When coherence coupling is disabled, baseline dynamics are intentionally not evolved.

These tests support interpretive and qualitative claims only.



Run log:

PASS



Interpretation:

Confirms directional coherence response behavior.

Does not assert quantitative physical accuracy or Hamiltonian completeness.



Priority 2B — GPE / hydrodynamic / higher-order CE (limits, structure, and numerics)



This group validates that:



(1) the UCFF / CE formulations reduce correctly to Gross–Pitaevskii / cubic NLS limits when higher-order and auxiliary couplings are disabled

(2) hydrodynamic reductions exhibit the expected structural terms and limiting behavior

(3) higher-order dispersion structure (k^4, k^6) is present and numerically consistent under multiple stepping approaches

(4) qualitative second-order phenomena appear in controlled settings



What these tests do not do:

Do not guarantee uniqueness of the reduction or physical completeness of the hydrodynamic closure beyond the tested structure.

Do not guarantee high-accuracy solutions in all regimes; tolerances and setups are explicitly limited.



Run log:

PASS (Phase 11–13, Phase 31/31A per user re-run logs)



Priority 2C — Hydrodynamic + metric / acoustic geometry (structure and local numeric checks)



This group validates the acoustic metric and hydro metric formulations as implemented across several modules.

These tests are intended to confirm internal structural correctness and local consistency properties, not to enforce a single global convention unless explicitly stated.



2C.1 Phase 21 — hydrodynamic structural formulation



Path: tests/test\_phase21\_hydrodynamics.py

Primary implementation exercised: equations/phase21\_hydrodynamics.py (with shared symbols from equations/phase9\_freeze.py)



What it does:



Confirms that the hydrodynamic continuity/Euler structures are present in first-order form.



Confirms that second-order hydrodynamics includes higher-order spatial derivatives consistent with λ and β extensions.



Confirms that helper dispersion constructions contain the expected k-power structure (k^2, k^4, and with second-order also k^6) and reference parameters (g, rho0, lam, beta) in the way the implementation defines them.



What it does not do:



Does not prove the hydrodynamic system is derived uniquely from a single Lagrangian in all cases.



Does not validate a specific numerical scheme’s accuracy; it validates symbolic structure and presence/absence of required terms.



Run log:

PASS (user re-run log, 4 tests)



2C.2 Phase 25 — hydro metric (symbolic, coherence-aware)



Path: tests/test\_phase25\_hydro\_metric.py

Primary implementation exercised: equations/phase25\_hydro\_metric.py



What it does:



Confirms that coherence-dependent terms appear in the hydro-metric construction where expected by that module’s definitions.



Confirms that the module’s effective pressure and sound-speed extraction behave as that module defines them.



Confirms that the symbolic acoustic metric uses the effective sound speed produced by that module.



What it does not do:



Does not enforce that other modules use the same coherence-to-sound-speed convention.



Does not prove that the acoustic metric corresponds to an experimentally verified spacetime geometry.



Run log:

PASS (user re-run log, 3 tests)



2C.3 Phase 29 — acoustic metric numerics (parameter dependence and signature)



Path: tests/test\_phase29\_acoustic\_metric\_numerics.py

Primary implementation exercised: equations/phase29\_acoustic\_metric\_numerics.py (and parameter container as imported by that module)



What it does:



Confirms numeric computation of c\_eff and the corresponding diagonal metric form used in that module.



Confirms monotonic behavior of c\_eff with respect to lambda\_coh according to that module’s implemented rule.



Confirms the metric has the expected signature in the tested parameter regime.



What it does not do:



Does not guarantee that the numeric c\_eff formula matches the symbolic c\_eff formula used in other modules.



Does not validate full PDE evolution; it validates metric-related numeric constructions.



Run log:

PASS (user re-run log, 5 tests)



2C.4 Phase 34 — hydro metric numeric (local consistency in a coherence-free construction)



Path: tests/test\_phase34\_hydro\_metric\_numeric.py

Primary implementation exercised: equations/ucff\_core.py (symbols and constants used to build a local metric in the test)



What it does:



Confirms that a local acoustic-metric construction using c\_eff^2 = g\*rho0 behaves consistently (baseline metric components) in the tested setup.



What it does not do:



Does not test coherence-on behavior for sound speed or metric.



Does not test cross-module agreement; it is a local construction check.



Run log:

PASS (user re-run log, 2 tests)



2C.5 Phase 35 — hydro symbolics (symbolic pressure, coherence potential, and sound-speed extraction)



Path: tests/test\_phase35\_hydro\_symbolics.py

Primary implementation exercised: equations/hydro\_symbolics.py



What it does:



Confirms that symbolic definitions (velocity, quantum-pressure-like pieces, coherence potential) match exact expected forms in that module.



Confirms that the module’s effective pressure definition and its derivative-based sound-speed extraction match the module’s implemented convention.



What it does not do:



Does not enforce that the phase25 or phase29 conventions for c\_eff match this module.



Does not validate numerical stability or convergence of a hydro-metric PDE solver.



Run log:

PASS (user re-run log, 8 tests)



Priority 2C group-level limitation (explicit)



What Priority 2C tests do:



Validate that each hydro/metric module is internally self-consistent under its own definitions and that key structural properties and local numeric properties hold.



What Priority 2C tests do not:



Do not enforce a single global coherence-to-sound-speed convention across all hydro/metric modules unless a dedicated cross-module contract test is added.



Do not prove that the acoustic metric is physically realized; they validate the implemented mathematical structures and selected numeric behaviors.



Priority 2D — Geometry + LCRD hooks (structure-level bridge tests)



This group provides the geometry bridge layer and LCRD hook points referenced by the monograph.



These tests do:



Validate internal symbolic structure, limiting behavior, and self-consistency of the implemented geometry and hook formulations.



Confirm that certain “flat limits” reduce to zero curvature / zero Einstein tensor in the toy 1+1D construction.



Confirm that selected stress-energy constructions and hydrodynamic Jacobians match the exact algebraic forms implemented in their target modules.



These tests do not:



Validate full general-relativistic dynamics, constraints, or covariant conservation beyond the specific toy identities checked.



Enforce global cross-module unification of the “equation of state” / pressure closure used for sound speed and characteristic structure.



Validate that these geometry bridge modules exactly match any external document, including LCRD\_Reconstruction\_v3.md and Extended CRFT docs, unless those documents’ exact formulas are re-checked against the tested implementations.



Validate LCRD’s rotor-curvature closure equations (R, K, Q\_rotor) themselves; LCRD has its own implementation and test family.



2D.1 Phase 17 — Geometry scaffolding (effective metrics and curvature proxies)



Path: tests/test\_phase17\_geometry.py

Primary implementation exercised: equations/phase17\_geometry.py



What it does:



Confirms 1D/2D/3D “effective metric” objects are returned with the expected matrix sizes (2×2, 3×3, 4×4).



Confirms entries include dependence on the declared sound-speed symbol c and/or basic coordinate symbols as required by the implementation.



Confirms the curvature-proxy routines return scalar expressions with the expected symbol dependence.



What it does not do:



Does not test that these metrics are derived from CRFT hydrodynamics, LSDA, or LCRD reconstruction.



Does not test geometric correctness of curvature (Ricci, Riemann) computed from these metrics; it tests the metric objects and curvature proxies as implemented.



Run log:

pytest -q tests/test\_phase17\_geometry.py → PASS (4 tests)



2D.2 Phase 19 — Einstein-geometry toy consistency (1+1D)



Path: tests/test\_phase19\_einstein\_geometry.py

Primary implementation exercised: equations/phase19\_einstein\_geometry.py

Additional dependency used by the test: equations/phase18\_backreaction.py (metric definition) and equations/phase9\_freeze.py (shared symbols)



What it does:



Builds Christoffel symbols, Ricci tensor/scalar, and Einstein tensor for the toy 1+1D backreaction metric used by the Phase 19 layer.



Confirms these tensors vanish in the explicit flat limit (kappa → 0 with rho → rho0).



Confirms the trace equation is structurally consistent and reduces to zero in the same flat limit.



Confirms the “natural units” helper removes explicit (ħ, m, c) symbols from the Einstein tensor expression.



What it does not do:



Does not implement or validate full GR field equations (no full Einstein equation solve, no constraint propagation).



Does not validate physical sourcing or covariant conservation beyond the checked toy identities and flat-limit reductions.



Run log:

pytest -q tests/test\_phase19\_einstein\_geometry.py → PASS (4 tests)



2D.3 Phase 42 — Coherence stress-energy construction (hydrodynamic form)



Path: tests/test\_phase42\_coherence\_stress\_energy.py

Primary implementation exercised: equations/phase42\_coherence\_stress\_energy.py



What it does:



Confirms an explicitly constructed hydrodynamic stress-energy tensor T^{μν} matches the implementation’s algebraic forms on a Minkowski background.



Confirms the coherence potential and contact potential take the exact functional forms implemented in Phase 42.



Confirms coherence-only stress-energy contributions vanish when lambda\_coh = 0.



What it does not do:



Does not couple the constructed stress-energy into Phase 19 geometry or any Einstein-like equation.



Does not enforce agreement with other modules’ pressure / sound-speed conventions; it validates the Phase 42 definitions as implemented.



Run log:

pytest -q tests/test\_phase42\_coherence\_stress\_energy.py → PASS (6 tests)



2D.4 Phase 43 — Hydrodynamic Jacobians (characteristic structure hook)



Path: tests/test\_phase43\_hydro\_jacobians.py

Primary implementation exercised: equations/phase43\_hydro\_jacobians.py



What it does:



Defines a 1D quasilinear hydrodynamic system in variables (rho, v) with a specified pressure closure P(rho).



Constructs the Jacobian A(U) of the flux map and checks exact algebraic forms for A(U), the rest-state Jacobian, and its characteristic polynomial.



Extracts an effective characteristic speed via the implementation’s derivative-based rule at rho = rho0 and confirms the expected polynomial form λ^2 − c\_eff^2.



What it does not do:



Does not validate a full PDE solver, numerical stability, or long-time evolution for this system.



Does not enforce that the pressure closure used here matches Phase 42, Phase 25, or other hydro/metric modules; it validates the Phase 43 closure and linearization hook as implemented.



Run log:

pytest -q tests/test\_phase43\_hydro\_jacobians.py → PASS (7 tests)



Priority 2D group-level interpretation



What a PASS in Priority 2D means:



The geometry and hook modules are internally self-consistent under their own definitions, and the specific limiting behaviors and algebraic identities encoded by these tests are satisfied.



What a PASS in Priority 2D does not mean:



It does not mean the geometry bridge is uniquely derived from CRFT, LSDA, or LCRD documents.



It does not mean the monograph’s geometry discussion is automatically “in sync” with LCRD\_Reconstruction\_v3.md or Extended\_CRFT\_v1.md; that requires explicit document-to-code reconciliation.



Priority 3 — Long-time robustness, stability, and phenomenology



These tests support “numerically stable and physically reasonable” narratives only in the following restricted sense:



What Priority 3 tests do:



Validate that selected long-run and parameter-scan pipelines execute reliably under defined settings.



Validate that outputs are finite, bounded (within defined tolerances), structurally consistent (expected keys/shapes), and reproducible under fixed seeds where applicable.



Validate that defined coherence metrics and stability functionals produce expected ordering on reference fields (e.g., plane-wave-like versus noisy fields).



Validate that phase-diagram and regime-map constructions are self-consistent (labels match masks, deterministic outputs match repeated runs).



What Priority 3 tests do not do:



Do not prove physical correctness of the model beyond internal consistency and tested behavior.



Do not prove global well-posedness, global stability, or mathematical existence/uniqueness results.



Do not, by themselves, establish solver convergence (grid/time refinement) unless explicitly encoded by the test.



Do not enforce a single unified “coherence equation-of-state” or “coherence energy” definition across all diagnostic modules; Priority 3 contains both diagnostic/qualitative evolvers and UCFF-adjacent scan pipelines.



3.1 Phase 32 — long-time robustness



Path: tests/test\_phase32\_longtime\_robustness.py



What it does:



Runs long-time robustness checks on the Phase 24/26/27 diagnostic coherence-evolution modules (dark soliton, bright soliton, vortex).



Enforces that key diagnostics remain finite and that drift/boundedness constraints used by the test are satisfied over the long-time run.



What it does not do:



Does not validate full UCFF/CP–NLSE baseline dynamics for lambda\_coh = 0; these diagnostic modules intentionally do not evolve baseline dynamics in that case.



Does not prove physical long-time asymptotics; it validates numerical robustness in the defined diagnostic models.



Run log:

pytest -q tests/test\_phase32\_longtime\_robustness.py → PASS (3 tests; user re-run log)



3.2 Phase 40 — soliton stability scan



Path: tests/test\_phase40\_soliton\_stability\_scan.py



What it does:



Executes a stability-scan pipeline and checks:



output structure is correct,



stability flags meet the test’s expectations in the tested cases,



mass/diagnostic drift remains below explicit tolerances,



maxima remain finite and nonpathological under test settings.



What it does not do:



Does not prove stability for arbitrary parameters.



Does not provide a theorem-level stability proof; it is a boundedness/drift validator on a scan grid.



Run log:

pytest -q tests/test\_phase40\_soliton\_stability\_scan.py → PASS (4 tests; user re-run log)



3.3 Phase 41 — multiscale soliton fine test



Path: tests/test\_phase41\_multiscale\_soliton\_fine.py



What it does:



Runs a multiscale soliton fine-structure pipeline and checks correctness of returned structure, finiteness, and boundedness criteria defined by the test.



What it does not do:



Does not establish asymptotic multiscale validity across all parameter regimes.



Does not certify convergence without explicit refinement checks.



Run log:

pytest -q tests/test\_phase41\_multiscale\_soliton\_fine.py → PASS (2 tests; user re-run log)



3.4 Phase 44 — soliton interactions



Path: tests/test\_phase44\_soliton\_interactions.py



What it does:



Validates soliton interaction scenarios produce outputs with expected keys/shapes and remain finite/bounded under the test’s constraints.



What it does not do:



Does not validate exact integrable scattering data (phase shifts, exact invariants).



Does not prove physical correctness of interaction outcomes beyond the model’s implemented definitions.



Run log:

pytest -q tests/test\_phase44\_soliton\_interactions.py → PASS (8 tests; user re-run log)



3.5 Phase 45 — two-soliton phase-locked



Path: tests/test\_phase45\_two\_soliton\_phase\_locked.py



What it does:



Validates a two-soliton phase-locked scenario remains finite and satisfies the test’s internal consistency and boundedness criteria.



What it does not do:



Does not prove phase-locking is universal or uniquely determined.



Does not validate robustness under arbitrary perturbations unless tested.



Run log:

pytest -q tests/test\_phase45\_two\_soliton\_phase\_locked.py → PASS (4 tests; user re-run log)



3.6 Phase 46 — coherent turbulence (1D)



Path: tests/test\_phase46\_coherent\_turbulence\_1d.py



What it does:



Validates coherent-turbulence initial condition generation, core evolution pipeline execution, and structural properties (expected shapes, finiteness, and basic spectral sanity) under the tested setup.



What it does not do:



Does not validate turbulence universality, scaling laws, or high-resolution inertial-range properties.



Does not constitute a full turbulence validation campaign.



Run log:

pytest -q tests/test\_phase46\_coherent\_turbulence\_1d.py → PASS (4 tests; user re-run log)



3.7 Phase 47 — coherence phenomenology maps



Path: tests/test\_phase47\_coherence\_phenomenology\_maps.py



What it does:



Validates phenomenology map construction returns correctly structured outputs (keys/shapes), finite metrics, and repeatable behavior where the test fixes settings.



What it does not do:



Does not prove phase boundaries correspond to unique physical phases.



Does not enforce cross-module unification of the meaning of “coherence” beyond the metrics used here.



Run log:

pytest -q tests/test\_phase47\_coherence\_phenomenology\_maps.py → PASS (3 tests; user re-run log)



3.8 Phase 48 — coherence phase diagram



Path: tests/test\_phase48\_coherence\_phase\_diagram.py



What it does:



Validates phase diagram pipeline returns structured outputs and satisfies deterministic constraints and basic sanity checks under the test’s fixed settings.



What it does not do:



Does not prove the phase diagram is unique, physically correct, or robust across all seeds unless explicitly tested.



Run log:

pytest -q tests/test\_phase48\_coherence\_phase\_diagram.py → PASS (3 tests; user re-run log)



3.9 Phase 50 — coherence metrics



Path: tests/test\_phase50\_coherence\_metrics.py



What it does:



Validates coherence metric functions return expected shapes, finite values, and ordering behavior on reference fields (coherent vs noisy).



What it does not do:



Does not prove metric uniqueness or physical necessity.



Does not prove metric values correspond to experimentally measurable observables.



Run log:

pytest -q tests/test\_phase50\_coherence\_metrics.py → PASS (7 tests; user re-run log)



3.10 Phase 51 — coherence drift metrics



Path: tests/test\_phase51\_coherence\_drift\_metrics.py



What it does:



Validates drift metrics and aggregation logic return finite values and correctly shaped summaries for tested scenarios.



What it does not do:



Does not prove global bounded drift across all parameter regimes.



Does not validate solver convergence.



Run log:

pytest -q tests/test\_phase51\_coherence\_drift\_metrics.py → PASS (6 tests; user re-run log)



3.11 Phase 52 — coherence stability functionals



Path: tests/test\_phase52\_coherence\_stability\_functionals.py



What it does:



Validates stability functional computations (order/uniformity/fragmentation-type measures) are finite and produce expected ordering on reference fields.



What it does not do:



Does not prove these functionals are sufficient as dynamical stability criteria.



Does not prove equivalence to Hamiltonian stability.



Run log:

pytest -q tests/test\_phase52\_coherence\_stability\_functionals.py → PASS (6 tests; user re-run log)



3.12 Phase 53 — static field classification



Path: tests/test\_phase53\_static\_field\_classification.py



What it does:



Validates deterministic rule-based classification of fields returns expected keys and stable labels/scores on reference cases.



What it does not do:



Does not prove classifications correspond to physically distinct phases.



Does not guarantee generalization outside tested settings.



Run log:

pytest -q tests/test\_phase53\_static\_field\_classification.py → PASS (5 tests; user re-run log)



3.13 Phase 55 — coherence–soliton interaction map



Path: tests/test\_phase55\_coherence\_soliton\_interaction\_map.py



What it does:



Validates interaction-map pipeline returns structured maps (keys/shapes), stable numeric outputs, and expected baseline normalization anchors where defined by the test.



What it does not do:



Does not prove a universal soliton stabilization mechanism.



Does not establish convergence beyond the tested configuration.



Run log:

pytest -q tests/test\_phase55\_coherence\_soliton\_interaction\_map.py → PASS (4 tests; user re-run log)



3.14 Phase 56 — invariant scan



Path: tests/test\_phase56\_invariant\_scan.py



What it does:



Validates invariant drift scan outputs are finite, correctly shaped, and satisfy the test’s boundedness/inequality constraints.



What it does not do:



Does not prove exact conservation.



Does not prove invariants remain bounded under all solvers/resolutions.



Run log:

pytest -q tests/test\_phase56\_invariant\_scan.py → PASS (3 tests; user re-run log)



3.15 Phase 57 — multisoliton coherence convergence



Path: tests/test\_phase57\_multisoliton\_coherence\_convergence.py



What it does:



Validates multisoliton convergence-summary outputs are finite, correctly shaped, and internally consistent under tested cases.



What it does not do:



Does not provide formal convergence-order certification without explicit refinement ladders.



Does not prove “cluster” ontologies; it validates the computed convergence summary pipeline.



Run log:

pytest -q tests/test\_phase57\_multisoliton\_coherence\_convergence.py → PASS (2 tests; user re-run log)



3.16 Phase 58 — master coherence stability map



Path: tests/test\_phase58\_master\_coherence\_stability.py



What it does:



Validates master regime map construction returns a correctly shaped label array with labels in the expected set and masks consistent with labels.



Validates determinism under fixed seeds/settings where specified by the test.



What it does not do:



Does not prove regime boundaries are physically correct or unique.



Does not prove robustness to all seeds unless explicitly tested.



Run log:

pytest -q tests/test\_phase58\_master\_coherence\_stability.py → PASS (2 tests; user re-run log)

Priority 4A — CLI, orchestration, and output bundling



The Priority 4A tests validate tooling, orchestration, and reporting layers that sit above the core theory.

They do not validate equations of motion, numerical solvers, physical correctness, or mathematical completeness.



A failure in Priority 4A indicates a defect in execution control, metadata capture, or result packaging, not a failure of CRFT, UCFF, LSDA, or LCRD theory layers.



4A.1 Phase 15 — CLI helper and provenance capture



Path:

tests/test\_phase15\_cli.py



Primary implementation exercised:

examples/phase15\_cli.py



What this test validates:



This test validates that the CLI helper layer correctly constructs and returns structured execution metadata and dispatches supported phases through a callable interface.



Specifically, it confirms that provenance information is captured in a deterministic dictionary containing timestamps, Python and NumPy version strings, working directory information, and a cryptographic hash of input parameters.



It confirms that supported phase identifiers are dispatched to the correct internal routines and that the returned result objects contain the expected top-level structure, including phase identifiers, provenance blocks, and result payload dictionaries.



It confirms that unsupported phase identifiers are rejected with an explicit, structured error message rather than silent failure or undefined behavior.



What this test does not validate:



This test does not validate the numerical accuracy, physical correctness, or scientific interpretation of any phase results.



It does not validate command-line argument parsing, shell-level invocation, environment configuration, or executable entry points.



It does not validate reproducibility of scientific results beyond the structural presence of metadata.



Run log:

pytest -q tests/test\_phase15\_cli.py → PASS



4A.2 Linear-program orchestration helper



Path:

tests/test\_lp\_orchestration.py



Primary implementation exercised:

toe/lp\_orchestration.py



What this test validates:



This test validates that the linear-program orchestration helper executes successfully and returns a finite, non-negative objective value under the tested configuration.



It confirms that the returned task-selection structure has the expected dimensionality and type and is compatible with downstream orchestration logic.



What this test does not validate:



This test does not prove that the linear program is optimal, globally correct, or unique.



It does not independently verify enforcement of memory or time constraints beyond what the orchestration helper internally encodes.



It does not validate scheduling correctness for untested parameter regimes.



Run log:

pytest -q tests/test\_lp\_orchestration.py → PASS



4A.3 Phase 54 — output bundling for static fields and drift diagnostics



Path:

tests/test\_phase54\_output\_bundling.py



Primary implementation exercised:

phase54\_output\_bundling.py

(with downstream use of Phase 50, Phase 51, Phase 52, and Phase 53 diagnostic modules)



What this test validates:



This test validates that static-field and drift-diagnostic results are bundled into a structured dictionary with predictable keys corresponding to the contributing diagnostic phases and an aggregate summary section.



It confirms that reference-case ordering behaves as expected under the implemented metrics, such that plane-wave-like fields score at least as coherent as explicitly noisy fields according to the bundled summaries.



It confirms that when identical initial and final fields are supplied, the bundled drift diagnostics report near-zero drift and unity-ratio behavior consistent with the module’s definitions.



It validates that the markdown report generation functions return structured text containing the expected section headers and summary content.



What this test does not validate:



This test does not validate the physical correctness, completeness, or uniqueness of any bundled metric.



It does not enforce real-valued semantics beyond the implementation’s internal casting rules.



It does not validate convergence, stability, or solver correctness of any contributing diagnostic phase.



Run log:

pytest -q tests/test\_phase54\_output\_bundling.py → PASS

(with ComplexWarning due to real casting of complex diagnostic arrays)



4A.4 Phase 60 — multi-phase output bundling and serialization



Path:

tests/test\_phase60\_output\_bundling.py



Primary implementation exercised:

phase60\_output\_bundling.py



What this test validates:



This test validates that multi-phase result bundles are assembled into a JSON-safe structured dictionary containing metadata, summary information, and per-phase result blocks.



It confirms that missing phases are handled deterministically and explicitly represented as absent rather than silently omitted.



It validates that serialization to JSON and deserialization back into Python data structures preserves the bundled content exactly for the tested fields.



What this test does not validate:



This test does not validate the scientific correctness, internal consistency, or physical interpretation of any included phase.



It does not validate human-readable presentation quality beyond structural correctness and serialization safety.



Run log:

pytest -q tests/test\_phase60\_output\_bundling.py → PASS



Priority 4B — Predictions, noise, random graphs, tensor (draft text)



The Priority 4B tests validate prediction helpers, noise channel plumbing, random-graph substrate entropy proxies, and tensor-based coherence and entropy utilities. These tests do not validate CRFT, UCFF, LSDA, LCRD equations of motion, hydrodynamic closures, metric constructions, or soliton dynamics.



A PASS in Priority 4B means that the relevant helper modules execute, return correctly shaped outputs, and satisfy the limited structural and ordering constraints encoded by the tests. It does not establish physical correctness beyond those constraints.



4B.1 Predictions core



Path:

tests/test\_predictions\_core.py 



Primary implementation exercised:

toe/qca.py (via SplitStepQCA1D, energy\_conservation\_proxy)



What this test validates:



Validates that the QCA lightcone predictor returns a finite radius and that the implied effective velocity computed as radius / steps does not exceed a fixed upper bound with small slack (v\_eff <= 1.05) for the tested QCA parameters and step count. 



Validates that a drift proxy derived from energy\_conservation\_proxy is weakly monotone non-decreasing as a noise probability parameter p increases across a small grid of tested p values, within a numerical slack. 



What this test does not validate:



Does not validate that the lightcone bound corresponds to a physically meaningful speed limit outside this QCA construction.



Does not validate that energy\_conservation\_proxy measures physical energy conservation; it validates monotone behavior of the chosen proxy under the tested noise injection interface.



Does not validate large-system scaling or asymptotic behavior; it is limited to the specific N and T used in the test.



Run log:

pytest -q tests/test\_predictions\_core.py → PASS (2 tests; user re-run log)



4B.2 Noise channels



Path:

tests/test\_noise\_channels.py 



Primary implementation exercised:

toe/noise.py (via bit\_flip, phase\_flip, depolarizing, apply\_channel) and toe/qca.py (via SplitStepQCA1D, energy\_conservation\_proxy)



What this test validates:



Validates that each noise helper (bit\_flip, phase\_flip, depolarizing) returns a state vector whose norm is preserved to within a tight tolerance for the tested probability p and RNG. 



Validates that apply\_channel dispatches correctly for the channel name strings "bitflip", "phaseflip", and "depolarizing", returning a state vector of the same shape as the input. 



Validates that a drift measure derived from energy\_conservation\_proxy and then reduced to a scalar drift is weakly monotone non-decreasing as p increases across the tested values. 



What this test does not validate:



Does not validate that these channels are completely-positive trace-preserving maps in the density-matrix sense; the test operates on state vectors and checks norm preservation and dispatch behavior.



Does not validate physical noise realism or calibration; it validates only the implemented functional behavior under the tested inputs.



Does not validate statistical properties of the RNG usage beyond deterministic reproducibility implied by fixed seeds in the test.



Run log:

pytest -q tests/test\_noise\_channels.py → PASS (3 tests; user re-run log)



4B.3 Noise scan



Path:

tests/test\_noise\_scan.py 



Primary implementation exercised:

toe/qca.py (via SplitStepQCA1D, energy\_conservation\_proxy)



What this test validates:



Validates that a scalar drift summary computed from the output of energy\_conservation\_proxy increases from the zero-noise case to the highest tested noise case (p=0.2) for the tested configuration. 



What this test does not validate:



Does not validate a full monotonic curve across all intermediate p; it asserts only that drift at the first tested point is less than drift at the last tested point.



Does not validate the correctness of the proxy as energy, only that the implemented proxy responds to noise under the tested interface.



Does not validate behavior outside the tested system size and step count.



Run log:

pytest -q tests/test\_noise\_scan.py → PASS (1 test; user re-run log)



4B.4 Random graph area proxy



Path:

tests/test\_random\_graph\_area.py 



Primary implementation exercised:

toe/substrate.py (via Substrate) and NetworkX graph construction used in the test.



What this test validates:



Builds an Erdős–Rényi graph with fixed parameters and constructs a Substrate with a specified bond dimension.



For a small chosen region of vertices A, validates that the returned entropy proxy S.entropy\_of(A).s\_bits is non-negative. 



Validates that this entropy proxy does not exceed an explicit upper bound based on the number of boundary edges leaving the region times log2(bond\_dim). 



What this test does not validate:



Does not validate that this entropy proxy equals a physically correct entanglement entropy; it validates non-negativity and a cut-based upper bound consistent with the implementation’s “minimal cut” style logic.



Does not validate correctness for all graphs or all region choices; it is limited to the tested random-graph instance and region size.



Run log:

pytest -q tests/test\_random\_graph\_area.py → PASS (1 test; user re-run log)



4B.5 Tensor coherence (dense and tensor-train)



Path:

tests/test\_tensor\_coherence.py 



Primary implementation exercised:

toe/tensor\_coherence.py (via coherence\_dense, as\_tt, reconstruct, coherence\_tt, and feature flag TENSORLY\_AVAILABLE)



What this test validates:



Validates that the dense coherence functional computed by coherence\_dense is finite and strictly positive for a smooth 2D reference field and the tested grid spacing. 



When TensorLy is available, validates that tensor-train coherence coherence\_tt closely matches dense coherence coherence\_dense for the same field:



without a potential term, and



with a quartic potential term included in the coherence integrand. 



When TensorLy is available, validates that reconstruction error from tensor-train approximation is non-increasing as the requested TT rank increases across the tested rank list. 



What this test does not validate:



Does not validate that the coherence functional corresponds to any specific physical coherence observable; it validates only internal numeric consistency and TT-versus-dense agreement for the implemented definition.



Does not validate performance, memory scaling, or optimal TT rank selection beyond the monotone error check on a single smooth field.



Run log:

pytest -q tests/test\_tensor\_coherence.py → PASS (4 tests; user re-run log)



4B.6 Tensor entropy



Path:

tests/test\_tensor\_entropy.py 



Primary implementation exercised:

toe/tensor\_entropy.py (via tensor\_rank\_entropy, schmidt\_entropy\_by\_cuts) and toe/qca.py (via SplitStepQCA1D, apply\_qca\_steps)



What this test validates:



Validates that tensor\_rank\_entropy reports zero entropy for an explicit product state vector (single basis state populated) under the tested parameters. 



Evolves the product state under a QCA for a small number of steps and validates that tensor\_rank\_entropy becomes strictly positive after evolution under the tested QCA parameters. 



Validates that schmidt\_entropy\_by\_cuts returns an array of shape (N-1,) for an N-site state and returns all zeros for the product state. 



What this test does not validate:



Does not validate that tensor\_rank\_entropy equals the von Neumann entanglement entropy; it validates behavior of the implemented rank-based proxy.



Does not validate entanglement growth rates, scaling laws, or convergence of Schmidt computations beyond the tested small systems.



Run log:

pytest -q tests/test\_tensor\_entropy.py → PASS (2 tests; user re-run log)



4B.7 Tensor optional utilities



Path:

tests/test\_tensor\_optional.py 



Primary implementation exercised:

toe/tensor\_coherence.py (via coherence\_integral\_numpy, coherence\_integral\_tt)



What this test validates:



Computes a reference coherence integral using the NumPy dense path.



Computes a tensor-train based integral estimate using coherence\_integral\_tt with an explicit request to estimate approximation error.



Validates that the returned integral value is finite in all cases.



If the TT path reports ok=True and provides an approximation error estimate, validates that the approximation error is below a stated relative bound compared to the reference scale used in the test. 



What this test does not validate:



Does not validate that TT integration is always accurate; it validates only that it returns finite values and that, when it self-reports a valid approximation error, that error is bounded in the tested case.



Does not validate correctness when external tensor backends are absent; the test explicitly allows a fallback behavior where the dense value is returned.



Run log:

pytest -q tests/test\_tensor\_optional.py → PASS (1 test; user re-run log)



4B.8 LR velocity (QCA drift proxy sanity)



Path:

tests/test\_lr\_velocity.py 



Primary implementation exercised:

toe/qca.py (via SplitStepQCA1D, energy\_conservation\_proxy)



What this test validates:



Constructs a small QCA and a simple product initial state.



Runs energy\_conservation\_proxy for a small number of steps and validates that the returned drift value is below a strict tolerance (drift < 1e-12) in the tested configuration. 



What this test does not validate:



Does not validate a general Lieb–Robinson theorem or a universal LR velocity bound; it validates a numerical proxy behavior for the tested QCA and initial state.



Does not validate large-system behavior or long-time accumulation; it is a small-system sanity check.



Run log:

pytest -q tests/test\_lr\_velocity.py → PASS (1 test; user re-run log)



Priority 4C — Legacy, scaffolding, and meta-validation (run logs added)

4C.1 Phase 1 grammar locks and homogeneity gates



Path:

tests/test\_phase1\_grammar.py 



Primary implementation exercised:

This test file is self-contained and uses SymPy directly. It does not import a project equation module.



What this test validates:



Validates dimensional homogeneity of three Phase-1 target term structures under the test’s symbolic dimension model, requiring each target to match the scale L \* T^(-2):



kinetic-like term scale,



time-like term scale,



amplitude-gradient coherence term scale. 



Validates exact algebraic equivalence between a complex-form Hamiltonian density and a symplectic real (q, p) representation using explicit identities for |∂xϕ|^2 and ∂xρ. 



Validates a Phase 1 scope policy that excludes the phase-gradient coherence form λ f^2 (∂xθ)^2, by asserting an explicit policy flag remains false. 



What this test does not validate:



Does not validate numerical discretization, solver behavior, or simulation stability.



Does not validate that the dimension model used here equals the project-wide unit system; it validates consistency under this test’s monomial L and T scheme.



Does not validate any physical interpretation; it enforces algebraic and dimensional consistency plus a scope restriction.



Run log:

pytest -q tests/test\_phase1\_grammar.py → PASS (3 tests; user re-run log)



4C.2 Phase 1b calculus “shape” for ε-regularized coherence variation



Path:

tests/test\_phase1b\_shapes.py



Primary implementation exercised:

This test file is self-contained and uses SymPy directly. It does not import a project equation module.



What this test validates:



Defines an ε-regularized density ρ\_ε = ϕ ϕ\* + ε^2 and amplitude f\_ε = sqrt(ρ\_ε).



Defines a 1D coherence Lagrangian slice L\_c = λ (∂x f\_ε)^2.



Computes the Euler–Lagrange variation with respect to ϕ\* and asserts the exact symbolic form equals −λ (ϕ / f\_ε) ∂xx f\_ε under the ε-regularized definition.



Validates a Phase 1 scope policy that excludes the phase-gradient coherence form λ f^2 (∂xθ)^2, via an explicit policy flag.



What this test does not validate:



Does not validate multidimensional variational derivations; it is a 1D symbolic slice.



Does not validate numerical correctness, discretization, or boundary handling.



Does not validate physical interpretation; it locks the selected symbolic variation shape used by the project.



Run log:

pytest -q tests/test\_phase1b\_shapes.py → PASS (2 tests; user re-run log)



4C.3 Phase 7 fail-fast guards for structural prerequisites



Path:

tests/test\_phase7\_failfast.py



Primary implementation exercised:

equations/phase7\_failfast.py (guard and helper functions imported by the test)



What this test validates:



Validates that a complex-versus-symplectic consistency guard passes when ∂xϕ is constructed consistently from real derivatives.



Validates that a canonical bracket normalization guard passes for the tested normalization value.



Validates that a continuity prerequisite guard:



passes when current and continuity stencils match and the time-step condition satisfies the configured bound for the tested method, and



raises an assertion failure when a deliberately mismatched stencil is supplied.



Validates that an energy coercivity quadratic guard:



passes when curvature U''(ρ0) and gradient weight λ meet the positivity floors, and



raises an assertion failure when U''(ρ0) is negative or when λ is below the specified floor.



What this test does not validate:



Does not validate derivations of continuity or coercivity conditions; it validates guard logic and failure modes as implemented.



Does not validate solver accuracy or stability; it enforces prerequisite consistency checks.



Run log:

pytest -q tests/test\_phase7\_failfast.py → PASS (6 tests; user re-run log)



4C.4 Phase 8 no-claims tripwires and scope enforcement



Path:

tests/test\_phase8\_noclaims.py



Primary implementation exercised:

equations/phase8\_noclaims.py (scope structure and guard functions imported by the test)



What this test validates:



Validates that the default Phase 1 scope object has claim flags disabled.



Validates that the allowed coherence form set and advertised Noether current set match exactly what the Phase 1 scope is permitted to assert under the implementation.



Validates that the guard functions accept the default scope.



Validates that explicit “claim flags” or disallowed supported-form/current entries trigger assertion failures with explicit messages when Phase 1 attempts to claim:



relativistic covariance,



entropy–coherence duality,



alternative coherence densities,



extra Noether currents beyond those allowed in Phase 1.



What this test does not validate:



Does not validate whether disallowed claims are true or false; it enforces that Phase 1 does not assert them.



Does not validate later-phase expansions; it constrains Phase 1 scope policy only.



Does not validate numerical behavior; it is a policy and drift-prevention suite.



Run log:

pytest -q tests/test\_phase8\_noclaims.py → PASS (9 tests; user re-run log)



4C.5 Phase 9 validation protocol against frozen deliverables



Path:

tests/test\_phase9\_validation\_protocol.py 



Primary implementation exercised:

equations/phase9\_validation.py (via run\_all\_checks())



What this test validates:



Executes the Phase 9 validation protocol by calling run\_all\_checks() and asserts that every returned check reports ok == True.



If any check fails, the test fails with an aggregated message containing check names and messages. 



What this test does not validate:



Does not enumerate or validate the content of each sub-check; those are defined within equations/phase9\_validation.py.



Does not validate physical correctness; it validates that the protocol reports “all checks passed” as implemented.



Run log:

pytest -q tests/test\_phase9\_validation\_protocol.py → PASS (1 test; user re-run log)

## Direct answer



Yes: based on what you provided, the \*\*canonical-theory equation sources\*\* for the monograph are (a) the \*\*symbolic UCFF core module\*\* and (b) the \*\*equation inventory + state-of-the-theory documents\*\* that define the intended stack. The immediate risk is not “missing files,” but \*\*scope and sign-convention mismatches\*\* between what the inventory asserts and what `ucff\_core.py` actually encodes in its symbolic EOM residuals.   



---



\## Step-by-step: what your outputs imply about canonical membership



\### 1) Canonical “source of truth” files (must align with tests and monograph)



These are canonically binding because they define the equations you claim as definitive:



\* \*\*`field\_theory/equations/ucff\_core.py`\*\* (symbolic UCFF core: parameters, hydrodynamic Lagrangian density, first/second-order symbolic EOM residuals, and dispersion relations). 

\* \*\*`equation\_inventory\_finalv8.md`\*\* (declares the authoritative PDE forms and the full symbol glossary used for the monograph). 

\* \*\*`state\_of\_the\_theoryv8.md`\*\* (declares the validated “LSDA → CRFT → Extended CRFT → LCRD → geometry/turbulence diagnostics” stack and its governing equations). 



Everything else (phase modules, numerics, diagnostics) is “canonical” only insofar as it implements these declared equations and is locked by tests.



\### 2) Your PowerShell results show the \*shape\* of the canonical import surface



\* Many tests import from `equations.\*` (package-level API).

\* Many files reference `ucff\_core` across `field\_theory/equations/\*` and numerics steppers, meaning \*\*UCFF is a dependency root\*\* for the continuum layer and for multiple test families (Phase 11/13/14/31/46 etc.). (Your pasted `Select-String` results demonstrate this structurally.)



This supports the monograph claim that UCFF is the canonical continuum base, but it also means any mismatch in UCFF sign conventions propagates widely.



---



\## Critical scope statements: what the UCFF core does and does not do



\### A) `ucff\_core.py` does



1\. \*\*Defines a first-order hydrodynamic Lagrangian density\*\* containing:



\* canonical term `-ħ ρ θ\_t`

\* phase-gradient kinetic `-(ħ²/(2m)) ρ θ\_x²`

\* a “coherence-like” gradient density of the form `-lam (ρ\_x)²/(4ρ)`

\* a potential placeholder `U(ρ)` 



2\. \*\*Defines a first-order complex-field residual\*\* (symbolic EOM residual) of the form:



\* `R₁\[φ] = i φ\_t + (1/2) φ\_xx - g |φ|² φ + lam φ\_xxxx + beta φ\_xxxxxx`

&nbsp; and treats “coherence backreaction” `lambda\_coh` as \*\*not included here\*\*. 



3\. \*\*Defines a second-order-in-time residual\*\* that reproduces the baseline linear dispersion:



\* `φ\_tt + (1/4) φ\_xxxx - g ρ0 φ\_xx = 0`

&nbsp; which implies

\* `ω²(k) = (k²/2)² + (g ρ0) k²` in the baseline. 



4\. \*\*Defines dispersion relations directly at the level of ω²(k)\*\*, including lam and beta terms:



\* First-order: `ω² = (k²/2)² + (g ρ0) k² + lam k⁴`

\* Second-order: `ω² = (k²/2)² + (g ρ0) k² + lam k⁴ + beta k⁶` 



\### B) `ucff\_core.py` does not



1\. It does \*\*not\*\* include the coherence penalty backreaction term in the first-order φ EOM; it explicitly says `lambda\_coh` is added elsewhere (e.g., in phase22 via δC/δφ\*). 



2\. It does \*\*not\*\* implement lam/beta in the \*\*second-order EOM\*\* at the PDE level (it keeps the PDE minimal and only enforces the correct baseline dispersion and the `g ρ0 k²` piece). 



3\. It does \*\*not\*\* uniquely fix sign conventions for the PDE as written in your inventory (see mismatch below). The tests may be consistent internally, but the monograph-facing “authoritative PDE” must match whatever sign convention your canonical core actually enforces.



---



\## Key mismatch you should treat as “must reconcile in writing” (not a code change request)



Your \*\*Equation Inventory v8\*\* declares the authoritative CP–NLSE line as:



\* `i φ\_t = (1/2) φ\_xx − g |φ|² φ − lam φ\_xxxx − beta φ\_xxxxxx` 



But your \*\*UCFF core residual\*\* is defined as:



\* `i φ\_t + (1/2) φ\_xx − g |φ|² φ + lam φ\_xxxx + beta φ\_xxxxxx = 0` 



Algebraically, that residual implies:



\* `i φ\_t = −(1/2) φ\_xx + g |φ|² φ − lam φ\_xxxx − beta φ\_xxxxxx`



So, relative to the inventory’s “authoritative PDE,” \*\*the Laplacian term and the cubic term have opposite signs\*\* when you rewrite `R₁\[φ]=0` into “i φ\_t = …” form.



This is not a small stylistic difference; it changes whether the cubic term is focusing/defocusing under a given sign convention. If your tests pass, your code stack is self-consistent, but the monograph must not present a PDE with opposite signs from the one your canonical core actually encodes.



---



\## Alternative perspectives on how to treat this (without changing code yet)



1\. \*\*Documentation-first reconciliation (preferred at this stage):\*\*



&nbsp;  \* Treat `ucff\_core.py` as canonical, and rewrite the inventory PDE line to match the residual’s implied PDE exactly.



2\. \*\*Convention-lock approach:\*\*



&nbsp;  \* Add an explicit “sign convention” section in the monograph defining the PDE in “residual form” (R=0) rather than “i φ\_t = …” form, and always present the equation in the same residual convention used by tests.



3\. \*\*Two-branch naming clarity:\*\*



&nbsp;  \* If you truly intend both focusing and defocusing regimes, document them as separate parameterizations/conventions rather than letting them differ silently across documents.



---



\## Practical action plan



1\. For \*\*canonical membership auditing\*\*, treat these as authoritative sources to align:



&nbsp;  \* `field\_theory/equations/ucff\_core.py` 

&nbsp;  \* `equation\_inventory\_finalv8.md` 

&nbsp;  \* `state\_of\_the\_theoryv8.md` 



2\. For \*\*immediate, no-code-change cleanup in the monograph\*\*, do one of:



&nbsp;  \* Replace the CP–NLSE “authoritative single-line PDE” in the inventory with the PDE implied by `R₁\[φ]=0`, or

&nbsp;  \* Present the CP–NLSE in residual form to avoid sign-flip ambiguity.



3\. Next “inspection for belonging” pass (your requested directory order):



&nbsp;  \* Enumerate every `equations/\*.py` symbol that is \*\*imported by Phase 10/11/13/14/31 tests\*\* and map each to the exact equation lines in the inventory/state docs.

&nbsp;  \* Any equation in the monograph that is not mapped to a specific module+symbol is “non-canonical” by definition and should be removed or explicitly labeled as qualitative/diagnostic.



If you want, paste the \*\*full `Select-String` output including `Line` content\*\* (not just `Path`) for the `from equations.` results; that gives enough detail to produce an exact per-test → per-module dependency map without guessing.



\## Direct answer



Based on the manifests you posted, your “core simulator” surface is \*\*not\*\* `simulators/` (it is effectively empty); it is the package code under \*\*`fundamental\_theory/crft`\*\*, \*\*`fundamental\_theory/lcrd`\*\*, \*\*`fundamental\_theory/lsda`\*\*, plus the top-level \*\*`numerics/`\*\* and \*\*`field\_theory/\*`\*\* modules that tests import. The `numerics/` directory is small, coherent, and appears to be on \*\*validated paths\*\* (multiple `tests/test\_phase10\_\*\_numerics.py` and `tests/test\_phase11\_\*` import from it). Your “legacy / scratch / experiment” corpus is largely already quarantined under `archive/`, and it is being detected by your keyword scan (expected).



What I cannot do yet (with high confidence) is produce an explicit per-file “referenced-by-these-tests” table, because your `Select-String` output for Step 2A is missing the \*\*actual import lines\*\* (only Path + LineNumber are visible in your pasted output).



---



\## Step-by-step: grounded classification from what you already provided



\### 1) Core simulators (CRFT / LCRD / LSDA)



\*\*Observation:\*\*



\* `fundamental\_theory/simulators/` contains only `\_\_init\_\_.py`.

\* `field\_theory/simulators/` does not exist.

&nbsp; So “simulators” are not under `simulators/`; they are under the domain packages.



\*\*What is effectively serving as the simulator layer (by explicit file presence and your keyword scan hits):\*\*



\* `fundamental\_theory/crft/\*` (e.g., `cp\_nlse\_2d.py`, `phi\_chi\_coupled.py`, `rk4.py`, `invariants.py`, plus `crft/diagnostics/\*`)

\* `fundamental\_theory/lcrd/lcrd\_v3.py`

\* `fundamental\_theory/lsda/\*` (e.g., `dynamics.py`, `stepper.py`, `rk4.py`)

\* `field\_theory/cpu/\*`, `field\_theory/gpu/\*` (you have `field\_theory/cpu/numerics.py`, `field\_theory/gpu/numerics.py`, etc.)



\*\*Cross-check status (tests exist):\*\*



\* You have explicit test modules under `fundamental\_theory/crft/tests/\*` and `fundamental\_theory/lcrd/tests/\*` and `fundamental\_theory/tests/\*` for LSDA. That satisfies “each simulator referenced by at least one test” at the package level (pending a precise import graph).



\*\*Conclusion (current evidence):\*\*



\* `fundamental\_theory/simulators/` is \*\*scaffolding/unused\*\* (likely safe to archive or delete if nothing imports it).

\* The “core simulators” are \*\*package modules\*\*, not a `simulators/` directory.



---



\### 2) Numerics infrastructure (`numerics/`)



You have exactly:



\* `numerics/diagnostics.py`

\* `numerics/grid1d.py`

\* `numerics/phase16\_split\_step\_nd.py`

\* `numerics/stepper\_nls.py`

\* `numerics/stepper\_ucff.py`

\* `numerics/\_\_init\_\_.py`



\*\*Validated path evidence you posted:\*\*



\* Tests explicitly import from `numerics|field\_theory|fundamental\_theory` (your Step 2A output shows multiple `tests/test\_phase10\_\*\_numerics.py`, `tests/test\_phase11\_\*`, etc. are matched).

\* Your keyword scan shows dedicated tests around “acoustic metric” and “hydro metric” numerics (e.g., `test\_phase29\_acoustic\_metric\_numerics.py`, `test\_phase34\_hydro\_metric\_numeric.py`).



\*\*Conclusion (current evidence):\*\*



\* `numerics/` appears \*\*active and on validated paths\*\*.

\* `\_\_pycache\_\_/` is non-source (ignore/remove).

\* The \*content\* you pasted for `numerics\_filelist.txt` is not trustworthy as provenance (it contains narrative claims and LaTeX-like content rather than a file list). Treat it as \*\*documentation text\*\*, not an authoritative inventory source.



---



\### 3) Legacy / scratch / experiments



Your “possible legacy” keyword scan hits:



\* many scripts under `archive/` (expected)

\* `archive/lcrd\_legacy\_docs/...` (explicitly legacy)

\* various `field\_theory/examples/\*`

\* `field\_theory/cpu/\*`, `field\_theory/gpu/\*` (not legacy by location, but flagged by generic keywords like “prototype/experiment” matches—these need import-graph confirmation)



\*\*Conclusion (current evidence):\*\*



\* Anything under `archive/` is already segregated and can be labeled \*\*experimental/archived\*\* unless your import graph shows active imports from it (rare, but we will confirm).



---



\## Alternative perspectives (how to structure this cleanly)



\### Option A — Accept “package simulators” as canonical



Document that canonical simulators live in:



\* `fundamental\_theory/crft`, `fundamental\_theory/lcrd`, `fundamental\_theory/lsda`

&nbsp; and deprecate the `fundamental\_theory/simulators/` directory entirely.



\### Option B — Move toward a unified `simulators/` facade



Create a new canonical `simulators/` package that simply re-exports stable APIs from the packages above (thin wrappers), then make tests import only from that facade. This gives you a single import surface and makes “belonging” audits easier.



---



\## Practical next action plan (minimal additional output needed)



\### A) Re-run Step 2A but include the actual import lines (this is required for per-file mapping)



```powershell

Get-ChildItem -Recurse .\\tests -Filter \*.py |

&nbsp; Select-String -Pattern "from (simulators|numerics|field\_theory|fundamental\_theory)\\.|import (simulators|numerics|field\_theory|fundamental\_theory)\\." |

&nbsp; Select-Object Path, LineNumber, Line |

&nbsp; Format-Table -AutoSize -Wrap

```



Paste that output.



\### B) Produce a reverse-import map for \*non-test\* code importing numerics (find “old variants” risk)



```powershell

Get-ChildItem -Recurse . -Filter \*.py |

&nbsp; Where-Object { $\_.FullName -notmatch "\\\\\\.venv\\\\|\\\\archive\\\\" } |

&nbsp; Select-String -Pattern "from numerics\\.|import numerics\\.|from field\_theory\\.cpu\\.|from field\_theory\\.gpu\\." |

&nbsp; Select-Object Path, LineNumber, Line |

&nbsp; Format-Table -AutoSize -Wrap

```



Paste that output.



\### C) Provide the full file list `$all` as a file (best), instead of pasting 385 lines



```powershell

$all | Out-File -Encoding utf8 repo\_all\_py\_files.txt

$imports | Out-File -Encoding utf8 repo\_all\_import\_lines.txt

```



Upload:



\* `repo\_all\_py\_files.txt`

\* `repo\_all\_import\_lines.txt`



Once I have A (import lines) plus C (full lists), I will return:



1\. \*\*Simulator inventory with exact test linkage\*\* (per file)

2\. \*\*Numerics infrastructure audit\*\* (per file, “validated path” vs “untested use”)

3\. \*\*Legacy/orphan list\*\* (explicitly “never imported anywhere” vs “imported but untested”)



\## Direct answer



1\. \*\*“Core simulators / numerics for CRFT and LCRD” are not currently located in `fundamental\_theory/simulators/` or `field\_theory/simulators/`.\*\*



&nbsp;  \* `fundamental\_theory/simulators/` exists but contains only `\_\_init\_\_.py`【】.

&nbsp;  \* `field\_theory/simulators/` is missing (per your console output).

&nbsp;  \* The actual “simulator/integrator” implementations appear to live under:



&nbsp;    \* `fundamental\_theory/crft/…` (CRFT/CP–NLSE machinery)【】

&nbsp;    \* `fundamental\_theory/lcrd/lcrd\_v3.py` (LCRD core)【】

&nbsp;    \* root `numerics/…` (general steppers + grid + diagnostics)【】

&nbsp;    \* `field\_theory/cpu/\*` and `field\_theory/gpu/\*` (separate numerics stacks)【



2\. \*\*Cross-check “each simulator referenced by at least one test”:\*\*



&nbsp;  \* \*\*CRFT:\*\* tests exist in `fundamental\_theory/crft/tests/\*.py`【 (e.g., `crft\_c5\_multifield\_consistency.py`, `crft\_c6\_cp\_nlse\_2d\_dispersion.py`, etc.)\*\*

&nbsp;  \* \*\*LCRD:\*\* `fundamental\_theory/lcrd/tests/lcrd\_t1\_to\_t10.py` exists【

&nbsp;  \* \*\*Root numerics:\*\* files exist and are referenced by phase tests (your `tests/test\_phase10\_\*` and `test\_phase11\_\*` import numerics, per your grep). The repository inventory confirms the numerics modules exist (`stepper\_ucff.py`, `stepper\_nls.py`, etc.)【



3\. \*\*Numerics infrastructure “validated paths only / not old variants”:\*\*



&nbsp;  \* You have \*\*two numerics “families”\*\*:



&nbsp;    \* root `/numerics` (grid/steppers/diagnostics)【

&nbsp;    \* `field\_theory/cpu` and `field\_theory/gpu` (their own numerics modules)【

&nbsp;  \* Additionally, you have \*\*explicit legacy content in `archive/…`\*\*, including `archive/lcrd\_legacy\_docs/...` (legacy simulators/tests). Your grep already surfaced these as “legacy/old/prototype/scratch/experiment” candidates.



4\. \*\*Legacy / scratch / experiment scripts:\*\*



&nbsp;  \* Everything under `archive/` should remain \*\*archived\*\* by definition; the key action is to ensure \*\*nothing outside `archive/` is “dead code”\*\* (never imported by any non-archive module and never hit by tests).



---



\## Step-by-step reasoning (grounded in what you provided)



1\. Your listing shows no real simulator modules under `fundamental\_theory/simulators/` beyond `\_\_init\_\_.py`【, and `field\_theory/simulators/` doesn’t exist.

2\. The repository file list shows where the real simulator logic lives:



&nbsp;  \* CRFT core modules (`fundamental\_theory/crft/\*.py`) and diagnostics/tests【

&nbsp;  \* LCRD v3 implementation + test bundle【

&nbsp;  \* Root numerics modules exist (`numerics/\*.py`)【

&nbsp;  \* Field-theory CPU/GPU numerics exist as separate stacks【

3\. Therefore, the correct “cross-check” target is \*\*not\*\* the `simulators/` folders, but those actual modules + their associated tests in:



&nbsp;  \* `fundamental\_theory/crft/tests/\*`【

&nbsp;  \* `fundamental\_theory/lcrd/tests/\*`【

&nbsp;  \* root `tests/test\_phase10\_\*` and `tests/test\_phase11\_\*` (you already grepped these as importing `numerics.`)

&nbsp;  \* `field\_theory/tests/\*` for CPU/GPU parity (exists in repo)【



---



\## Alternative perspectives (two viable ways to “fix” the architecture)



\### Option A (minimal churn): document “simulators” as a \*concept\*, not a folder



\* Declare the canonical simulator modules as:



&nbsp; \* CRFT simulator core: `fundamental\_theory/crft/dynamics.py`, `cp\_nlse\_2d.py`, etc.【

&nbsp; \* LCRD simulator core: `fundamental\_theory/lcrd/lcrd\_v3.py`【

&nbsp; \* Root time-steppers: `numerics/stepper\_ucff.py`, `numerics/stepper\_nls.py`【

\* Advantage: no refactor risk.



\### Option B (architecture normalization): create real `simulators/` packages and re-export



\* Create:



&nbsp; \* `fundamental\_theory/simulators/crft.py` (imports/re-exports from `fundamental\_theory/crft/\*`)

&nbsp; \* `fundamental\_theory/simulators/lcrd.py` (wraps `lcrd\_v3`)

&nbsp; \* `field\_theory/simulators/` as a thin wrapper around `field\_theory/cpu` and `field\_theory/gpu`

\* Advantage: meets your stated directory contract (“simulators/ exists and is canonical”).



---



\## Practical action plan (commands + deliverables)



\### 1) Produce a \*\*ground-truth “used vs unused” report\*\* (outside `archive/`)



Run this PowerShell to find python files that are never imported by any \*\*non-archive\*\* module (best-effort static reachability):



```powershell

\# From repo root (ToE)

$py = Get-ChildItem -Recurse . -Filter \*.py |

&nbsp; Where-Object { $\_.FullName -notmatch "\\\\\\.venv\\\\|\\\\archive\\\\" }



\# Build a set of all imported module strings

$importLines = $py | Select-String -Pattern "^\\s\*(from\\s+(\[A-Za-z0-9\_\\.]+)\\s+import|import\\s+(\[A-Za-z0-9\_\\.]+))"



$mods = New-Object System.Collections.Generic.HashSet\[string]

foreach ($m in $importLines.Matches) {

&nbsp; if ($m.Groups\[2].Value) { $mods.Add($m.Groups\[2].Value) | Out-Null }

&nbsp; if ($m.Groups\[3].Value) { $mods.Add($m.Groups\[3].Value) | Out-Null }

}



\# Map file path -> possible module names (simple heuristic)

function Get-ModuleCandidates($path) {

&nbsp; $rel = Resolve-Path $path | ForEach-Object { $\_.Path }

&nbsp; $rel = $rel -replace \[regex]::Escape((Resolve-Path ".").Path + "\\"), ""

&nbsp; $rel = $rel -replace "\\\\", "."

&nbsp; $rel = $rel -replace "\\.py$", ""

&nbsp; @($rel)

}



$unused = @()

foreach ($f in $py) {

&nbsp; $cands = Get-ModuleCandidates $f.FullName

&nbsp; $hit = $false

&nbsp; foreach ($c in $cands) {

&nbsp;   if ($mods.Contains($c)) { $hit = $true; break }

&nbsp; }

&nbsp; if (-not $hit) { $unused += $f.FullName }

}



$unused | Sort-Object | Out-File -Encoding utf8 .\\unused\_py\_outside\_archive.txt

"wrote unused\_py\_outside\_archive.txt"

```



This will generate `unused\_py\_outside\_archive.txt` which you can then triage into:



\* \*\*keep (entry-point scripts)\*\*,

\* \*\*experimental-only\*\*,

\* \*\*delete\*\*.



\### 2) Enforce “validated numerics paths only”



Add a policy test that fails if anything imports legacy locations. For example, forbid imports from `archive.` and any legacy “lcrd\_legacy\_docs” module path. Minimal version:



```powershell

Get-ChildItem -Recurse . -Filter \*.py |

&nbsp; Where-Object { $\_.FullName -notmatch "\\\\\\.venv\\\\" } |

&nbsp; Select-String -Pattern "from\\s+archive\\.|import\\s+archive\\.|lcrd\_legacy\_docs" |

&nbsp; Select-Object Path, LineNumber, Line

```



\### 3) Make the “simulators/” contract explicit (pick A or B)



\* If you pick \*\*Option A\*\*, update `state\_of\_the\_theoryv8.md` to say:



&nbsp; \* “Simulator implementations live in `fundamental\_theory/crft`, `fundamental\_theory/lcrd`, root `numerics`, and `field\_theory/{cpu,gpu}`; `simulators/` is reserved for future consolidation.”

\* If you pick \*\*Option B\*\*, add wrapper modules and then update tests to import via `fundamental\_theory.simulators.\*` (but this is a refactor step and should be done with one commit + immediate pytest run).



---



\## Immediate “flag list” from what’s already visible



\* \*\*Structural mismatch to your task definition:\*\* `field\_theory/simulators` missing; `fundamental\_theory/simulators` empty【

\* \*\*Likely intentional “legacy”:\*\* `archive/lcrd\_legacy\_docs/...` and other archive scripts (already detected by your grep).

\* \*\*Multiple numerics stacks:\*\* root `numerics` plus `field\_theory/cpu` and `field\_theory/gpu` numerics【 — acceptable, but only if you explicitly define which one is canonical for which claims/tests.



---



If you upload `unused\_py\_outside\_archive.txt` after you generate it, I can classify each entry as \*\*archive / delete / experimental-only\*\* and identify any “should be tested but currently isn’t” modules.



\## Direct answer



\* \*\*“simulators/” (core simulators / integrators):\*\* In your current tree, there is \*\*no real simulator package\*\* under either `fundamental\_theory/simulators/` (only `\_\_init\_\_.py`) and \*\*`field\_theory/simulators/` is missing\*\*. Functionally, your “simulators” live in \*\*`fundamental\_theory/crft/\*`, `fundamental\_theory/lcrd/\*`, `fundamental\_theory/lsda/\*`, plus `numerics/\*` and `field\_theory/cpu|gpu/\*`\*\*.

\* \*\*Numerics infrastructure:\*\* Your \*\*active numerics\*\* are clearly `numerics/grid1d.py`, `numerics/stepper\_nls.py`, `numerics/stepper\_ucff.py`, `numerics/phase16\_split\_step\_nd.py`, `numerics/diagnostics.py`, and these are \*\*referenced by tests\*\* (notably the phase10/phase11 numerics tests you grepped).

\* \*\*Legacy variants:\*\* Your “legacy / alternate integrators” hits are overwhelmingly in `archive/…` (including `archive/lcrd\_legacy\_docs/...`). Your grep for imports from `archive` returned nothing, so \*\*validated code paths are not importing legacy archive code\*\*.

\* \*\*Unused `.py` flagging:\*\* Your `unused\_py\_outside\_archive.txt` list is useful as a \*triage queue\*, but its heuristic (“module string appears in an import line somewhere”) will produce \*\*false positives\*\* (e.g., pytest discovery, script entrypoints, dynamic imports, `python -m package.module`, and modules only referenced by tests in other ways). Still, it’s a good starting list for “experimental / CLI / tooling / examples” classification. 



---



\## Step-by-step reasoning



\### 1) Core simulators / numerics for CRFT and LCRD



\* Your PowerShell listing shows:



&nbsp; \* `fundamental\_theory/simulators/` exists but contains only `\_\_init\_\_.py`.

&nbsp; \* `field\_theory/simulators/` is missing.

\* However, your repo clearly contains simulation engines in:



&nbsp; \* `fundamental\_theory/crft/` (grid, operators, dynamics, state, rk4, diagnostics)

&nbsp; \* `fundamental\_theory/lcrd/lcrd\_v3.py`

&nbsp; \* `fundamental\_theory/lsda/\*` (backend, grid, eom, stepper, etc.)

&nbsp; \* `numerics/\*` (NLS + UCFF steppers, grids, diagnostics)

&nbsp; \* `field\_theory/cpu/\*` and `field\_theory/gpu/\*`

\* Conclusion: \*\*your “simulators” are distributed\*\*, not centralized in a `simulators/` namespace.



\### 2) Cross-check: each simulator referenced by at least one test in `tests/`



\* You confirmed direct test imports from `numerics.\*` in phase10/11 numerics tests.

\* You also have `fundamental\_theory/crft/tests/\*.py` and `fundamental\_theory/lcrd/tests/lcrd\_t1\_to\_t10.py`, which act as \*\*self-contained test modules\*\* (often run via `python -m ...`).

\* This satisfies “referenced by tests,” but \*\*not under a single `tests/` root\*\*—you have multiple test roots: repo `/tests`, plus `fundamental\_theory/crft/tests`, plus `fundamental\_theory/lcrd/tests`, plus `field\_theory/tests`.



\### 3) Numerics infrastructure (FFT wrappers, grid management, time steppers)



\* In practice, your numerics infrastructure is split across:



&nbsp; \* `numerics/\*` (generic grids/steppers/diagnostics)

&nbsp; \* `fundamental\_theory/crft/\*` (CRFT-specific grid/operators/dynamics/diagnostics)

&nbsp; \* `field\_theory/cpu|gpu/numerics.py` (field-theory specific)

\* Your greps show tests import the canonical `numerics.\*` modules directly (good: “validated path” exists).

\* Risk to check next: \*\*duplicate implementations\*\* (e.g., `field\_theory/cpu/numerics.py` vs `numerics/stepper\_ucff.py` vs `fundamental\_theory/crft/dynamics.py`) where one silently drifts.



\### 4) Legacy / scratch / experiment scripts



\* Your grep for `archive` imports returned nothing, so \*\*archive is not on active import paths\*\*.

\* The “possible legacy integrator” grep shows many hits in `archive/\*` (expected) and also many hits in \*\*examples and tooling\*\* (e.g., `field\_theory/examples/\*`, `mei/\*`).

\* Your `unused\_py\_outside\_archive.txt` contains many candidates to classify as:



&nbsp; \* \*\*core-but-unimported\*\* (entrypoints, pytest-discovered tests)

&nbsp; \* \*\*examples\*\* (safe “experimental only”)

&nbsp; \* \*\*tooling\*\* (MEI checks/build scripts)

&nbsp; \* \*\*true dead code\*\* (likely safe to archive/delete after confirmation) 



---



\## Alternative perspectives / approaches



\### A) Keep the current distributed structure, but formalize it



\* Treat `numerics/` as the canonical low-level layer.

\* Treat `fundamental\_theory/crft|lcrd|lsda` as domain layers.

\* Treat `field\_theory/cpu|gpu` as implementation layers.

\* Add a single documentation map: “which PDE/stepper lives where” + “which test validates it.”



\### B) Create a real `simulators/` facade package (recommended for long-term hygiene)



\* Add `field\_theory/simulators/` and expand `fundamental\_theory/simulators/` to re-export only \*\*validated\*\* steppers:



&nbsp; \* `simulators/crft.py` → wraps `fundamental\_theory.crft.dynamics` (or whichever is canonical)

&nbsp; \* `simulators/lcrd.py` → wraps `fundamental\_theory.lcrd.lcrd\_v3`

&nbsp; \* `simulators/ucff.py` → wraps `numerics.stepper\_ucff`

&nbsp; \* `simulators/nls.py` → wraps `numerics.stepper\_nls`

\* Then require: each facade module has at least one test under `/tests` that imports it (so you stop “testing internal modules directly”).



\### C) Split “tests” into a single root (optional, but reduces ambiguity)



\* Consolidate `fundamental\_theory/\*/tests` into `/tests/fundamental\_theory/...` so `pytest` is the single collector.

\* This makes “referenced by at least one test in tests/” literally true and easy to enforce.



---



\## Practical action plan (do this next)



\### 1) Establish what “simulator” means in \*your\* repo (without moving code yet)



Add a policy (in `state\_of\_the\_theoryv8.md` or a new `docs/architecture.md`):



\* \*\*Simulator = an evolution driver / integrator callable\*\* (step function or evolve function) used to advance state.

\* \*\*Numerics = grids/operators/FFT wrappers/steppers used by simulators.\*\*

\* \*\*Examples = not imported by tests; may be executed manually.\*\*



\### 2) Build a \*reliable\* reachability check (better than the current heuristic)



Your current “unused” detector only checks whether a module name ever appears in an import statement; it will mislabel entrypoints and pytest-collected tests. Keep it, but add a second pass:



\* Run these two commands and save outputs:



&nbsp; \* `pytest -q --collect-only > pytest\_collect.txt`

&nbsp; \* `python -c "import pkgutil, toe; print(\[m.name for m in pkgutil.walk\_packages(toe.\_\_path\_\_, toe.\_\_name\_\_+'.')])" > toe\_pkgutil.txt`



Then you can classify “unused” into:



\* collected-by-pytest

\* reachable-by-package-walk

\* truly unreferenced



\### 3) Create the missing `field\_theory/simulators/` and upgrade `fundamental\_theory/simulators/`



Do \*\*not\*\* move implementations yet—just add facades and tests:



\* `field\_theory/simulators/\_\_init\_\_.py`

\* `field\_theory/simulators/nls.py` (wrap CPU/GPU as appropriate)

\* `field\_theory/simulators/ucff.py`

\* `fundamental\_theory/simulators/crft.py`

\* `fundamental\_theory/simulators/lcrd.py`



Add minimal tests:



\* `/tests/test\_simulators\_facade\_imports.py` that imports each facade and asserts expected call signatures exist.



\### 4) Classify “legacy / scratch / experiment”



Start with these buckets (based on what’s clearly in your tree/list):



\* \*\*Archive-only (leave in archive):\*\* everything under `archive/` (already isolated).

\* \*\*Examples (experimental only):\*\* `field\_theory/examples/\*` and `examples/\*`.

\* \*\*Tooling (keep, but not “theory code”):\*\* `mei/\*`, `common/plots/\*`, `common/utils/\*`.

\* \*\*Extraction scripts (keep, but mark as CLI utilities):\*\* `fundamental\_theory/tests/extract\_\*.py`.



Your `unused\_py\_outside\_archive.txt` is the correct queue to work through for this labeling. 



