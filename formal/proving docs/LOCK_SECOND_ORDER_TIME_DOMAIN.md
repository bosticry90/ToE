=====================================================================

LOCK\_SECOND\_ORDER\_TIME\_DOMAIN.md

=====================================================================

SCOPE AND PURPOSE



This lock defines the canonical second-order-in-time (time-domain) UCFF/UEFM equation family, the associated ω²(k) dispersion objects used across the symbolic framework, and the evidence bundle of passing tests that constrain the canonical presentation.



This lock is canonical. It is not an implementation lock. Numerical realizations (first-order-in-time split-step / Crank–Nicolson evolutions, ω(k) branch choices, and numerical phenomenology tests) are excluded from this document and belong in LOCK\_SECOND\_ORDER\_NUMERICS.md.



=====================================================================

CANONICAL STATEMENT



The canonical second-order time-domain layer is represented in the repository as a φ\_tt-based residual-form equation and ω²(k) dispersion objects.



The canonical lock is a layered claim:



The codebase contains a canonical time-domain second-order residual (φ\_tt present) with a corresponding ω²(k) dispersion statement in the Phase-13 time-domain module, and a structural test asserts the required ingredients are present.



The broader symbolic framework contains proof-style and equality-style validators showing:



Euler–Lagrange residual equality in Phase 2,



exact dispersion identity in Phase 2,



EOM-to-ω² dispersion round-trip (baseline regime) in UCFF core,



ω²(k) polynomial structure in UCFF core (first- and second-order),



hydrodynamic reformulation structural consistency and ω²(k) polynomial structure up to k⁶ in Phase 21.



Together these establish that “residual-form canon + ω²(k) dispersion canon” is the consistent theoretical standard in the repository, and that second-order extensions are structurally constrained across multiple independent modules.



=====================================================================

PRIMARY CANONICAL DEFINITION (PHASE 13 TIME-DOMAIN MODULE)



Canonical definition module:



equations/phase13\_ucff\_second\_order.py



Canonical residual-form equation object:



second\_order\_eom\_phi()



Canonical dispersion object:



second\_order\_dispersion\_from\_eom()



Canonical natural-units dispersion object:



second\_order\_dispersion\_natural\_units\_from\_eom()



Canonical symbol inventory helper:



symbol\_names\_phase13\_second\_order()



This module encodes the Phase-13 time-domain target equation residual (with φ\_tt explicitly present) and defines ω²(k) dispersion at the object level for use in symbolic documentation and lock statements.

The dispersion helpers in this module return explicit analytic ω²(k) Equality objects associated with the canonical residual and the stated plane-wave convention. They are not produced by an automated symbolic reduction of the residual inside the code, and the module does not attempt a full variational derivation of the residual from the Lagrangian density.



=====================================================================

PRIMARY CONSTRAINT TEST (PHASE 13 TIME-DOMAIN)



Primary constraint test:



tests/test\_phase13\_ucff\_second\_order.py



What this test enforces (structural constraints):



A) Residual structure constraints

The second-order residual returned by second\_order\_eom\_phi():



is a SymPy expression,



depends on x and t as free symbols,



contains ∂t² φ (phi\_tt),



contains ∂x² φ (phi\_xx),



contains ∂x⁴ φ (phi\_xxxx),



contains ∂x⁶ φ (phi\_xxxxxx),



contains the nonlinearity g |φ|² φ in the explicit density form

g \* (conjugate(phi) \* phi) \* phi.



B) Dispersion object constraints (ω² form)

The dispersion returned by second\_order\_dispersion\_from\_eom():



is a SymPy Equality,



has no x or t dependence,



its RHS contains k², k⁴, k⁶ as explicit symbolic subexpressions,



its RHS contains lam and beta.



C) Natural-units dispersion constraints

The natural-units dispersion returned by second\_order\_dispersion\_natural\_units\_from\_eom():



is a SymPy Equality,



removes explicit hbar and m from the RHS,



retains k², k⁴, k⁶ and retains lam and beta.



D) Symbol inventory constraints

symbol\_names\_phase13\_second\_order() includes:

x, t, hbar, m, c, lam, beta, g, rho0, phi, k, omega.



This test is a “no-drift” guard ensuring the canonical time-domain equation object retains the required derivative orders and that the dispersion is presented in ω²(k) form with the required polynomial structure.



=====================================================================

ASSOCIATED VALIDATORS (NON-PHASE13 NAMING)



These validators do not redefine the Phase-13 time-domain equation object. They provide independent confirmation that:



residual-form Euler–Lagrange equations are treated as canonical truth objects in the codebase,



ω²(k) dispersion objects are treated as canonical truth objects in the codebase,



second-order extensions are consistently represented as ω²(k) polynomials containing k²/k⁴/k⁶ with the expected parameter dependencies,



“proof-style” EOM → ω²(k) derivations exist in the repository (in baseline regimes), establishing the repository’s meaning of “equation implies dispersion.”



These are listed as associated evidence because they constrain canonical presentation standards and continuity expectations.



(1) Phase 2 exact dispersion identity (equality-style)



Validator:



tests/test\_phase2\_dispersion.py



Constraint:



simplify(linearized\_dispersion\_true()) == 0



Meaning:



The Phase-2 “true linearization” dispersion identity is asserted as an exact symbolic equality.



This establishes that dispersion verification in this codebase can be an exact equality claim, not only a structural claim.



(2) Phase 2 Euler–Lagrange residual equality (equality-style)



Validator:



tests/test\_phase2\_el\_residual.py



Constraint:



simplify(expand(R\_actual - R\_target\_scaled)) == 0



Meaning:



A Phase-2 Euler–Lagrange residual is asserted to match a scaled target residual exactly.



This establishes residual-form equality as a canonical verification mode.



(3) UCFF core dispersion structure (structural ω² form, first and second order)



Validator:



tests/test\_ucff\_core\_symbolic.py



Constraints (structural):



First-order ω² structure:



ω² contains k² and k⁴ and depends on g, rho0, lam.



Second-order ω² structure:



ω² contains k², k⁴, k⁶ and depends on g, rho0, lam, beta.



Meaning:



UCFF core dispersions are treated canonically at the ω²(k) level.



Second-order canonical structure includes an explicit k⁶ term at the dispersion level.



(4) UCFF core EOM → ω² dispersion round-trip (proof-style, baseline regime)



Validator:



tests/test\_ucff\_core\_roundtrip.py



Constraints (proof-style in baseline linear regime):



First-order baseline round-trip:



Reduce the EOM residual with a plane wave ansatz,



Solve for ω,



Square to ω²,



Compare to ucff\_dispersion\_first\_order in the baseline regime:

g = 0, lambda\_coh = 0, lam = 0, beta = 0,



Assert exact equality (diff == 0).



Second-order baseline round-trip:



Same steps for ucff\_second\_order\_eom and ucff\_dispersion\_second\_order,



Same baseline regime substitution,



Assert exact equality (diff == 0).



Meaning:



The repository contains an explicit “equation implies dispersion” proof pattern.



The baseline regime is locked exactly. These round-trip tests lock exact equality only in the λ = β = 0 baseline regime and do not require equality of λ- and β-dependent pieces between EOM-derived ω²(k) and the UCFF-core Bogoliubov form.



(5) Phase 21 hydrodynamic reformulation and ω² dispersion structure (structural)



Validator:



tests/test\_phase21\_hydrodynamics.py



Module dependencies:



equations/phase21\_hydrodynamics.py



equations/phase9\_freeze.py



Constraints (structural):



Hydrodynamic system structure:



Continuity contains ∂t rho and dependence on ∂x theta,



Euler-like equation contains ∂t theta and contains g rho,



Second-order hydro carries spatial derivatives up to at least 6th order.



Hydrodynamic ω² dispersion structure:



First-order hydro ω² contains k² and k⁴ and depends on g, rho0, lam.



Second-order hydro ω² contains k², k⁴, k⁶ and depends on g, rho0, lam, beta.



Meaning:



Independent hydrodynamic reformulation preserves the canonical “ω²(k) polynomial” presentation standard up to k⁶.



This provides additional cross-module structural confirmation of the second-order ω²(k) polynomial requirement.

These Phase-21 tests are deliberately structural and do not re-derive coefficients. In particular, β is introduced locally in the test file for structural k⁶ checks, and the tests only assert ingredient presence and k-power structure.



=====================================================================

EXCLUSIONS (NOT PART OF THIS LOCK)



The following are explicitly excluded from the canonical time-domain lock because they define or test operational numerical realization (ω(k) form, specific integrators, numerical phenomenology):



equations/phase13\_second\_order\_numerics.py



tests/test\_phase13\_second\_order\_numerics.py



tests/test\_phase13\_second\_order\_cn\_vs\_splitstep.py



tests/test\_phase13\_second\_order\_mi.py



tests/test\_phase13\_second\_order\_dispersive\_shock.py



These belong to LOCK\_SECOND\_ORDER\_NUMERICS.md.



=====================================================================

EVIDENCE (TEST RESULTS)



All tests listed below were executed and reported passing:



Phase-13 canonical time-domain structural guard:



python -m pytest -q tests/test\_phase13\_ucff\_second\_order.py

..... \[100%]



Associated validators (executed individually):



python -m pytest -q tests/test\_phase2\_dispersion.py

. \[100%]



python -m pytest -q tests/test\_phase2\_el\_residual.py

. \[100%]



python -m pytest -q tests/test\_ucff\_core\_symbolic.py

... \[100%]



python -m pytest -q tests/test\_ucff\_core\_roundtrip.py

.. \[100%]



python -m pytest -q tests/test\_phase21\_hydrodynamics.py

.... \[100%]



Associated validators (executed as one bundle):



python -m pytest -q

tests/test\_phase2\_dispersion.py

tests/test\_phase2\_el\_residual.py

tests/test\_ucff\_core\_symbolic.py

tests/test\_ucff\_core\_roundtrip.py

tests/test\_phase21\_hydrodynamics.py

........... \[100%]



=====================================================================

LOCKED OUTPUT REQUIREMENTS FOR DOCUMENTATION



When documenting the canonical second-order time-domain layer in equation inventory or monograph text:



The canonical time-domain second-order equation must be presented as a residual-form equation with φ\_tt present.



Dispersion must be presented in ω²(k) form, not ω(k) form, for canonical statements.



Statements of “proof” must distinguish:



equality-style proofs (Phase 2),



proof-style EOM→ω² round-trips in baseline regimes (UCFF core),



structural no-drift guards (Phase 13 and Phase 21).



Numerical implementations, ω(k) branch choices, and integrator-specific claims must be documented only under LOCK\_SECOND\_ORDER\_NUMERICS.md.



=====================================================================

END LOCK\_SECOND\_ORDER\_TIME\_DOMAIN.md



