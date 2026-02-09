=====================================================================

LOCK\_SECOND\_ORDER\_NUMERICS.md

=====================================================================

SCOPE AND PURPOSE



This lock defines the operational (numerics) UCFF/UEFM evolution equation as implemented for simulation in 1D periodic geometry, together with the ω(k) linear dispersion statement enforced by the numerical tests.



In this numerics context, “second-order” refers to inclusion of higher-order spatial dispersion terms (4th- and 6th-order spatial derivatives). It does not refer to a second-order-in-time (φ\_tt) formulation.



This lock is operational. It is not the canonical time-domain (φ\_tt) lock.



Canonical second-order time-domain statements (residual form with φ\_tt and ω²(k) dispersion) are defined separately in:



LOCK\_SECOND\_ORDER\_TIME\_DOMAIN.md



This lock governs:



the first-order-in-time PDE that is actually stepped by the numerical integrators,



the linear dispersion in ω(k) form used by the numerical evolution,



the validated operational limiting case lam = beta = 0 (reduction to standard NLS),



the validated stability / behavior constraints enforced by executable tests.



=====================================================================

AUTHORITATIVE FILES



Implementation module (operational equation and integrators):



equations/phase13\_second\_order\_numerics.py



Primary validation tests (operational constraints):



tests/test\_phase13\_second\_order\_numerics.py



tests/test\_phase13\_second\_order\_cn\_vs\_splitstep.py



tests/test\_phase13\_second\_order\_mi.py



=====================================================================

FIELD, DOMAIN, AND VARIABLES



φ(x,t) — complex scalar field



Domain:



1D periodic domain of length L



x is the spatial coordinate on \[0, L) with periodic boundary conditions



t is physical time used in numerical evolution



Density:



ρ(x,t) = |φ(x,t)|²



Fourier wavenumbers:



k are the discrete Fourier wavenumbers associated with the periodic grid



=====================================================================

PARAMETERS (OPERATIONAL NUMERICS LAYER)



g — cubic nonlinearity coefficient (can be positive or negative)



lam — fourth-order dispersion coefficient



beta — sixth-order dispersion coefficient



All parameters are real-valued.



No assumptions about sign are imposed globally. Specific sign choices are enforced by specific behavioral tests where required.



=====================================================================

LOCKED OPERATIONAL EVOLUTION EQUATION (FIRST-ORDER-IN-TIME)



The operational numerics equation implemented by equations/phase13\_second\_order\_numerics.py is:



i φ\_t = - (1/2) φ\_xx + lam φ\_xxxx + beta φ\_xxxxxx + g |φ|² φ



This equation is the equation that the numerical integrators step forward in time.



This is not the canonical time-domain second-order (φ\_tt) equation. This is an operational first-order-in-time evolution used for simulation and validated by test constraints listed in this lock.



=====================================================================

LOCKED LINEAR DISPERSION (ω FORM, NOT ω² FORM)



For the linear regime with g = 0 and plane-wave solutions of the form:



φ(x,t) = A exp(i (k x - ω t))



the operational dispersion relation locked by the numerical tests is:



ω(k) = 0.5 k² + lam k⁴ + beta k⁶



This lock uses ω(k) form because the numerical tests estimate ω directly from time series and compare to this analytic expression.



This ω(k) statement is operational and belongs to this numerics lock. Canonical dispersion statements in ω²(k) form belong to LOCK\_SECOND\_ORDER\_TIME\_DOMAIN.md.



=====================================================================

LOCKED LIMITING CASE (REDUCTION TO STANDARD NLS AT lam = beta = 0)



When lam = 0 and beta = 0, the operational numerics equation reduces to the standard nonlinear Schrödinger equation (NLS):



i φ\_t = - (1/2) φ\_xx + g |φ|² φ



In the defocusing case (g > 0), the dark-soliton healing-length setting used for validation is:



Initial condition (profile form):



φ(x,0) = sqrt(rho0) \* tanh( sqrt(g rho0) \* (x - x0) )



The corresponding theoretical healing length is:



ξ\_theory = 1 / sqrt(g rho0)



The operational test suite enforces that, after evolution under the operational numerics integrator at lam = beta = 0, the numerically estimated healing length ξ\_num matches ξ\_theory to within 10%.



Precision note (estimator definition):



In this validation, ξ\_num is computed from the final-time profile using a local-slope estimator near the soliton center (not a global tanh-parameter fit).



=====================================================================

OPERATIONAL STABILITY / BEHAVIOR CONSTRAINTS ENFORCED BY TESTS



The following constraints are enforced by the operational tests:



(1) Linear dispersion agreement (frequency estimation)



Under plane-wave evolution with g = 0, the numerically estimated ω must match:



ω(k) = 0.5 k² + lam k⁴ + beta k⁶



within relative error < 1e-2.



(2) Mass (L² norm) drift as a stability proxy



Over a moderate evolution window, the relative drift in mass:



M = ∫ |φ|² dx



must remain below 5e-2 under the operational split-step integrator.



(3) Split-step vs Crank–Nicolson agreement in the linear regime



With g = 0 and a plane-wave initial condition (linear regime), the final states produced by:



split\_step\_second\_order\_ucff



crank\_nicolson\_second\_order\_ucff



must agree in relative L2 norm to within 1e-2 at the tested resolution and timestep.



Precision note (Crank–Nicolson scope):



The Crank–Nicolson integrator advances only the linear operator. It ignores the nonlinear term by design, and the validation tests call it with g = 0.0 accordingly.



(4) Modulational-instability (MI) qualitative separation with beta > 0



With beta > 0 and a weakly modulated plane wave:



focusing case (g < 0) must show strong growth (growth factor > 5.0),



defocusing case (g > 0) must remain comparatively stable (growth factor < 3.0).



This enforces the operational sign convention for “focusing vs defocusing” behavior in the implemented numerics equation.



=====================================================================

EXCLUSIONS (NOT PART OF THIS LOCK)



The following are explicitly excluded from this operational numerics lock:



Canonical second-order time-domain equation objects (φ\_tt residual form) and ω²(k) canonical dispersion statements.



These are defined in:



LOCK\_SECOND\_ORDER\_TIME\_DOMAIN.md



Any claims of derivation, variational origin, or coefficient-level proof of the operational PDE beyond what is enforced by the numerical tests listed here.



=====================================================================

EVIDENCE (TEST RESULTS)



The operational numerics lock is supported by the following passing tests:



python -m pytest -q tests/test\_phase13\_second\_order\_numerics.py



... \[100%]



python -m pytest -q tests/test\_phase13\_second\_order\_cn\_vs\_splitstep.py



. \[100%]



python -m pytest -q tests/test\_phase13\_second\_order\_mi.py



. \[100%]



=====================================================================

LOCKED OUTPUT REQUIREMENTS FOR DOCUMENTATION



When documenting the operational numerics layer in equation inventory or monograph text:



The operational numerics PDE must be written exactly as:



i φ\_t = - (1/2) φ\_xx + lam φ\_xxxx + beta φ\_xxxxxx + g |φ|² φ



The linear dispersion must be written in ω(k) form exactly as:



ω(k) = 0.5 k² + lam k⁴ + beta k⁶



The lam = beta = 0 limiting case must be stated explicitly as reduction to NLS, and the healing-length consistency constraint must be described only as an operational validation (not a canonical derivation claim). The healing-length estimator used here is a local-slope estimator near the soliton center.



Any statement of focusing/defocusing behavior must match the operational MI convention enforced by the tests:



focusing: g < 0 (unstable growth),



defocusing: g > 0 (stable or weak growth),



with beta > 0 in the validated MI separation test.



Crank–Nicolson references must not imply nonlinear evolution. In this operational suite, Crank–Nicolson is used as a linear-operator integrator and is validated under g = 0.



Canonical time-domain φ\_tt statements and ω²(k) canonical dispersion statements must be documented only under the canonical lock and must not be conflated with this operational lock.



=====================================================================

END LOCK\_SECOND\_ORDER\_NUMERICS.md

