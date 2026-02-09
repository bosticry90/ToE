============================================================



LOCK: LCRD v3 ROTOR–CURVATURE SYSTEM



============================================================



Status



This document locks the LCRD v3 rotor–curvature system as implemented and validated in the numerical layer. The lock applies to the governing equations, the first-order time formulation, the numerical operators, and the specific properties explicitly enforced by the test suite.



This lock does not assert physical completeness, optimality, or universal applicability beyond the conditions directly tested.



System Overview



The LCRD v3 system evolves a set of one-dimensional fields representing a rotor–curvature closure of CRFT hydrodynamic dynamics. The system is implemented as a closed, first-order-in-time partial differential equation system suitable for explicit time integration.



The system is defined on a one-dimensional periodic spatial domain and uses spectral differentiation throughout.



Fields and State Variables



The LCRD v3 system evolves the following real-valued fields:



ρ(x, t)

Mass or density-like scalar field.



u(x, t)

Velocity-like scalar field.



R(x, t)

Rotor field encoding local rotational structure.



K(x, t)

Curvature field encoding higher-order spatial structure.



The state at time t is:



state(t) = (ρ(x, t), u(x, t), R(x, t), K(x, t))



Spatial Domain and Operators



The system is defined on a one-dimensional periodic domain of length L, discretized on N grid points.



All spatial derivatives are computed spectrally using FFTs with standard Fourier multipliers:



First derivative: D1 → (i k)

Second derivative: D2 → −k²



Only first- and second-order spatial derivatives are used in the LCRD v3 governing equations. No higher-order spatial derivatives appear in the implementation.



No finite-difference operators are used.



Parameters



The parameter set for the LCRD v3 system is defined by:



rho0

Uniform background density used for initialization and test construction. This parameter does not explicitly appear in the governing equations.



g\_eff

Effective acoustic coupling inherited from CRFT hydrodynamics.



nu\_eff

Effective viscosity acting on velocity gradients.



c1

Rotor stiffness coefficient multiplying ∂x R in the velocity equation.



c2

Curvature stiffness coefficient multiplying ∂xx K in the velocity equation.



alpha\_R

Rotor relaxation rate.



alpha\_K

Curvature relaxation rate.



b\_R

Coupling coefficient driving R from |∂x u|.



b\_K

Coupling coefficient driving K from ∂x R.



d\_R

Coupling coefficient driving R from ∂x K.



Additional numerical parameters (time step, grid size, integration duration) are external and are not part of the model definition.



Governing Equations (Authoritative Form)



The LCRD v3 system is defined by the following coupled partial differential equations.



Density evolution:



∂t ρ = −∂x (ρ u)



Velocity evolution:



∂t u

= −u ∂x u

&nbsp; − g\_eff ∂x ρ

&nbsp; + c1 ∂x R

&nbsp; + c2 ∂xx K

&nbsp; + nu\_eff ∂xx u



Rotor evolution:



∂t R

= −alpha\_R R

&nbsp; + b\_R |∂x u|

&nbsp; + d\_R ∂x K



Curvature evolution:



∂t K

= −alpha\_K K

&nbsp; + b\_K ∂x R



These equations define the authoritative mathematical structure of the LCRD v3 rotor–curvature system.



First-Order Time Formulation



All fields are evolved as a first-order-in-time system. No second-order-in-time equations are present. The system is therefore directly compatible with standard explicit ODE integrators.



Numerical Implementation



The system is implemented in lcrd\_v3.py using:



• Spectral spatial differentiation on a periodic grid  

• Explicit fourth-order Runge–Kutta (RK4) time stepping  

• Periodic boundary conditions  

• Deterministic floating-point arithmetic  



The implementation is algebraically consistent with the governing equations above.



Validated Properties (Locked Claims)



The following properties are explicitly validated by the test suite lcrd\_t1\_to\_t10.py and are therefore locked.



Structural Correctness



All governing equations are implemented consistently with their mathematical definitions, including nonlinear advection, rotor–curvature coupling terms, and dissipative operators.



CRFT Reduction Consistency



When rotor and curvature fields are constrained to zero and their couplings disabled, the system reduces exactly to the CRFT hydrodynamic equations without spurious source terms.



Rotor Isolation Behavior



With velocity and curvature couplings disabled, the rotor field decays exponentially according to its relaxation rate.



Rotor Energy Conservation (Isolated, Zero-Coupling Limit)



When all relaxation and coupling terms are disabled, and the rotor–curvature subsystem is fully isolated, the rotor–curvature energy functional remains conserved up to numerical drift. This conservation does not hold for the general coupled LCRD dynamics.



Deterministic Reproducibility



Repeated runs with identical parameters and initial conditions produce consistent numerical results to within floating-point tolerance.



Absence of Numerical Divergence Under Tested Conditions



The system exhibits no numerical divergence or catastrophic instability for the parameter regimes exercised in tests L1–L10.



Evidence and Validation



The LCRD v3 system is validated by the test suite:



fundamental\_theory.lcrd.tests.lcrd\_t1\_to\_t10



This suite was executed using both direct pytest invocation and module-level execution:



pytest -q lcrd/tests/lcrd\_t1\_to\_t10.py  

python -m fundamental\_theory.lcrd.tests.lcrd\_t1\_to\_t10  



All tests passed successfully.



Scope of This Lock



This lock guarantees:



• Correct governing equations  

• Correct parameter interpretation  

• Correct numerical implementation  

• Verified coupling behavior  

• Exact CRFT reduction  

• Bounded numerical behavior under tested regimes  



This lock does not guarantee:



• Physical realism of rotor or curvature fields  

• Long-time behavior outside tested regimes  

• Universality across parameter space  

• Analytical well-posedness  

• Energy conservation beyond explicitly tested cases  



Those properties require separate, explicit validation.



Locked Status



The LCRD v3 rotor–curvature system is locked at the level of:



• Governing equations  

• Coupling topology  

• First-order time formulation  

• Verified numerical behavior  



Any future modification to the equations, parameters, or numerical operators must explicitly invalidate or extend this lock.



============================================================



