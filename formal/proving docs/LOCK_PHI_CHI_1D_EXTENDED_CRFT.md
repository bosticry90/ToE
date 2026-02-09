============================================================



LOCK: 1D COUPLED φ–χ EXTENDED CRFT SYSTEM



============================================================



Status



This document locks the one-dimensional coupled φ–χ extended CRFT system as implemented and validated in the numerical layer. The lock applies to the structure of the equations, the coupling terms, the first-order time formulation, and the verified reduction property.



This lock does not assert general solution correctness, stability, or physical completeness beyond what is explicitly tested.



Fields and State Variables



The system evolves three fields on a one-dimensional periodic domain:



φ(x, t)

Complex scalar field representing the primary CRFT field.



χ(x, t)

Real scalar auxiliary field.



π(x, t)

Real scalar field defined as π = ∂t χ.



The state at time t is:



state(t) = (φ(x, t), χ(x, t), π(x, t))



Spatial Domain and Operators



The system is defined on a one-dimensional periodic domain of length L, discretized on N grid points.



All spatial derivatives are computed spectrally using FFTs with standard multipliers:



First derivative: D1 → (i k)

Second derivative: D2 → −k²

Fourth derivative: D4 → +k⁴

Sixth derivative: D6 → −k⁶



where k are the spectral wave numbers associated with the periodic grid.



Parameters



The parameter set for the coupled system is:



g\_eff

Effective nonlinear coupling inherited from the CRFT first-order branch.



rho0

Uniform background density.



alpha

Dimensionless coupling coefficient multiplying χ in the φ equation.



gamma

Dimensionless coupling coefficient multiplying (|φ|² − rho0) in the χ equation.



lambda\_chi

Coefficient multiplying the fourth spatial derivative of χ.



beta\_chi

Coefficient multiplying the sixth spatial derivative of χ.



Time-stepping parameters are external and are not part of the model definition.



Governing Equations (Authoritative Form)



The coupled φ–χ system is defined by the following partial differential equations.



Primary field equation:



i ∂t φ

= −(1/2) ∂xx φ

&nbsp; + g\_eff (|φ|² − rho0) φ

&nbsp; + alpha χ φ





Auxiliary field equations:



∂t χ = π



∂t π

= −(1/2) ∂xx χ

− lambda\_chi ∂xxxx χ

− beta\_chi ∂xxxxxx χ

− gamma (|φ|² − rho0)



First-Order Time Formulation



The auxiliary field χ obeys a second-order-in-time equation, which is evolved numerically by introducing the auxiliary variable π:



π = ∂t χ



This yields a closed first-order system in time for the state (φ, χ, π), suitable for standard ODE time integrators.



Implementation Form



For numerical time stepping, the system is implemented in an algebraically equivalent solved-for form:



φ\_t

= i \[ (1/2) ∂xx φ − g\_eff (|φ|² − rho0) φ − alpha χ φ ]



χ\_t = π



π\_t

= −(1/2) ∂xx χ

− lambda\_chi ∂xxxx χ

− beta\_chi ∂xxxxxx χ

− gamma (|φ|² − rho0)



This solved-for representation is mathematically equivalent to the governing equations above and differs only by algebraic rearrangement.



Reduction Property (Locked Consistency Claim)



The following exact reduction property is enforced and validated:



If all of the following conditions hold simultaneously:



alpha = 0

gamma = 0

χ(x, t) = 0 for all x

π(x, t) = 0 for all x



then the coupled system reduces exactly to the single-field CRFT first-order φ equation:



i ∂t φ

= −(1/2) ∂xx φ

&nbsp; + g\_eff (|φ|² − rho0) φ





and the auxiliary fields remain identically zero:



∂t χ = 0

∂t π = 0



This reduction is exact, not approximate.



Evidence and Validation



The reduction property is validated by the test:



crft.tests.crft\_c5\_multifield\_consistency



The test computes:



• The φ right-hand side using the coupled system with couplings disabled.

• The φ right-hand side using an independent single-field implementation.

• The χ and π right-hand sides under the same conditions.



The reported results are:



max |dphi\_coupled − dphi\_single| = 0.000e+00

max |dchi\_coupled − pi| = 0.000e+00

max |dpi\_coupled| = 0.000e+00



These results demonstrate bit-for-bit equality of the two φ evolutions and correct auxiliary behavior.



Scope of This Lock



This lock guarantees:



• Structural correctness of the coupled φ–χ equations.

• Correct implementation of coupling terms.

• Exact reduction to the single-field CRFT equation when couplings are disabled.

• Consistent first-order time formulation.



This lock does not assert:



• Stability for arbitrary parameters.

• Physical interpretation of χ.

• Energy conservation of the coupled system.

• Dispersion relations of the coupled system.



Those properties require separate, explicit validation.



Locked Status



The 1D coupled φ–χ extended CRFT system is locked at the level of:



• Equation structure

• Coupling topology

• Reduction consistency



Any future modification affecting the equations or parameters must invalidate or extend this lock explicitly.



============================================================

