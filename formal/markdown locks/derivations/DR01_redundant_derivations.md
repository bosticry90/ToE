DR01 Redundant Derivations (EQ-02 Only)

====================================================================

Purpose and scope

This document re-derives the dispersion relation DR-01 using only the locked linearized equation EQ-02 as recorded in State\_of\_the\_Theory.md.

Markdown role (intent authority):

Present complete and explicit derivation narratives.

Provide a full assumption audit.

Lean role (structural authority):

Certify definitional expansions and equivalences of expressions derived here.

Python role (behavioral authority):

Minimal numeric cross-check only.

A minimal numeric assertion exists in test\_dr01\_eq02\_dispersion.py (structural-numeric).

This document does not assert physical correctness, experimental interpretation, or model completeness. Its sole purpose is to show that, given EQ-02, multiple independent internal derivation routes converge to the same dispersion relation.

====================================================================

Canonical EQ-02 statement (linear Schrödinger limit)

Locked limiting case (as implemented in ToeFormal.CPNLSE2D.Dispersion):

For g = 0:

i \* partial\_t psi(x, y, t) = - (1/2) \* Delta psi(x, y, t)

where:

Delta = partial\_xx + partial\_yy

Target dispersion relation (locked form in Lean definition omega):

omega(kx, ky) = (kx^2 + ky^2) / 2

====================================================================

Route F — Plane-wave / Fourier mode substitution
Ansatz

Assume a complex plane-wave solution of the form:

psi(x, y, t) = A \* exp(i \* (kx \* x + ky \* y - omega \* t))

where:

A is a nonzero complex constant

kx, ky, omega are real numbers

This functional form matches the structural template planeWave used in the Lean lock file.

Time derivative

Compute the time derivative:

partial\_t psi
= A \* partial\_t exp(i \* (kx \* x + ky \* y - omega \* t))
= A \* exp(i \* (kx \* x + ky \* y - omega \* t)) \* i \* (-omega)
= -i \* omega \* psi

Therefore:

i \* partial\_t psi = omega \* psi

Spatial Laplacian

Compute spatial derivatives:

partial\_x psi = i \* kx \* psi
partial\_xx psi = (i \* kx)^2 \* psi = -kx^2 \* psi

partial\_yy psi = -ky^2 \* psi

Therefore:

Delta psi = partial\_xx psi + partial\_yy psi
Delta psi = -(kx^2 + ky^2) \* psi

Applying the operator in EQ-02:

(1/2) \* Delta psi
= - (1/2) \* (-(kx^2 + ky^2) \* psi)
= (1/2) \* (kx^2 + ky^2) \* psi

Substitution into EQ-02

EQ-02 states:

i \* partial\_t psi = - (1/2) \* Delta psi

Substitute the computed expressions:

omega \* psi = (1/2) \* (kx^2 + ky^2) \* psi

For a nontrivial mode (A != 0), psi can be cancelled, yielding:

omega(kx, ky) = (kx^2 + ky^2) / 2

This exactly matches the locked omega definition.

====================================================================

Route O — Operator diagonalization (spectral route)
Operator form of EQ-02

Define the spatial linear operator:

L = - (1/2) \* Delta

Then EQ-02 becomes:

i \* partial\_t psi = L psi

Eigenfunctions of the spatial operator

A Fourier mode exp(i \* (kx \* x + ky \* y)) satisfies:

Delta exp(i \* (kx \* x + ky \* y))
= - (kx^2 + ky^2) \* exp(i \* (kx \* x + ky \* y))

Applying L:

L exp(i \* (kx \* x + ky \* y))
= - (1/2) \* Delta exp(i \* (kx \* x + ky \* y))
= (1/2) \* (kx^2 + ky^2) \* exp(i \* (kx \* x + ky \* y))

Thus the eigenvalue is:

lambda(kx, ky) = (kx^2 + ky^2) / 2

Dispersion from spectral evolution

For a single eigenmode evolving in time:

psi(x, y, t) = A \* exp(i \* (kx \* x + ky \* y)) \* exp(-i \* omega \* t)

Applying operators:

i \* partial\_t psi = omega \* psi
L psi = lambda \* psi

EQ-02 therefore requires:

omega = lambda

Hence:

omega(kx, ky) = (kx^2 + ky^2) / 2

This route reflects the spectral structure that UCFF and second-order constructions rely on, without introducing any additional assumptions.

====================================================================

Route E — Quadratic functional (linear Hamiltonian) route
Quadratic functional associated with EQ-02

Define the quadratic functional:

H\[psi] = integral over Omega of (1/2) \* |grad psi|^2 dx dy

where Omega is a spatial domain such as R^2 or a periodic domain.

This functional is introduced solely as a mathematical construction that generates the linear equation EQ-02. It does not assert or imply a Hamiltonian formulation for the nonlinear parent theory.

Variational convention and boundary assumptions

For the variational steps below:

psi and its complex conjugate psi\* are treated as independent variables.

Periodic boundary conditions or sufficient decay at infinity are assumed so that boundary terms vanish under integration by parts.

Variational derivative

Under these assumptions, the functional derivative is:

delta H / delta psi\* = - (1/2) \* Delta psi

If the evolution is defined by the standard Schrödinger-type relation:

i \* partial\_t psi = delta H / delta psi\*

then the resulting equation of motion is:

i \* partial\_t psi = - (1/2) \* Delta psi

which is exactly EQ-02.

Fourier-mode evaluation

Expand psi into Fourier modes. For a single mode:

psi = A \* exp(i \* (kx \* x + ky \* y)) \* exp(-i \* omega \* t)

The gradient satisfies:

|grad psi|^2 = (kx^2 + ky^2) \* |psi|^2

Thus the contribution of this mode to H is proportional to:

(1/2) \* (kx^2 + ky^2) \* |A|^2

In Schrödinger evolution, the mode frequency equals the eigenvalue of the linear operator generated by the quadratic functional. Therefore:

omega(kx, ky) = (kx^2 + ky^2) / 2

====================================================================

Equivalence checks

All three derivation routes reduce to the same algebraic statement:

omega(kx, ky) = (kx^2 + ky^2) / 2

Lean formalization covers two layers:



A2 (purely algebraic redundancy):

\- Route F expression = Route O expression = locked omega

&nbsp; (definitional expansions / equivalences only; no PDE calculus)



A3 (operator-level reduction on planeWave via axioms):

\- EQ-02 on planeWave reduces to coefficient-equality-times-planeWave (no cancellation)

\- Closed-form operator reductions for i\*Dt(planeWave) and (-(1/2))\*Delta(planeWave)

&nbsp; using only the stated operator-action axioms

====================================================================

Assumption audit (no hidden assumptions beyond EQ-02 and the explicit assumptions listed)

Assumption:
psi admits Fourier or plane-wave mode decomposition
Used in:
Routes F, O, E
Justification:
Linear constant-coefficient PDE on R^2 or a periodic domain supports Fourier eigenmodes

Assumption:
kx, ky, omega are real numbers
Used in:
All routes
Justification:
Consistent with the locked definition omega : R -> R -> R

Assumption:
Cancellation of psi is valid for nontrivial modes
Used in:
Route F
Justification:
Plane-wave ansatz assumes A != 0

Assumption:
Spatial integration domain Omega exists
Used in:
Route E
Justification:
Required only to define the quadratic functional; dispersion depends on mode eigenvalues, not domain details

Assumption:
Boundary terms vanish under integration by parts
Used in:
Route E
Justification:
Guaranteed by periodic boundary conditions or sufficient decay

No external physics assumptions (such as BEC physics, Bogoliubov theory, or Gross–Pitaevskii interpretations) are used in any derivation step.

Assumption:

Operator action on planeWave is axiomatized (Dt\_planeWave and Delta\_planeWave) in the A3 layer

Used in:

A3 operator-level reduction (PlaneWaveOperators.lean)

Justification:

This layer is structural-only: it encodes the expected operator behavior on the specific planeWave template,

but does not derive derivative facts from Mathlib analysis (no differentiability development).

====================================================================

Outputs

Derived internally from EQ-02:

omega(kx, ky) = (kx^2 + ky^2) / 2

Lean evidence pointers (implemented):



A2 (ToeFormal/CPNLSE2D/DR01\_Redundant.lean):

\- omegaF\_eq\_omega

\- lambdaO\_eq\_omega

\- routeF\_equals\_routeO

\- routeF\_equals\_locked\_form

\- routeO\_equals\_locked\_form



A3 (ToeFormal/CPNLSE2D/PlaneWaveOperators.lean):

\- iDt\_planeWave\_closed

\- negHalfDelta\_planeWave\_closed

\- L\_planeWave\_closed

\- EQ02Holds\_planeWave\_iff



Not implemented here (explicitly out of scope for A2/A3 as written):

\- A Mathlib-analytic proof that Delta applied to an exponential/plane wave equals -(kx^2+ky^2) times itself

\- Any Route E variational formalization in Lean

====================================================================

