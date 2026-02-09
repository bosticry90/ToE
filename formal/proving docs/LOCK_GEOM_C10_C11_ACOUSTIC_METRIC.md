============================================================



LOCK: CRFT GEOM C10–C11 ACOUSTIC METRIC (1D AND 2D)



============================================================



Status



This document locks the acoustic-metric construction used in the CRFT geometry diagnostics and tests C10–C11, as implemented and evaluated in the numerical layer. The lock applies to:



The explicit metric component formulas used to construct the acoustic metric in 1D and 2D.



The determinant formulas used to evaluate the metric signature.



The specific diagnostic predicates and test assertions that are executed and passed.



This lock does not assert physical completeness, uniqueness, or correctness beyond what is explicitly computed and asserted by the referenced diagnostics and tests.



Files Covered by This Lock



Primary implementation:



acoustic\_metric.py



Test and diagnostic drivers:



crft/tests/crft\_c7\_acoustic\_metric\_diagnostics.py

crft/tests/crft\_geom\_c10\_c11.py



Note: The C7 diagnostic constructs the acoustic metric internally using the same analytical form, but does not call the functions in acoustic\_metric.py. C10–C11 directly exercise the implementation in acoustic\_metric.py.



Definitions and Conventions



The acoustic metric is constructed from:



A density-like scalar field rho (ρ).



A velocity field u:



1D: u(x)



2D: (u\_x(x,y), u\_y(x,y))



A coupling parameter g\_eff.



A local sound-speed-squared field is defined as:



c\_s2 = g\_eff · rho



All computations are performed pointwise on the grid.



Acoustic Metric in 1D (Authoritative Component Form)



The 1D acoustic metric is represented by a 2×2 matrix with components:



g\_tt = −(c\_s2 − u²)

g\_tx = −u

g\_xx = 1



This form is implemented by:



compute\_acoustic\_metric\_1d(rho, u, g\_eff) in acoustic\_metric.py



The returned structure contains arrays for (g\_tt, g\_tx, g\_xx) defined on the 1D grid.



Metric Determinant in 1D (Authoritative Determinant Form)



The determinant of the 1D acoustic metric is defined as:



det(g) = g\_tt · g\_xx − (g\_tx)²



This is implemented by:



metric\_determinant\_1d(metric) in acoustic\_metric.py



Acoustic Metric in 2D (Authoritative Component Form)



The 2D acoustic metric is represented by a 3×3 matrix in coordinates (t, x, y) with components:



g\_tt = −(c\_s2 − u\_x² − u\_y²)

g\_tx = −u\_x

g\_ty = −u\_y

g\_xx = 1

g\_yy = 1



Spatial cross terms (such as g\_xy) are assumed to vanish by construction and are not represented as stored fields in the implementation.



This form is implemented by:



compute\_acoustic\_metric\_2d(rho, u\_x, u\_y, g\_eff) in acoustic\_metric.py



The returned structure contains arrays for (g\_tt, g\_tx, g\_ty, g\_xx, g\_yy) defined on the 2D grid.



Metric Determinant in 2D (Authoritative Determinant Form)



Under the vanishing spatial cross-term assumption (no off-diagonal spatial terms), the determinant of the 2D acoustic metric is computed as:



det(g) = g\_tt · g\_xx · g\_yy − (g\_tx)² · g\_yy − (g\_ty)² · g\_xx



This is implemented by:



metric\_determinant\_2d(metric) in acoustic\_metric.py



For the metrics produced by compute\_acoustic\_metric\_2d, g\_xx = 1 and g\_yy = 1 everywhere, and the determinant reduces algebraically to:



det(g) = g\_tt − (g\_tx)² − (g\_ty)²



Locked Diagnostic and Assertion Claims (What Is Actually Verified)



C7 Acoustic Metric Diagnostics



The module crft/tests/crft\_c7\_acoustic\_metric\_diagnostics.py evaluates diagnostic predicates using an internal construction of the 1D acoustic metric with the same analytical form and prints:



finite fields : True

g\_tt < 0 everywhere : True

det(g) < 0 everywhere: True

PASS



This locks the following claim under the specific construction used by that diagnostic:



The constructed metric component arrays are finite.



The computed g\_tt array is strictly negative everywhere on the diagnostic grid.



The computed det(g) array is strictly negative everywhere on the diagnostic grid.



C10 Acoustic Metric Signature Test (1D)



In crft/tests/crft\_geom\_c10\_c11.py, test\_C10\_acoustic\_metric\_1d constructs a 1D test configuration and asserts:



All metric component arrays are finite.



g\_tt < 0 everywhere.



det(g) < 0 everywhere.



The specific test configuration includes:



N = 128

L = 2π

rho0 = 1.0

u0 = 0.3

g\_eff = 9.8696



This locks the claim that, for this specific parameterized construction, the 1D acoustic metric has:



Negative g\_tt everywhere.



Negative determinant everywhere.



No NaN or Inf values in the checked arrays.



C11 Acoustic Metric Signature Test (2D)



In crft/tests/crft\_geom\_c10\_c11.py, test\_C11\_acoustic\_metric\_2d constructs a 2D test configuration and asserts:



All metric component arrays are finite.



g\_tt < 0 everywhere.



det(g) < 0 everywhere.



The specific test configuration includes:



Nx = 64

Ny = 64

Lx = 2π

Ly = 2π

rho0 = 1.0

u\_x0 = 0.2

u\_y0 = 0.1

g\_eff = 9.8696



This locks the claim that, for this specific parameterized construction, the 2D acoustic metric has:



Negative g\_tt everywhere.



Negative determinant everywhere.



No NaN or Inf values in the checked arrays.



Evidence



You executed the following and obtained PASS:



python -m crft.tests.crft\_c7\_acoustic\_metric\_diagnostics

pytest -q fundamental\_theory\\crft\\tests\\crft\_geom\_c10\_c11.py



Scope Limits (Explicit Non-Claims)



This lock does not claim:



That the acoustic metric is physically correct for all CRFT regimes.



That the signature conditions hold for arbitrary inputs, parameters, or time-evolved fields.



That curvature tensors, geodesics, horizons, or other geometric objects are implemented or validated.



Any analytical equivalence to general-relativistic metrics beyond the explicit component formulas implemented here.



Locked Status



The acoustic-metric component formulas and determinant calculations implemented in acoustic\_metric.py, together with the specific finiteness and signature properties asserted by the C7 diagnostics and C10–C11 tests, are locked at the level described above.



============================================================

