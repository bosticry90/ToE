=====================================================================

LOCK\_CP\_NLSE\_2D\_DISPERSION.md

=====================================================================



=====================================================================

SCOPE AND PURPOSE

=====================================================================



This document defines and locks the two-dimensional plane-wave dispersion

relation for the Coherence-Regularized Field Theory (CRFT) two-dimensional

Coherence-Penalized Nonlinear Schrödinger Equation (CP–NLSE) in its linear

limit.



The lock applies strictly to the linear Schrödinger regime obtained by

setting the nonlinear coupling to zero. It establishes the operational

dispersion relation as measured from numerical time evolution and does

not assert any canonical second-order-in-time or nonlinear dispersion

claims in two spatial dimensions.



=====================================================================

AUTHORITATIVE FILES

=====================================================================



Evidence driver and validation test:



formal/python/crft/tests/test\_c6\_cp\_nlse\_2d\_dispersion.py



Implementation module providing the governing equation, grid construction,

and time evolution used by the validation test:



formal/python/crft/cp\_nlse\_2d.py



Package boundary establishing the CRFT module namespace:



crft/\_\_init\_\_.py



=====================================================================

FIELD, DOMAIN, AND VARIABLES

=====================================================================



psi(x, y, t) is a complex scalar field defined on a two-dimensional

spatial domain.



x and y are spatial coordinates.



t is physical time.



rho(x, y, t) = |psi(x, y, t)|^2 is the field density.



The validation and implementation operate on a two-dimensional periodic

domain:



x in \[0, Lx)

y in \[0, Ly)



with uniform grid resolution Nx by Ny.



For the C6 dispersion validation, the test configuration uses:



Nx = 32

Ny = 32

Lx = 2 pi

Ly = 2 pi



=====================================================================

GOVERNING EQUATION (OPERATIONAL 2D CP–NLSE)

=====================================================================



The two-dimensional CP–NLSE implemented in the numerical layer is:



i partial\_t psi = - (1/2) Laplacian psi + g ( |psi|^2 - rho0 ) psi



where:



Laplacian psi = partial\_xx psi + partial\_yy psi



g is the nonlinear coupling coefficient.



rho0 is a uniform background density parameter used in the coherence-style

nonlinearity.



This equation is treated as an operational evolution equation for

numerical simulation.



=====================================================================

LOCKED LIMITING CASE (LINEAR SCHRÖDINGER LIMIT)

=====================================================================



The CRFT C6 validation locks the linear regime by setting:



g = 0



In this limit, the governing equation reduces to the two-dimensional

linear Schrödinger equation:



i partial\_t psi = - (1/2) Laplacian psi



This linear equation is the only regime used to establish the dispersion

relation locked in this document.



=====================================================================

LOCKED PLANE-WAVE DISPERSION RELATION

=====================================================================



Consider a plane-wave solution of the form:



psi(x, y, t) = A exp( i ( kx x + ky y - omega t ) )



Substitution into the linear Schrödinger equation yields the angular

frequency relation:



omega(kx, ky) = 1/2 ( kx^2 + ky^2 )



This relation is the operational dispersion statement locked by this

document.



=====================================================================

VALIDATION PROCEDURE

=====================================================================



The C6 validation test performs the following steps:



1\. Construct a plane-wave initial condition at background amplitude:



   psi(x, y, 0) = sqrt(rho0) exp( i ( kx x + ky y ) )



2\. Evolve the field forward in time using the numerical simulator

   implemented in crft/cp\_nlse\_2d.py.



3\. Record the complex field value at a single spatial grid point,

   specifically the grid index (0, 0), at each time step.



4\. Estimate the dominant angular frequency from the real part of the

   recorded time series using a Fourier transform.



5\. Compute the theoretical angular frequency using:



   omega\_th = 1/2 ( kx^2 + ky^2 )



6\. Declare the test successful if the relative error satisfies:



   |omega\_num - omega\_th| / omega\_th < 1.0e-1



=====================================================================

LOCKED EVIDENCE

=====================================================================



The dispersion relation locked in this document is validated by executing:



python -m crft.tests.crft\_c6\_cp\_nlse\_2d\_dispersion



The observed validation output includes:



rel\_error = 5.755e-02 < 1.0e-01



This confirms agreement between the numerically measured frequency and

the theoretical dispersion relation within the enforced tolerance.



=====================================================================

EXCLUSIONS

=====================================================================



This lock does not establish or imply:



\- Any nonlinear two-dimensional dispersion relation for g not equal to

  zero.



\- Any higher-order spatial dispersion operators in two dimensions.



\- Any canonical second-order-in-time or omega-squared dispersion

  relation in two dimensions.



\- Any conservation laws or invariants beyond what is explicitly measured

  by the validation test.



=====================================================================

DOCUMENTATION REQUIREMENTS

=====================================================================



Any reference to this lock in equation inventories or formal documents

must include:



\- The governing two-dimensional CP–NLSE equation.



\- The explicit linear limiting case g = 0.



\- The locked dispersion relation:



  omega(kx, ky) = 1/2 ( kx^2 + ky^2 )



\- The name of the enforcing validation test:

  crft/tests/crft\_c6\_cp\_nlse\_2d\_dispersion.py



\- The enforced tolerance and observed validation result.



=====================================================================

END LOCK\_CP\_NLSE\_2D\_DISPERSION.md

=====================================================================

