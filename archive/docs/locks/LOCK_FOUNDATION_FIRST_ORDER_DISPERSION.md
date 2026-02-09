=====================================================================

LOCK FOUNDATION — FIRST-ORDER DISPERSION (TEST-BACKED)



CANONICAL SOURCES



equations/ucff\_core.py :: ucff\_dispersion\_first\_order() defines the first-order dispersion directly in terms of ω²(k). 



tests/test\_ucff\_core\_symbolic.py enforces the k-power and parameter structure of the first-order dispersion (presence of k² and k⁴, and explicit dependence on g, ρ0, and lam). 



tests/test\_phase31\_gpe\_limit.py enforces the standard Bogoliubov limiting case when lam = beta = lambda\_coh = 0. 



tests/test\_ucff\_core\_roundtrip.py enforces baseline consistency between the first-order EOM plane-wave reduction and the dispersion specification in the baseline linear regime g = lam = beta = lambda\_coh = 0. 



LOCKED STATEMENT (DISPERSION)



The first-order UCFF dispersion relation is specified at the level of ω²(k) as:



ω²(k) = (k²/2)² + (g ρ0) k² + lam k⁴. 



This is a direct specification of the squared angular frequency as a function of spatial wavenumber. It is not an intermediate result derived from solving the first-order equation of motion for ω(k). The project treats this ω²(k) expression as the canonical dispersion specification for the first-order layer.



LOCKED LIMITING CASE (STANDARD BOGOLIUBOV / NLS–GPE LIMIT)



In the limit:



lam = 0, beta = 0, lambda\_coh = 0,



the first-order UCFF dispersion reduces to the standard Bogoliubov form:



ω²(k) = (k²/2)² + (g ρ0) k². 



The coherence coupling lambda\_coh does not appear in the first-order dispersion at linear order around the homogeneous background, and is explicitly absent from the dispersion expression. 



EVIDENCE (TEST STATUS)



The following tests pass:



tests/test\_ucff\_core\_symbolic.py 



tests/test\_phase31\_gpe\_limit.py 



tests/test\_ucff\_core\_roundtrip.py 



User-run evidence:



python -m pytest -q tests/test\_ucff\_core\_symbolic.py tests/test\_phase31\_gpe\_limit.py tests/test\_ucff\_core\_roundtrip.py



Result: all tests pass (100%).



=====================================================================

