*### Lock first-order UCFF foundation (test-backed)*

Canonical source: equations/ucff\_core.py :: ucff\_first\_order\_eom() 



Locked equation (residual form):

R₁\[φ] = i φₜ + (1/2) φₓₓ − g|φ|²φ + lam φₓₓₓₓ + beta φₓₓₓₓₓₓ = 0 



Locked by tests: test\_phase31\_gpe\_limit.py, test\_phase22\_coherence.py, test\_ucff\_core\_roundtrip.py, test\_ucff\_core\_symbolic.py



Evidence: pytest run shows 100% pass (your output).

