\# FN-01 — Admissible Deformation Class P\[ψ]



\*\*Inventory linkage:\*\* FN-01  

\*\*Purpose:\*\* Organizational / gating framework for candidate deformation terms P\[ψ] applied to EQ-01 / EQ-02.  

\*\*Epistemic level:\*\* Probe-relative; organizational only.  

\*\*Not a physical claim.\*\*



---



\## Scope and intent



This document defines how candidate deformation terms P\[ψ] are \*\*classified\*\* for inclusion in FN-01.



It does \*\*not\*\*:

\- Prove correctness

\- Assign physical interpretation

\- Upgrade epistemic status

\- Define analytic linearization



It \*\*only\*\*:

\- Records gating rules

\- Records classification outcomes

\- Points to existing evidence where applicable



---



\## Gates (binding within FN-01 only)



\### Gate A — CT-01 (linearization-at-0 rule)



\*\*Requirement:\*\*  

The deformation must introduce \*\*no ψ-linear contribution at ψ = 0\*\*, as evaluated under the existing CT-01 probe semantics.



\*\*Reference evidence:\*\*  

\- CT-01-EVIDENCE-PHB  

\- CT-01-EVIDENCE-SOLVER-OMEGA  



---



\### Gate B — Source-free admissibility



\*\*Requirement:\*\*  

The deformation must satisfy:



P(0) = 0





Any ψ-independent constant or source term fails this gate.



---



\### Gate C — Probe invisibility



\*\*Requirement:\*\*  

The deformation must be \*\*probe-invisible\*\* under the \*\*same plane-wave coefficient-identity semantics used by CT-01\*\*.



This gate is \*\*identical\*\* to CT-01’s probe-level dispersion-preservation semantics and introduces no new criterion.



---



\## Classification rule



| Outcome     | Meaning |

|-------------|---------|

| \*\*PASS\*\*    | Survives Gates A + B + C |

| \*\*FAIL\*\*    | Violates at least one gate |

| \*\*UNDECIDED\*\* | Not yet evaluated under current probe semantics |



No reinterpretation, tuning, or exception handling is permitted.



---



\## Examples (with evidence pointers)



\### PASS example



\*\*Candidate:\*\*  



P\[ψ] = g |ψ|² ψ





\- Gate A: PASS (purely nonlinear)

\- Gate B: PASS (P(0)=0)

\- Gate C: PASS (probe-invisible in small-amplitude regime)



\*\*Evidence:\*\*  

\- CT-01-EVIDENCE-PHB  

\- CT-01-EVIDENCE-SOLVER-OMEGA  



---



\### FAIL example



\*\*Candidate:\*\*  



P\[ψ] = V ψ





\- Gate A: FAIL (explicit ψ-linear term)

\- Gate B: PASS

\- Gate C: FAIL (probe-visible; shifts ω̂)



\*\*Evidence:\*\*  

\- CT-01-EVIDENCE-PHB  

\- CT-01-EVIDENCE-SOLVER-OMEGA  



---



\### UNDECIDED example (explicitly unclassified)



\*\*Candidate:\*\*  



P\[ψ] = β ∇·(|ψ|² ∇ψ)





\- Gate A: \*\*Not evaluated\*\* (linearization rule for this operator class not defined)

\- Gate B: Expected P(0)=0, \*\*not asserted\*\*

\- Gate C: \*\*UNDECIDED\*\* pending explicit probe evaluation



\*\*Status:\*\*  

UNDECIDED — requires explicit probe-level test before classification.



---



\## Notes



\- This document is organizational and probe-relative only.

\- Member-level outcomes may be marked Deprecated elsewhere if FAIL.

\- No claims here upgrade FN-01 beyond Hypothesis.

