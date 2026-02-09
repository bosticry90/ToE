# Abstract (backup venue)

Automated analysis systems often compute comparisons whenever data are available, even when the justification for comparing those data is underspecified. This creates a structural failure mode in which automation erodes epistemic boundaries.

We describe a deterministic pipeline architecture that enforces explicit admissibility as a prerequisite for comparison. The system separates intent declaration from execution, generates enforcement artifacts that bind governance decisions to runtime behavior, and records refusal (“blocked”) outcomes as first-class, auditable results.

The contribution is architectural and methodological rather than analytical: absent explicit authorization, the correct system behavior is to refuse comparison and record that refusal deterministically. This pattern enables reproducible, auditable scientific software systems that preserve epistemic constraints even under automation.
