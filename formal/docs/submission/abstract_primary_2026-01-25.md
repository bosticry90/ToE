# Abstract (primary venue)

Scientific computing pipelines frequently compute comparisons by default whenever numerical data are available, even when the epistemic prerequisites for comparison are ambiguous or absent. This practice risks silently converting uncertainty into inferred claims under automation.

We present a failure-resistant comparison pipeline architecture in which admissibility is treated as an explicit governance concern rather than an implicit assumption. Comparisons are executed only when authorized by a declared admissibility configuration; when authorization is absent, the pipeline deterministically emits a structured “blocked” outcome rather than a partial or inferred result.

The system separates intent declaration from enforcement, uses generated manifests to bind governance decisions to execution, and records both computed and blocked outcomes as canonical, auditable artifacts. Importantly, numerical proximity is never treated as evidence of admissible pairing.

This work does not propose new analytical methods or domain claims. Instead, it contributes a reproducible execution pattern that preserves epistemic boundaries in automated scientific workflows by making refusal to compare a first-class, inspectable outcome.
