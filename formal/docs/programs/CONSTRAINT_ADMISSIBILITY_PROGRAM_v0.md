# Constraint Admissibility Program v0

Scope and intent
- This document defines the constraint (CX) governance program for admissibility predicates.
- Constraints are first-class testable objects: deterministic front doors, comparators, controls, lock files.
- This document is governance-only and does not assert external truth.

Constraint families
- Bound constraints: inequalities such as finite norms, residual bounds, and bounded functionals.
- Invariance constraints: equivalence checks under pinned transforms.
- Stability constraints: non-expansive or contractive update checks under pinned norms.
- Causality/locality constraints: bounded influence-cone or domain-of-dependence checks.

Canonical front-door report schema conventions
- Required top-level fields: `schema`, `config_tag`, `regime_tag`, `domain_tag`, `params`, `cases`, `fingerprint`.
- Reports are typed and deterministic.
- `fingerprint` is sha256 of the report payload excluding the fingerprint field.

Comparator posture
- Comparator input must be typed reports only.
- Pass/fail is expectation-aware by case kind (`positive_control`, `negative_control`).
- Comparator record is deterministic and lockable.
- Comparator records must include explicit `scope_limits`.

Required controls
- Positive control: pinned admissible setting expected to pass.
- Negative control: pinned break setting expected to fail internally and pass only as explicit break detection.

Allowed claim types
- `within_rep_only`
- `front_door_only`
- `external_anchor_only`

Scope boundaries
- Constraints are admissibility predicates over artifacts, not unconditional claims about nature.
- No external truth claim unless explicitly tied to a pinned external anchor contract.

Operational workflow
- Pin definitions and tolerances.
- Generate front-door artifacts from pinned inputs.
- Run comparator pass/fail semantics.
- Verify negative controls.
- Freeze lock markdown from the deterministic record.
- Wire tests into governance suite and inventory.
