LEGACY REINTEGRATION REGISTER (BOOKKEEPING)

Project: ToE

Last updated: 2026-02-01


Purpose

Reincorporate prior work from archive/ as conditionally admissible input without violating:
- Lean-first authority
- front-door-only bridge discipline
- gate/lock hygiene
- status discipline in State_of_the_Theory.md

This register does not promote any legacy claim. It records what exists, what is a candidate to revalidate, and the intended (safe) migration path.


Triage artifacts (generated)

- Markdown summary: formal/output/legacy_archive_triage_20260201_130457_477894.md
- JSON payload: formal/output/legacy_archive_triage_20260201_130457_477894.json


Buckets (meaning)

- reference_only
  Keep in archive/; treat as provenance/context. No imports into core; no new status.

- candidate_revalidate
  Eligible for staged extraction into current lanes, but only via:
  - explicit scope statement
  - a new front-door callable (if code)
  - regression tests (pytest) and/or computed locks where appropriate
  - explicit Dependencies + Evidence entries when/if it becomes an inventory item


Initial shortlist (recommended to review first)

1) Prior state-of-the-theory drafts (structured docs)
- archive/docs/state_of_the_theory_ARCHIVE.md
- archive/docs/state_of_the_theoryv5.md
Action: treat as historical reference; mine for missing inventory items only if they can be restated under current rules.

2) Field-theory test inventory (process artifact)
- archive/field_theory/docs/dev_notes/test_inventory_master.md
Action: extract any tests that still apply as “Behavioral (Python) invariants” into formal/python/tests/, but only after confirming the target modules still exist.

3) LCRD / field-theory step notes (structured but legacy)
- archive/lcrd_legacy_docs/ft_candidate_algebra_01_*.md
- archive/lcrd_legacy_docs/ft_step7_lcrd_v2_*.md
Action: treat as design notes; if any concrete invariant is salvageable, rewrite it as a modern observable/audit with explicit inputs and no implicit data reads.

4) Legacy acoustic metric diagnostic code
- archive/fundamental_theory/crft/diagnostics/acoustic_metric.py
Status: Resolved (Already Present)

Canonical surface (adopt): MT-01a Python front door + lock regression
- formal/python/crft/acoustic_metric.py
- formal/python/tests/test_mt01_acoustic_metric_lock.py

Action taken (2026-02-01): Removed redundant duplicate port/test and adopted MT-01a as the single authoritative Python surface.

Pilot closure: Completed; canonical surface is MT-01a; duplicate-surface prevention test present; no further action unless MT-01a changes.

Do not re-port: Do not create a second acoustic-metric implementation under a different package path; extend or adapt MT-01a if a new API shape is needed.

5) Legacy UCFF tests
- archive/tests/test_ucff_core_roundtrip.py
- archive/tests/test_ucff_core_symbolic.py
Action: port clean-room under formal/python/tests/ against the non-archive UCFF core/front-door (formal/python/toe/ucff/core_front_door.py).

Dossiers (resolved; bounded evidence only):
- formal/quarantine/dossiers/DOSSIER_0001_archive_tests_test_ucff_core_roundtrip_py.md
- formal/quarantine/dossiers/DOSSIER_0002_archive_tests_test_ucff_core_symbolic_py.md

Revalidation target (explicit):
- Identify the intended canonical UCFF target module(s) (non-archive) and re-express the invariants against the current API surface.
- If no canonical UCFF symbolic/core exists yet, keep these as reference_only until a front-door UCFF core is intentionally introduced.

Proposed next pilot (selection rule: high reuse, low scope, lockable): Start here after a quick feasibility scan for current UCFF core targets.

Feasibility scan (2026-02-01):
- Eligible UCFF Diagnostics (not core): OV-UCFF-01..07 exist as deterministic, typed-input audit tools with report schemas and pinned artifacts:
  - Observables: formal/python/toe/observables/ovucff01_jitter_structure_audit.py .. ovucff07_cross_metric_coupling_audit.py
  - Tools (front doors): formal/python/tools/ovucff01_jitter_structure_audit.py .. ovucff07_cross_metric_coupling_audit.py
  - Diagnostics artifacts + pinned inputs: formal/python/artifacts/diagnostics/OV-UCFF-*/; formal/python/artifacts/input/OV-UCFF-*/
- Eligible UCFF Core (non-archive): formal/python/toe/ucff/core_front_door.py (typed inputs + deterministic JSON report; no archive imports).

Decision: UCFF core target exists; UCFF legacy test families have been revalidated clean-room against the non-archive front door via bounded, deterministic pytest evidence (see dossiers).

Exit condition (explicit): Keep the UCFF core front door quarantine-safe and keep the bounded UCFF invariants passing under deterministic locks.


6) CRFT turbulence diagnostics (C8)
Status: Blocked (no canonical non-archive front door)

Feasibility evidence: formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json

Closure: This block is enforced by the feasibility scan artifact above (not a judgment call).

Pointer: C8 tickets prohibited until prerequisite satisfied.

Prerequisite: Introduce CRFT turbulence front door (non-archive, typed inputs, deterministic outputs).


Safety rules (non-negotiable)

- Do not import archive/ Python modules into current core modules.
- Any reincorporated behavior must be expressed as a new audited observable/tool with explicit inputs.
- Any speculative legacy content must remain quarantined (documentation-only) until it has an explicit exit condition and a declared revalidation target.


Next action (choose one)

A) Port one legacy test family (small scope)
- Pick one of the legacy tests above, identify its intended target module, and re-express it against current APIs.

B) Port the acoustic_metric diagnostic (medium scope)
- (Resolved) Acoustic metric already present via MT-01a (see item 4). Do not re-port; extend/adapt MT-01a if needed.

C) Create a “legacy quarantine index” section in State_of_the_Theory.md (docs-only)
- Add a small inventory-style note pointing to this register and the triage artifacts.
