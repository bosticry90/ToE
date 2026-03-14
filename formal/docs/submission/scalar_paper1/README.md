# Scalar Paper 1 Canonical Export Package

Package ID:
- scalar_paper1

Purpose:
- Provide one canonical TeX export object for the bounded free-scalar Paper 1 route.
- Keep a single-source manuscript for later arXiv and journal variants.

Canonical source files:
- main.tex
- refs.bib
- metadata.json
- figures/

Single-source policy:
- Edit only main.tex for canonical manuscript content.
- Derivative format variants must branch from this package after governance approval.

Bounded-claim policy anchors:
- The manuscript must preserve bounded free-scalar scope.
- The manuscript must preserve explicit non-claim boundaries.
- Seam hold token remains: QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0.

arXiv-first refinement status (v1):
- title and abstract upgraded from placeholder-only form to publication-facing draft text.
- canonical section ordering now includes introduction, route summary, physical contribution, and non-claim boundary.
- bibliography and citation callouts are wired for a minimal compile-ready baseline.
- figure callout placeholder is represented in-manuscript using a compile-safe boxed figure.

Compile-validation freeze status:
- compile-validation tranche is complete and treated as frozen for this lane.
- canonical PDF artifact exists at `formal/docs/submission/scalar_paper1/main.pdf`.
- submission hardening now proceeds without opening a new derivation or infrastructure tranche.

Submission-package hardening artifacts (active):
- TITLE_ABSTRACT_LOCK.md
- SUBMISSION_METADATA_LOCK.md
- VENUE_FORMATTING_PROFILE.md
- FIGURE_PACKAGE_PLAN.md
- COVER_LETTER_SKELETON.md
- REVIEWER_FACING_SUMMARY.md
- UPLOAD_BUNDLE_MANIFEST.md
- SUBMISSION_EXECUTION_BOARD.md

Execution handoff:
- Active runbook: `SUBMISSION_EXECUTION_BOARD.md`.
- Execution is limited to formatting, packaging, and submission metadata hardening.

Focused scalar gate replay command:
- `python -m pytest -q formal/python/tests/test_toe_qft_scalar_route_export_compile_validation_gate.py formal/python/tests/test_toe_qft_scalar_route_export_canonical_package_gate.py formal/python/tests/test_toe_qft_scalar_route_submission_package_gate.py formal/python/tests/test_toe_qft_scalar_route_submission_candidate_gate.py formal/python/tests/test_toe_qft_scalar_route_submission_readiness_gate.py formal/python/tests/test_toe_qft_gr_seam_fork_decision_gate.py`
