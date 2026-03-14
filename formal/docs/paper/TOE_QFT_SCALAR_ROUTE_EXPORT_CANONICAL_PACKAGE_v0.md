# ToE QFT Scalar Route Export Canonical Package v0

Export package ID:
- TOE_QFT_SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_v0

Scope:
- Canonical TeX paper object for bounded free-scalar Paper 1 under formal/docs/submission/scalar_paper1.

Purpose:
- Convert the governed scalar manuscript stack into one checkable canonical export artifact.
- Keep a single-source manuscript object before arXiv-first or journal-specific derivative layouts.

Canonical export package pointers:
- formal/docs/submission/scalar_paper1/README.md
- formal/docs/submission/scalar_paper1/main.tex
- formal/docs/submission/scalar_paper1/refs.bib
- formal/docs/submission/scalar_paper1/metadata.json
- formal/docs/submission/scalar_paper1/figures/

Export-governance checks:
1. Canonical manuscript presence:
- main.tex exists as the single canonical scalar manuscript source.

2. Bibliography presence:
- refs.bib exists and is bound by main.tex.

3. Figure package placeholder presence:
- figures directory exists for controlled figure ingress.

4. Title and abstract placeholders:
- main.tex contains TITLE_PLACEHOLDER_SCALAR_PAPER1 and ABSTRACT_PLACEHOLDER_SCALAR_PAPER1.

5. Bounded claim language parity:
- main.tex contains the bounded claim sentence aligned to TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.

6. Physical contribution representation:
- main.tex contains a dedicated physical-contribution section.

7. Authority surface mirroring:
- State_of_the_Theory.md and PHYSICS_ROADMAP_v0.md include export pointers and status token.

8. Seam hold continuity:
- QFT_GR_SEAM_FORK_DECISION_STATUS_v0 remains HOLD_FOR_SCALAR_PUBLICATION_v0.

Policy guardrails:
- scalar Paper 1 baseline freeze remains active.
- no new scalar derivation tranche is authorized.
- export package is canonical single-source only.

Status token:
- SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_STATUS_v0: CANONICAL_SCALAR_PAPER1_EXPORT_OBJECT_PINNED

Reproducibility pointers:
- formal/output/toe_qft_scalar_route_export_canonical_package_checkpoint_v0.json
- formal/python/tests/test_toe_qft_scalar_route_export_canonical_package_gate.py
- formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_PACKAGE_v0.md
- formal/docs/paper/TOE_QFT_GR_SEAM_FORK_DECISION_v0.md
