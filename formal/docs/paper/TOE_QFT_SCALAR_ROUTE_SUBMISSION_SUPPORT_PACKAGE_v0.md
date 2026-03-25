# ToE QFT Scalar Route Submission Support Package v0

Package ID:
- TOE_QFT_SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_v0

Scope:
- Last-mile scalar Paper 1 submission-support coherence only.
- No new scalar derivation tranche.
- No seam expansion and no scalar scope broadening.

Purpose:
- Convert the scalar submission support bundle into one machine-checkable package.
- Pin the exact last-mile owner-confirmation blocker without pretending upload completion.
- Enforce consistency across metadata lock, title/abstract lock, cover-letter skeleton, upload bundle manifest, execution board, and canonical export package.

Support-package components:
1. Metadata lock coherence:
- title, abstract, author line, affiliation line, keyword list, and seam-hold token remain aligned across metadata-bearing support files.

2. Support-file bundle completeness:
- title/abstract lock, metadata lock, venue profile, figure package plan, reviewer-facing summary, cover-letter skeleton, upload bundle manifest, and submission execution board are all present.

3. Figure bundle presence:
- canonical figure PDFs and source `.tex` files exist at the paths declared in the upload bundle manifest.

4. Placeholder-control policy:
- the corresponding-contact placeholder remains allowed only as a tracked owner-confirmation item.
- placeholder state must be explicit and not silently forgotten.

5. Pre-upload blocker registry:
- final upload is blocked only by owner confirmation of the submission email and by final upload-bundle assembly replay.

Outside-scope and freeze statement:
- this package does not authorize upload by itself.
- this package does not authorize scalar claim expansion.
- this package does not alter `QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0`.

Status token:
- SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_STATUS_v0: READY_WITH_OWNER_CONFIRMATION_PENDING_v0

Reproducibility pointers:
- formal/output/toe_qft_scalar_route_submission_support_package_checkpoint_v0.json
- formal/python/tests/test_toe_qft_scalar_route_submission_support_package_gate.py
- formal/docs/submission/scalar_paper1/TITLE_ABSTRACT_LOCK.md
- formal/docs/submission/scalar_paper1/SUBMISSION_METADATA_LOCK.md
- formal/docs/submission/scalar_paper1/VENUE_FORMATTING_PROFILE.md
- formal/docs/submission/scalar_paper1/FIGURE_PACKAGE_PLAN.md
- formal/docs/submission/scalar_paper1/COVER_LETTER_SKELETON.md
- formal/docs/submission/scalar_paper1/REVIEWER_FACING_SUMMARY.md
- formal/docs/submission/scalar_paper1/UPLOAD_BUNDLE_MANIFEST.md
- formal/docs/submission/scalar_paper1/SUBMISSION_EXECUTION_BOARD.md