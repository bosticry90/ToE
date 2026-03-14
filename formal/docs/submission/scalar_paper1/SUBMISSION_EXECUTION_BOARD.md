# Scalar Paper 1 Submission Execution Board

Execution scope:
- Submission preparation only.
- No new derivation or seam expansion work.

Policy anchors:
- Scalar publication priority is active on main.
- Seam status remains held: QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0.

Execution status:
1. Title and abstract lock: COMPLETE
2. Canonical compile and PDF validation: COMPLETE
3. Reviewer-facing summary draft: COMPLETE
4. Cover letter skeleton draft: COMPLETE
5. Venue profile and formatting path: IN_PROGRESS
6. Figure package final production files: IN_PROGRESS
7. Upload bundle final assembly: IN_PROGRESS

Immediate execution checklist:
1. Confirm final author and affiliation block for submission metadata.
2. Produce `figures/scalar_route_flow_v1.pdf` and `figures/claim_boundary_map_v1.pdf`.
3. Replace in-manuscript boxed figure with final `\\includegraphics` call.
4. Run compile replay and verify final PDF metadata.
5. Assemble final upload bundle from `UPLOAD_BUNDLE_MANIFEST.md`.
6. Copy final title and abstract to submission form fields.
7. Run scalar submission gate replay before upload.

Definition of done for this board:
- Author metadata is no longer placeholder text.
- Final figure files are present in `figures/` and rendered in `main.pdf`.
- Upload bundle contains canonical sources, generated PDF, and support files.
- Scalar gate subset is green after final packaging pass.