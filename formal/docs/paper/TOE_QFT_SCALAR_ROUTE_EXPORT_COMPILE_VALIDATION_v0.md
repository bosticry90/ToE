# ToE QFT Scalar Route Export Compile Validation v0

Validation ID:
- TOE_QFT_SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_v0

Scope:
- Compile and PDF artifact validation for the canonical scalar Paper 1 export package.

Purpose:
- Verify that the canonical TeX manuscript builds in the available environment.
- Pin generated PDF artifact presence and basic compile diagnostics.

Compile environment:
- compiler: pdflatex (MiKTeX)
- bib tool: bibtex
- package root: formal/docs/submission/scalar_paper1

Validation checks:
1. Compiler availability:
- pdflatex is available and invokable in the workspace environment.

2. Compile replay:
- pdflatex and bibtex replay completes without fatal build termination in final pass.

3. PDF artifact generation:
- formal/docs/submission/scalar_paper1/main.pdf exists and has non-zero size.

4. Log-level diagnostics:
- main.log contains output-written marker for main.pdf.
- non-fatal warnings are tracked explicitly as warning class, not failure class.

5. Governance invariants:
- export canonical package status remains pinned.
- seam hold token remains unchanged.
- no scalar scope expansion is introduced by compile validation.

Status token:
- SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_STATUS_v0: COMPILE_AND_PDF_ARTIFACT_VALIDATED

Reproducibility pointers:
- formal/output/toe_qft_scalar_route_export_compile_validation_checkpoint_v0.json
- formal/python/tests/test_toe_qft_scalar_route_export_compile_validation_gate.py
- formal/docs/submission/scalar_paper1/main.tex
- formal/docs/submission/scalar_paper1/main.pdf
- formal/docs/paper/TOE_QFT_GR_SEAM_FORK_DECISION_v0.md
