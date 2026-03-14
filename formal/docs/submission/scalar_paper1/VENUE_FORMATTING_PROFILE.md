# Scalar Paper 1 Venue Formatting Profile

Primary packaging target:
- arXiv-first package from canonical source `main.tex`.

Secondary packaging target:
- journal-template variant generated from canonical source after venue lock.

Current execution decision:
- Execute arXiv packaging now from canonical source.
- Keep journal conversion as a deferred formatting pass after scalar upload completion.

Formatting checklist:
1. Validate title and abstract length against venue constraints.
2. Replace `AUTHOR PLACEHOLDER` with final author/affiliation block.
3. Convert figure placeholders into final figure files in `figures/`.
4. Ensure bibliography style matches venue requirement.
5. Check section heading capitalization and citation style compliance.
6. Rebuild with venue-required class or style file while preserving bounded-claim language.

arXiv packaging controls:
1. Keep canonical `article` class for upload reproducibility.
2. Include only files required to reproduce `main.pdf`.
3. Verify that no local absolute paths are present in figure includes.
4. Ensure all references resolve in a clean replay (`pdflatex`, `bibtex`, `pdflatex`, `pdflatex`).

Policy guardrails:
- Keep bounded claim and non-claim sections unchanged in meaning.
- Do not alter seam hold status during formatting-only work.