# Scalar Paper 1 Upload Bundle Manifest

Canonical source bundle:
1. main.tex
2. refs.bib
3. figures/scalar_route_flow_v1.pdf
4. figures/claim_boundary_map_v1.pdf
5. figures/scalar_route_flow_v1.tex
6. figures/claim_boundary_map_v1.tex
7. figures/.gitkeep
8. metadata.json

Generated artifact bundle:
1. main.pdf
2. main.log

Submission support files:
1. TITLE_ABSTRACT_LOCK.md
2. VENUE_FORMATTING_PROFILE.md
3. FIGURE_PACKAGE_PLAN.md
4. COVER_LETTER_SKELETON.md
5. REVIEWER_FACING_SUMMARY.md
6. SUBMISSION_EXECUTION_BOARD.md
7. SUBMISSION_METADATA_LOCK.md

Upload-bundle assembly order:
1. Verify figure files exist in `figures/` and replace placeholder-only state.
2. Run compile replay from package directory:
	- `pdflatex -interaction=nonstopmode -halt-on-error main.tex`
	- `bibtex main`
	- `pdflatex -interaction=nonstopmode -halt-on-error main.tex`
	- `pdflatex -interaction=nonstopmode -halt-on-error main.tex`
3. Confirm `main.pdf` and `main.log` were updated in current pass.
4. Collect canonical source bundle, generated artifacts, and support files.
5. Perform pre-upload checklist and gate replay.

Pre-upload checks:
1. Compile replay succeeds from canonical source.
2. PDF opens and metadata is correct for target venue.
3. Author and affiliation placeholders are replaced.
4. Figure placeholders are replaced with final files.
5. Non-claim boundary language is unchanged in meaning.

Current readiness notes:
- Title and abstract lock is complete.
- Figure filenames are now fixed in the bundle inventory.
- Compile/PDF baseline exists and is validated.
- Corresponding-contact email remains final-owner confirmation item.

Policy lock:
- Submission assembly is formatting and packaging only.
- No new derivation tranche is authorized by this bundle step.