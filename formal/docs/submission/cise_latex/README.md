# CiSE LaTeX skeleton (camera-ready starting point)

Date: 2026-01-25

Purpose

- Provide a clean LaTeX skeleton for submission to Computing in Science & Engineering (CiSE).
- This is packaging only: it does not change scope/claims, and it treats the v0.2 technical appendix as frozen supplementary material.

Files

- `main.tex` — manuscript body (assembled from the merged v0.3-public manuscript content)
- `refs.bib` — bibliography stub (empty; add entries only if needed)

Compile

- If you have TeX Live / MiKTeX installed:
  - `latexmk -pdf main.tex`
  - or `pdflatex main.tex` (run twice if you add references)

Windows note (MiKTeX)

- `latexmk` may require a Perl installation (MiKTeX error: missing script engine `perl`).
  - Easiest fallback: use `pdflatex main.tex` (run twice).
  - Or install Perl (e.g., Strawberry Perl) and then use `latexmk`.

Notes

- This skeleton uses the standard `article` class so it compiles out-of-the-box.
- If CiSE requires an IEEE-provided class/template, swap the documentclass and adjust the front matter *without changing prose*.

Supplementary material

- Appendix A (Frozen; normative): `formal/docs/epistemic_governance_methodology_paper_draft.md` (v0.2, COMPLETE/FROZEN)
  - Submit as supplementary material / appendix file per CiSE instructions.
