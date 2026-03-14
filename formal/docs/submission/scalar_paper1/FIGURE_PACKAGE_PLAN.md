# Scalar Paper 1 Figure Package Plan

Current state:
- Manuscript contains one compile-safe boxed figure placeholder (`fig:scalar-route-flow`).

Submission hardening objective:
- Replace placeholder with a submission-ready derivation flow figure.

Planned figure set:
1. `figures/scalar_route_flow_v1.pdf`
   - Purpose: Master-action to low-energy Schrodinger-class extraction flow.
2. `figures/claim_boundary_map_v1.pdf`
   - Purpose: Visual split of recovered structure, interpretive clarification, bounded novelty, and explicit non-claims.

Execution checklist:
1. Produce both files as vector PDF assets.
2. Replace boxed placeholder in `main.tex` with `\\includegraphics` call for `scalar_route_flow_v1.pdf`.
3. Add claim-boundary figure either in main text or appendix once caption placement is finalized.
4. Re-run compile replay and verify figure rendering in `main.pdf`.

Acceptance criteria:
- Every figure has a caption aligned with bounded-scope language.
- No figure text implies interacting-field or gauge completion.
- Build remains compile-clean except accepted non-fatal layout warnings.