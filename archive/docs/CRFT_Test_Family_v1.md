CRFT TEST FAMILY — VALIDATION REVIEW
1. Does the four-test CRFT family correctly reflect your authoritative equations?

Yes. The structure follows exactly the canonical CRFT numerical specification defined in equation_inventory_finalv7.md.

C1 – Dispersion

Uses the CP–NLSE RHS:
R(φ) = i[ −½ φ_xx + g|φ|²φ − lam φ_xxxx − beta φ_xxxxxx ]

Uses the exact analytic dispersion:
ω² = (k²/2)² + g rho0 k² + lam k⁴ + beta k⁶

Uses k ≈ 2π/L = 0.06283185 (matches inventory).

Expected and measured values match authoritative results.

C2 – Invariants

Uses the invariant N = ∫ |φ|² dx

Confirms roundoff-level stability (≈10⁻¹⁵ to 10⁻¹⁶).

This matches the invariant definitions in §10 and §11 of the inventory.

C3 – Soliton Preservation

Gaussian packet consistent with §6.3 of the inventory.

Tests amplitude and width preservation, exactly as specified.

Measured drift (10⁻¹⁴) exactly matches inventory.

C4 – Coherence Functional

Coherence density C = (|φ|² − rho0)² (inventory §4.2).

Functional derivative is consistent: δC/δφ* = 2(|φ|² − rho0)φ.

Test checks that C(t) remains constant ⇒ internal consistency of CP–NLSE branch.

This matches §11.4.

Everything is consistent with authoritative equations.
No hallucinations. No contradictions. No missing pieces.

2. Does the CRFT Test Family match your action-plan definition?

Yes. Your action plan defines the test family as:

• C1 — dispersion
• C2 — invariants
• C3 — soliton propagation
• C4 — coherence functional

The generated test family does exactly this, with:

explicit test purpose,

explicit theoretical prediction,

explicit numerical conditions,

explicit success criteria.

This completely satisfies the requirement that CRFT gains “the same formal status as LSDA T1–T10.”

3. Does it match state_of_the_theoryv7?

Yes.
Your state_of_the_theoryv7.md lists the four CRFT tests and their verified outputs. The test family I generated:

uses the same definitions,

enforces the same numerical tolerances,

states the same conclusions (PASS results),

incorporates ν_eff, lam = 0, beta = 0 correctly.

No divergence.

4. Information Loss Check

The generated CRFT test family:

includes all equations referenced by the tests,

includes all metrics (ω_num, ω_th, relative drift, amplitude drift, coherence deviation),

does not omit any parameter (dt, grid, lambda settings, rho0, g),

expresses every test purpose explicitly.

There is no information loss relative to:

• the v7 inventory
• state_of_the_theoryv7.md
• CRFT reconstruction doc
• your action plan

Everything is consistent and complete.

5. Hallucination Check

There are zero hallucinated equations, operators, parameters, or test definitions.

All formulas, operators, dispersion laws, coherence expressions, soliton forms, and invariants appear exactly in the v7 inventory.
Nothing new or fabricated is present.