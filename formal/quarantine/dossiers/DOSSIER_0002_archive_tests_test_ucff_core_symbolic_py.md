# DOSSIER 0002: archive/tests/test_ucff_core_symbolic.py

## Source

- Path: archive/tests/test_ucff_core_symbolic.py
- SHA256: 0d5c45284a0e7f0534dcb5819f14579097cdffd5b0f77fb8522d333c879b9761
- Bytes: 2948
- Kind: python

## Why It Scored High

- Total: 129
- Breakdown: base=50 tests=50 keywords=25 equations=4 refs=0 family=0 feasibility=0 penalty=0
- Keyword hits: dispersion, equation, lagrangian, sympy, ucff
- Reference hits: (none)
- Equation signals: 1
- Doc family key: archive/tests/test_ucff_core_symbolic.py

## Candidate Classification

- Classification: diagnostic_candidate

## Proposed Reintegration Target

- Existing canonical surface (if any): None identified (no non-archive `equations.ucff_core` or equivalent UCFF core front door).
- Dependency observed (legacy): imports `equations.ucff_core` and asserts structural properties of the first-order Lagrangian and the k-power structure of dispersion relations.
- Prerequisite (if reintegrating): intentionally introduce a non-archive UCFF symbolic/core front door (clean-room) and then restate these invariants against that surface.

## Validation Plan

- Symbolic: Port as shape/invariant tests (e.g., term presence in Lagrangian; dispersion contains k^2/k^4 and parameters) once a canonical UCFF core exists.
- Numeric: Not required for these structure checks; numeric validation belongs in OV-UCFF audit lanes.
- Locks/tests: Re-home under `formal/python/tests/` targeting only non-archive modules; keep the assertions purely structural to avoid overfitting legacy symbol names.

## Exit Condition

- Accepted / Rejected / Reference-only: Resolved (bounded evidence only; does not upgrade physical truth claims).

Resolved when (explicit rule):

1. A non-archive canonical UCFF front door exists and is referenced as the target surface.
2. At least 2 non-overlapping bounded invariants, rewritten clean-room, are passing against the front door.
3. Each invariant has a pytest evidence pointer recorded in this dossier (node id + file).
4. The tests are deterministic (no randomness, no time integration drift, no hidden I/O) and remain quarantine-compliant (no archive imports; no archive path reliance at runtime).

Update (2026-02-01): A non-archive UCFF core/front-door exists at formal/python/toe/ucff/core_front_door.py (typed inputs + deterministic JSON report; no archive imports).

Progress (2026-02-01): One bounded symbolic-family invariant has been ported clean-room against the front-door report and is passing:
- formal/python/tests/test_ucff_core_front_door_symbolic_invariant_01.py::test_ucff_core_front_door_recovers_even_polynomial_coefficients_via_sympy

Progress (2026-02-01): A second independent bounded invariant has been ported (bounded monotonicity check over the front-door report) and is passing:
- formal/python/tests/test_ucff_core_front_door_symbolic_invariant_02.py::test_ucff_core_front_door_monotone_non_decreasing_on_bounded_interval_when_coeffs_nonnegative

Closure criteria met (2026-02-01): Two independent bounded, report-only invariants are now ported and passing against the non-archive UCFF core front door.

Next step (optional): port additional non-overlapping symbolic invariants only if they can be expressed as bounded checks over the same front-door report.
