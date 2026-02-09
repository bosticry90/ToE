# BRIDGE_TICKET_TOYH_0004 — C6 current-anchor compatibility proxy (Toy-H)

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-05

## Bridge family taxonomy (governance; docs-only)

- Bridge class: gauge_current_anchor_compatibility
- Evidence strength: bounded_multi
- Degrees of freedom: global phase theta pinned; local-phase-shear alpha pinned; current-anchor tolerance pinned; grid sizes bounded
- Falsification mode: current-anchor admissibility fails on pinned tiny-shear probes or passes under pinned wrong-operator controls
- Non-implication clause: passing implies only structural compatibility of a current-anchor proxy under the canonical C6 surface; it does not imply physical truth or empirical anchoring

## Claim (falsifiable; structural)

Given the canonical C6 CP-NLSE 2D surface, a deterministic current-anchor observable can remain admissible for tiny local-phase-shear controls that fail the legacy current-channel control threshold, while preserving fail-closed behavior under amplitude scaling and wrong-operator controls.

This is a **structural compatibility** statement only. It does **not** assert physical equivalence or empirical anchoring.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`
- Pre-gate feasibility: `formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_anchor_feasibility.json`

## Admissibility rule (pinned)

- invariance check: `current_l2_rel <= tol_invariance`
- anchor response check: `anchor_response >= min_anchor_response`
- anchor match check: `anchor_error <= tol_current_anchor`

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_deterministic`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_invariant_observables`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_resolves_small_alpha_control_case`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_zero_alpha_response_min`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_amplitude_scaling`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_wrong_operator_sign`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_resolution_scan.py::test_bridge_toyh_c6_current_anchor_resolution_scan`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_boundary_report_generate_determinism.py::test_bridge_toyh_c6_current_anchor_boundary_report_is_deterministic`
- `formal/python/tests/test_bridge_toyh_c6_current_anchor_boundary_report_pointers_exist.py::test_bridge_toyh_c6_current_anchor_boundary_report_pointers_exist`

## Boundary report artifact

- `formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_anchor_BOUNDARY_REPORT.json`

## Program-level impact check

- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`

Expected impact under pinned probes:
- raw-channel `nonredundant` remains true
- `mismatch_toyh_current_only` is eliminated from the mismatch frontier
- targeted resolution records `n_current_control_fail_resolved_by_current_anchor >= 1`

## Exit condition

- Passes deterministically under pinned admissibility rules and preserves fail localization under controls.

## Failure posture

- If tiny-shear anchor admissibility fails or wrong-operator controls pass, this ticket is eliminated under current surfaces.

