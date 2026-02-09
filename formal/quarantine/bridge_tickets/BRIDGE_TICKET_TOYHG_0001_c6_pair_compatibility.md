# BRIDGE_TICKET_TOYHG_0001 — C6 Toy-H/Toy-G pair-compatibility channel

Status: Proposed (falsifiable; bounded)

Opened: 2026-02-05

## Bridge family taxonomy (governance; docs-only)

- Bridge class: joint_pair_compatibility_bridge
- Evidence strength: bounded_multi
- Degrees of freedom: joint pass/fail signatures pinned; localization rule pinned; probe set bounded
- Falsification mode: pair channel passes on pinned inconsistent signatures or fails on pinned consistent signatures
- Non-implication clause: passing implies only structural compatibility of a joint bookkeeping channel under canonical surfaces; it does not imply physical truth or empirical anchoring

## Claim (falsifiable; structural)

Given pinned Toy-H and Toy-G bridge-channel outcomes on the same probe, a deterministic joint pair-compatibility functional can classify cross-channel agreement/disagreement in bounded form and resolve the remaining `mismatch_toyh_pair_vs_toyg_bridge` frontier under the pinned stress probe.

This is a **structural compatibility** statement only. It does **not** assert physical equivalence or empirical anchoring.

## Canonical surfaces

- C6 surface: `formal/python/crft/cp_nlse_2d.py`
- Pre-gate feasibility: `formal/quarantine/feasibility/BRIDGE_TOYHG_C6_pair_compatibility_feasibility.json`

## Admissibility rule (pinned)

- pair channel is admissible iff all three inputs match on pass/fail status
  - admissible signatures: `P-P-P`, `F-F-F`
  - inadmissible signatures: `P-F-P`, `P-P-F`, `F-F-P` (and other non-uniform tuples)
- failing signatures must emit deterministic localization (`toyh_phase_channel`, `toyh_current_channel`, `toyg_bridge_channel`, or `mixed`)

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_deterministic`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_accepts_uniform_pass_vector`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_phase_current_vs_toyg`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_current_only`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_toyg_only`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_resolution_scan.py::test_bridge_toyhg_c6_pair_compatibility_resolution_signature_map`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_boundary_report_generate_determinism.py::test_bridge_toyhg_c6_pair_compatibility_boundary_report_is_deterministic`
- `formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_boundary_report_pointers_exist.py::test_bridge_toyhg_c6_pair_compatibility_boundary_report_pointers_exist`

## Boundary report artifact

- `formal/quarantine/bridge_tickets/BRIDGE_TOYHG_C6_pair_compatibility_BOUNDARY_REPORT.json`

## Program-level impact check

- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json`

Expected impact under pinned probes:
- mismatch frontier decreases from 1 to 0 after pair-channel integration
- summary records `n_pair_vs_bridge_resolved_by_pair_channel >= 1`
- `recommended_next_target.reason_code == "none"`

## Exit condition

- Passes deterministically on pinned signature map and removes the remaining mismatch frontier.

## Failure posture

- If inconsistent signatures are admitted (or consistent signatures rejected), this ticket is eliminated under current surfaces.

