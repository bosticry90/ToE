# BRIDGE_FEASIBILITY_TOYG_0001 — Toy-G -> canonical feasibility scan

Status: Active (feasibility-gating; bounded)

Opened: 2026-02-04

## Bridge family taxonomy (governance; docs-only)

- Bridge class: topological_invariant_feasibility_scan
- Evidence strength: bounded_feasibility
- Degrees of freedom: none (target set pinned to C6/C7/UCFF; deterministic capability checks)
- Falsification mode: feasibility artifact regresses (no compatible canonical non-archive surface found)
- Non-implication clause: passing feasibility does not imply bridge validity; it only permits bounded ticket creation

## Purpose (bounded)

Before introducing Toy-G bridge tickets, verify that at least one canonical,
non-archive surface exposes typed, deterministic inputs suitable for Toy-G
topological invariant probes (phase-like field on a spatial grid).

## Inputs (pinned)

- C6 surface: `formal/python/crft/cp_nlse_2d.py`
- C7 surface: `formal/python/crft/acoustic_metric.py`
- UCFF surface: `formal/python/toe/ucff/core_front_door.py`

## Evidence (pytest)

- `formal/python/tests/test_bridge_toyg_canonical_feasibility_scan_determinism.py::test_bridge_toyg_canonical_feasibility_scan_is_deterministic`
- `formal/python/tests/test_bridge_toyg_canonical_feasibility_artifact_pointers_exist.py::test_bridge_toyg_canonical_feasibility_artifact_pointers_exist`

## Output artifact

- `formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json`

## Exit condition

- `found == true` for at least one canonical target.

## Failure posture

- If all targets are blocked, do not create Toy-G bridge tickets.
- Add or expose a typed deterministic canonical front door before continuing.
