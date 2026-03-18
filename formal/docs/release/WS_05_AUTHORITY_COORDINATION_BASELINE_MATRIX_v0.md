# WS_05_AUTHORITY_COORDINATION_BASELINE_MATRIX_v0

Spec ID:
- `WS_05_AUTHORITY_COORDINATION_BASELINE_MATRIX_v0`

Classification:
- `P-POLICY`

Purpose:
- Record the before-state coordination cost baseline for representative canonical changes.
- Provide quantitative evidence for WS-05 authority-surface simplification outcomes.

Non-claim boundary:
- coordination baseline artifact only.
- no theorem promotion.
- no route promotion.
- no external truth claim.

## Method

- Baseline measured from current enforcement surfaces and gate expectations.
- Counts are conservative minima intended for before/after comparison.
- Manual edit counts include token and pointer/path edits required to keep parity surfaces green.

## Evidence anchors

- Pillar consistency gate: `formal/python/tests/test_pillar_status_matrix_consistency_gate.py`
- Deep-maturity parity gate: `formal/python/tests/test_pillar_deep_maturity_program_gate.py`
- Representative seam packet progression gate: `formal/python/tests/test_toe_qft_gr_seam_packet41_hold_fork_decision_gate.py`
- Full governance suite references: `governance_suite.ps1`

## Baseline matrix (before-state)

| Workflow ID | Representative change | Minimum surfaces touched | Minimum token edits | Minimum path/pointer edits | Notes |
| --- | --- | ---: | ---: | ---: | --- |
| WF-01 | Pillar status promotion | 4 | 8 | 1 | Surfaces: discharge doc, pillar matrix, roadmap, compact state. Consistency gate enforces parity among discharge/matrix/roadmap and QFT matrix-state token agreement. |
| WF-02 | Seam packet progression | 5 | 10 | 6 | Surfaces: packet doc, packet artifact, roadmap, compact state or central inventory, packet gate/test family. Representative gate enforces decision/status parity and cross-surface pointer presence. |
| WF-03 | Deep-maturity target rollover | 5 | 12 | 4 | Surfaces: deep-maturity program doc, deep-maturity registry JSON, roadmap, compact state, deep-maturity gate expectations. Program/registry target tokens and per-row maturity fields require coordinated updates. |

## Baseline pressure indicators

- `SEAM_PACKET_GATE_FILE_COUNT_PACKET40_TO_49_v0: 66`
- `M4_SEAM_CLOSURE_GATE_FAMILY_COUNT_v0: 7`
- `GOVERNANCE_SUITE_EXPLICIT_WS05_RELEVANT_GATES_v0: pillar_status_matrix_consistency + pillar_deep_maturity_program`

## Interpretation

- Coordination burden is currently multi-surface by design and enforced by parity gates.
- WS-05 success criteria should reduce touch counts for at least one workflow by removing repeated fallback updates, not by weakening parity checks.
- This baseline is the reference for WS-05-T03/T04 after-state comparison.
