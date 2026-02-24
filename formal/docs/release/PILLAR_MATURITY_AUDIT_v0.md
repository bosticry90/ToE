# PILLAR_MATURITY_AUDIT_v0

Authority Status: ANALYTICAL / NON-AUTHORITY
This document does not define adjudication tokens, pillar status, or governance semantics.
All canonical authority resides in matrix + discharge + roadmap + state surfaces.

Date: 2026-02-23
Audit Version: v0.2 (re-baselined after 5x5 overreach correction)
Scope: QFT, QM, GR, EM, SR pillar authority surfaces.
Purpose: score current maturity on closure robustness, empirical evidence completeness, and drift resistance.

## Rubric (0-5)
- Closure Robustness: theorem/criteria closure quality and explicit boundedness.
- Evidence Completeness: artifact-backed evidence quality for physics-facing claims (not only governance control artifacts).
- Drift Resistance: ability to prevent semantic inflation, status drift, and cross-surface inconsistencies.

Overall score weighting:
- Closure Robustness: 40%
- Evidence Completeness: 35%
- Drift Resistance: 25%

Scoring guardrails:
- Evidence custody maturity (hash/pointer parity + coupling-gate continuity) is necessary but not sufficient for `Evidence Completeness = 5.0`.
- `Evidence Completeness = 5.0` requires explicit physics-facing adequacy justification, not only governance-control artifacts.
- The document must carry explicit gate tokens to distinguish custody maturity from adequacy maturity:
	- `EVIDENCE_CUSTODY_5X5_GATE`
	- `EVIDENCE_ADEQUACY_5X5_GATE`

## Canonical Inputs
- formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md
- formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md
- formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md
- formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md
- formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md
- formal/docs/paper/PHYSICS_ROADMAP_v0.md
- formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json
- formal/python/tests/test_pillar_status_matrix_consistency_gate.py
- formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py
- formal/python/tests/test_authority_token_single_definition_gate.py

Validation baseline observed in current cycle:
- Full suite: `1977 passed, 142 skipped`

## Results
| Pillar | Closure Robustness | Evidence Completeness | Drift Resistance | Overall Maturity | Priority |
|---|---:|---:|---:|---:|---|
| QFT | 5.0 | 4.4 | 5.0 | 4.79 | Preserve top-tier closure/drift; expand adequacy-facing evidence justification |
| QM | 4.7 | 4.1 | 4.9 | 4.55 | Strengthen adequacy-facing external lane beyond bounded internal continuity |
| GR | 4.6 | 4.0 | 4.9 | 4.47 | Extend publication-bridge replication breadth with explicit adequacy criteria |
| EM | 4.2 | 3.8 | 4.8 | 4.11 | Continue comparator depth and add adequacy-grade sensitivity justification |
| SR | 4.1 | 3.7 | 4.8 | 4.02 | Continue theorem-evidence series and add explicit adequacy-facing bridge criteria |

Current gating posture:
- `EVIDENCE_CUSTODY_5X5_GATE: SATISFIED_v0`
- `EVIDENCE_ADEQUACY_5X5_GATE: NOT_SATISFIED_v0`

Per-pillar adequacy justification token scaffold:
- `EVIDENCE_ADEQUACY_QFT_5X5_JUSTIFICATION_v0: NOT_PRESENT_v0`
- `EVIDENCE_ADEQUACY_QM_5X5_JUSTIFICATION_v0: NOT_PRESENT_v0`
- `EVIDENCE_ADEQUACY_GR_5X5_JUSTIFICATION_v0: NOT_PRESENT_v0`
- `EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_v0: NOT_PRESENT_v0`
- `EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_v0: NOT_PRESENT_v0`

## Delta Since Prior Audit
- SR evidence depth improved via theorem-evidence checkpoint artifact + dedicated coupling gate (`SR_THEOREM_EVIDENCE_CHECKPOINT_*`).
- EM evidence depth improved again via comparator cycle-02 artifact + dedicated coupling gate (`EM_PILLAR_MAXWELL_LINEAR_COMPARATOR_PACKET_CYCLE02_*`).
- GR evidence depth improved via publication-bridge checkpoint artifact + dedicated coupling gate (`GR01_PUBLICATION_BRIDGE_CHECKPOINT_*`).
- QFT evidence diversity improved via dedicated diversification checkpoint artifact + dedicated coupling gate (`QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_*`).
- Drift resistance remains high and stable: matrix coverage, single-definition policy, and cross-surface coupling gates all remain green under full-suite validation.

## Evidence Notes by Pillar
### QFT
- Closure robustness remains highest: adjudication + inevitability discharged with extensive pre-execution/nonflip governance chain and consistency gates.
- Evidence maturity increased via explicit diversification checkpoint coupling while preserving bounded nonflip/non-claim posture.

### QM
- Derivation-grade discharge remains strong with explicit anti-circularity, row-level criteria, and hashed artifact linkage.
- Evidence profile remains largely internal/theorem-governance; external alignment surfaces remain bounded and non-claim.

### GR
- Bounded/discrete discharge posture remains robust and anti-shortcut disciplined.
- Publication-bridge checkpoint is now pinned and coupled across authority surfaces; remaining drag is depth/replication breadth rather than absence of checkpoint evidence.

### EM
- EM now has two comparator cycles (cycle-01 and cycle-02) with independent coupling gates and synchronized hash/pointer surfaces.
- EM remains bounded non-claim; next gains come from controlled comparator depth expansion rather than governance changes.

### SR
- SR now has explicit matrix registration and synchronized token mirrors across roadmap/state/matrix, improving drift resistance.
- SR now includes an explicit theorem-evidence checkpoint artifact and coupling gate, lifting evidence maturity while preserving enforcement-roadmap closure semantics.
- SR remains below EM/GR evidence depth because current checkpoint is initial (single-cycle) rather than a broader theorem-evidence series.

## Highest-Leverage Next Remediation (smallest bounded move)
Target: continue low-end evidence-depth growth (SR/EM) and then strengthen QM external-facing evidence interfaces without scope inflation.

Action package (minimal):
1. SR: add theorem-evidence checkpoint cycle-02 with explicit linkage to next bounded theorem-discharge rows plus dedicated coupling gate.
2. EM: add comparator cycle-03 with sensitivity-row expansion and dedicated coupling gate.
3. QM: add one bounded external-lane evidence checkpoint (still non-claim) with artifact/hash/pointer coupling.
4. Keep ACTIVE/CLOSED roadmap rows matrix-registered and single-definition synchronized under existing gates.

Expected effect:
- Raises system floor further by lifting SR/EM evidence depth from checkpoint-level toward series-level.
- Improves balance across pillars without altering adjudication semantics or governance versioning.

## Execution Plan (next 3 release cycles)

Execution objective:
- Improve evidence-depth maturity while preserving existing closure tokens, matrix status, and non-claim governance semantics.
- No adjudication-token flips are authorized by this plan.

### Cycle R+1 (floor-raise cycle)

Scope:
1. SR: theorem-evidence checkpoint cycle-02.
2. EM: comparator packet cycle-03.
3. QM: external-lane evidence checkpoint cycle-01 (bounded non-claim).

Deliverables:
- SR artifact: `formal/output/sr_covariance_theorem_evidence_checkpoint_cycle02_v0.json`
- EM artifact: `formal/output/em_maxwell_linear_comparator_packet_cycle03_v0.json`
- QM artifact: `formal/output/qm_external_lane_evidence_checkpoint_cycle01_v0.json`
- Roadmap/state/matrix pointer sync for each new artifact token.

Required coupling gates (new tests expected):
- `formal/python/tests/test_sr_theorem_evidence_checkpoint_coupling_cycle02_gate.py`
- `formal/python/tests/test_em_comparator_evidence_coupling_cycle03_gate.py`
- `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_gate.py`

Pass criteria:
- All three artifacts exist and hashes are pinned in canonical surfaces.
- All three dedicated coupling gates pass.
- Existing matrix/coverage/single-definition gates remain green.

Fail criteria:
- Any missing artifact, missing hash token, or unsynchronized cross-surface pointer.
- Any dedicated coupling gate failure.
- Any regression in matrix consistency, roadmap coverage, or single-definition policy gates.

### Cycle R+2 (series-hardening cycle)

Scope:
1. SR: theorem-evidence checkpoint cycle-03 (series continuity).
2. EM: comparator packet cycle-04 with sensitivity-row broadening.
3. GR: publication-bridge checkpoint cycle-02 for replication breadth.

Deliverables:
- SR artifact: `formal/output/sr_covariance_theorem_evidence_checkpoint_cycle03_v0.json`
- EM artifact: `formal/output/em_maxwell_linear_comparator_packet_cycle04_v0.json`
- GR artifact: `formal/output/gr01_publication_bridge_checkpoint_cycle02_v0.json`

Required coupling gates (new tests expected):
- `formal/python/tests/test_sr_theorem_evidence_checkpoint_coupling_cycle03_gate.py`
- `formal/python/tests/test_em_comparator_evidence_coupling_cycle04_gate.py`
- `formal/python/tests/test_gr01_publication_bridge_checkpoint_coupling_cycle02_gate.py`

Pass criteria:
- SR/EM each demonstrate at least a 2-cycle evidence series in canonical references.
- GR publication bridge lane has at least two independently pinned checkpoint cycles.
- Full test baseline remains green including existing cross-surface gates.

Fail criteria:
- Any pillar cycle introduced without dedicated coupling gate.
- Any cycle lacking canonical hash/pointer synchronization.
- Any downgrade or drift in currently discharged status tokens.

### Cycle R+3 (balance and stabilization cycle)

Scope:
1. SR: theorem-evidence checkpoint cycle-04 (stability confirmation).
2. EM: comparator packet cycle-05 (sensitivity + robustness extension).
3. QM: external-lane evidence checkpoint cycle-02 (independent lane reinforcement).
4. QFT: evidence-diversification checkpoint cycle+1 under existing nonflip controls.

Deliverables:
- SR artifact: `formal/output/sr_covariance_theorem_evidence_checkpoint_cycle04_v0.json`
- EM artifact: `formal/output/em_maxwell_linear_comparator_packet_cycle05_v0.json`
- QM artifact: `formal/output/qm_external_lane_evidence_checkpoint_cycle02_v0.json`
- QFT artifact: `formal/output/qft_evidence_diversification_checkpoint_cycle02_v0.json`

Required coupling gates (new tests expected):
- `formal/python/tests/test_sr_theorem_evidence_checkpoint_coupling_cycle04_gate.py`
- `formal/python/tests/test_em_comparator_evidence_coupling_cycle05_gate.py`
- `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle02_gate.py`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle02_gate.py`

Pass criteria:
- SR and EM evidence lanes show sustained multi-cycle continuity (>= 3 consecutive cycles from this plan).
- QM external-lane evidence has >= 2 bounded cycles with independent artifacts.
- QFT evidence diversification grows without changing adjudication semantics.

Fail criteria:
- Any evidence cycle requires semantic broadening outside bounded non-claim scope.
- Any missing gate ownership (no dedicated coupling test for a new cycle artifact).
- Any ACTIVE/CLOSED row drift against matrix registration requirements.

## Program-level acceptance and stop/go rules

Global pass condition per cycle:
- Dedicated cycle gates pass for every planned artifact.
- `test_pillar_status_matrix_consistency_gate.py` passes.
- `test_pillar_matrix_roadmap_coverage_gate.py` passes.
- `test_authority_token_single_definition_gate.py` passes.

Global stop condition (no further cycle progression until fixed):
- Any red in the three global gates above.
- Any unsynchronized artifact/hash pointer between discharge, roadmap, state, and matrix surfaces.
- Any attempted status promotion without completed evidence-cycle coupling checks.

Planned maturity movement if all three cycles pass:
- SR evidence completeness approaches GR/EM range via checkpoint-series continuity.
- EM evidence completeness rises toward GR through comparator depth and sensitivity expansion.
- QM evidence completeness improves via bounded external-lane reinforcement.
- QFT remains top-tier on closure/drift while increasing evidence diversity under nonflip custody controls.

## Release Note (2026-02-23)

Scope completed in this cycle:
- Added and wired multi-cycle evidence checkpoint artifacts for SR (cycle-02/03/04), EM (cycle-03/04), GR publication bridge (cycle-02), QFT diversification (cycle-02), and QM external-lane (cycle-01/02).
- Synchronized artifact/hash/gate tokens across discharge docs, roadmap, and state surfaces.
- Upgraded all newly introduced cycle gates from scaffold checks to full artifact-hash + cross-surface pointer coupling tests.

Scope extension (post-note uplift):
- Added and wired EM comparator cycle-05 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired GR publication-bridge cycle-03 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired QFT evidence-diversification cycle-03 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired SR theorem-evidence cycle-05 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired QM external-lane evidence cycle-03 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired EM comparator cycle-06 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired GR publication-bridge cycle-04 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired QFT evidence-diversification cycle-04 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired SR theorem-evidence cycle-06 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired QM external-lane evidence cycle-04 artifact + coupling gate across discharge/roadmap/state surfaces.
- Added and wired EM comparator cycle-07 artifact + coupling gate across discharge/roadmap/state surfaces.
- Normalized EM state-surface token ordering (cycle-02 through cycle-07) and finalized cycle-06/07 SHA parity to clear cross-surface drift.
- Executed 5x5 program Cycle block A: added and wired SR theorem-evidence cycle-07/08 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block A: added and wired EM comparator cycle-08/09 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block A: added and wired QM external-lane evidence cycle-05/06 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block A: added and wired GR publication-bridge cycle-05/06 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block A: added and wired QFT evidence-diversification cycle-05/06 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block B: added and wired SR theorem-evidence cycle-09/10 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block B: added and wired EM comparator cycle-10/11 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block B: added and wired QM external-lane evidence cycle-07/08 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block B: added and wired GR publication-bridge cycle-07/08 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block B: added and wired QFT evidence-diversification cycle-07/08 artifacts + coupling gates across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block C: added and wired QM closure-hardening bundle cycle-01 artifact + coupling gate across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block C: added and wired GR closure-hardening bundle cycle-01 artifact + coupling gate across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block C: added and wired EM closure-hardening bundle cycle-01 artifact + coupling gate across discharge/roadmap/state surfaces.
- Executed 5x5 program Cycle block C: added and wired SR closure-hardening bundle cycle-01 artifact + coupling gate across discharge/roadmap/state surfaces.

Validation:
- Integrated checkpoint suite executed across all new cycle gates plus global matrix/coverage/single-definition gates.
- Result: `12 passed in 3.96s`.
- Extended integrated checkpoint (including EM cycle-05 gate) result: `13 passed in 4.30s`.
- Further-extended integrated checkpoint (including GR cycle-03 gate) result: `14 passed in 4.62s`.
- Further-extended integrated checkpoint (including QFT cycle-03 gate) result: `15 passed in 4.94s`.
- Further-extended integrated checkpoint (including SR cycle-05 gate) result: `16 passed in 5.30s`.
- Further-extended integrated checkpoint (including QM cycle-03 gate) result: `17 passed in 5.91s`.
- Further-extended integrated checkpoint (including EM cycle-06 gate) result: `18 passed in 5.93s`.
- Further-extended integrated checkpoint (including GR cycle-04 gate) result: `19 passed in 6.31s`.
- Further-extended integrated checkpoint (including QFT cycle-04 gate) result: `20 passed in 6.97s`.
- Further-extended integrated checkpoint (including SR cycle-06 gate) result: `21 passed in 6.99s`.
- Further-extended integrated checkpoint (including QM cycle-04 gate) result: `22 passed in 7.40s`.
- Integrated coupling+governance sweep (all active cycle coupling gates + global matrix/coverage/single-definition gates) result: `33 passed in 9.78s`.
- Cycle block A targeted gate sweep (10 new cycle gates + 3 global gates) result: `13 passed in 4.53s`.
- Integrated coupling+governance sweep after Cycle block A (all active cycle coupling gates + global matrix/coverage/single-definition gates) result: `43 passed in 12.46s`.
- Cycle block B targeted gate sweep (10 new cycle gates + 3 global gates) result: `13 passed in 4.48s`.
- Integrated coupling+governance sweep after Cycle block B (all active cycle coupling gates + global matrix/coverage/single-definition gates) result: `53 passed in 15.47s`.
- Cycle block C targeted gate sweep (4 new closure-hardening gates + 3 global gates) result: `7 passed in 2.46s`.
- Cycle block C integrated sweep #1 (all active coupling gates + global matrix/coverage/single-definition gates) result: `57 passed in 16.60s`.
- Cycle block C integrated sweep #2 (all active coupling gates + global matrix/coverage/single-definition gates) result: `57 passed in 16.80s`.
- Cycle block C integrated sweep #3 (all active coupling gates + global matrix/coverage/single-definition gates) result: `57 passed in 16.86s`.

All-5 promotion gate reassessment (2026-02-23):
- Gate status: `NOT_SATISFIED_v0`.
- Rationale: cycle continuity and coupling custody are strong, but evidence adequacy remains bounded/non-claim and is not yet sufficient for uniform `Evidence Completeness = 5.0`.
- Evidence/closure trace bundles by pillar:
	- QFT: `qft_evidence_diversification_checkpoint_cycle08_v0` (+ cycle05/06/07 continuity).
	- QM: `qm_external_lane_evidence_checkpoint_cycle08_v0` + `qm_closure_hardening_bundle_cycle01_v0`.
	- GR: `gr01_publication_bridge_checkpoint_cycle08_v0` + `gr01_closure_hardening_bundle_cycle01_v0`.
	- EM: `em_maxwell_linear_comparator_packet_cycle11_v0` + `em_closure_hardening_bundle_cycle01_v0`.
	- SR: `sr_covariance_theorem_evidence_checkpoint_cycle10_v0` + `sr_closure_hardening_bundle_cycle01_v0`.
- Drift-resistance trace: three consecutive full integrated sweeps green (`57/57`, `57/57`, `57/57`).

Governance posture:
- No adjudication-token flip or matrix-status policy change introduced.
- Non-claim boundedness and drift-resistance controls remain intact under existing authority semantics.

## Conclusion
- Current maturity state: re-baselined below all-5, with QFT highest and QM/GR/EM/SR in improving tiers.
- Governance integrity and drift resistance remain strong across active canonical pillars under matrix/coverage hardening.
- Custody maturity is high, but adequacy maturity is not yet sufficient for uniform `Evidence Completeness = 5.0`.

## 5x5 Target Program (all pillars to score 5.0 on all dimensions)

Target state:
- QFT, QM, GR, EM, SR each score `5.0` for Closure Robustness, Evidence Completeness, and Drift Resistance.
- Program remains non-authority and non-adjudicative; no status-token flips are authorized by this section.

### Gap-to-target snapshot (from current table)
- QFT: Closure `5.0` (gap `+0.0`), Evidence `4.4` (gap `+0.6`), Drift `5.0` (gap `+0.0`).
- QM: Closure `4.7` (gap `+0.3`), Evidence `4.1` (gap `+0.9`), Drift `4.9` (gap `+0.1`).
- GR: Closure `4.6` (gap `+0.4`), Evidence `4.0` (gap `+1.0`), Drift `4.9` (gap `+0.1`).
- EM: Closure `4.2` (gap `+0.8`), Evidence `3.8` (gap `+1.2`), Drift `4.8` (gap `+0.2`).
- SR: Closure `4.1` (gap `+0.9`), Evidence `3.7` (gap `+1.3`), Drift `4.8` (gap `+0.2`).

### Exit criteria for assigning score 5.0

Common requirements (all pillars, all dimensions):
1. Every new artifact cycle has dedicated coupling gate coverage and synchronized artifact/hash/pointer tokens across discharge + roadmap + state surfaces.
2. `test_pillar_status_matrix_consistency_gate.py`, `test_pillar_matrix_roadmap_coverage_gate.py`, and `test_authority_token_single_definition_gate.py` remain green on every cycle.
3. No semantic broadening outside bounded non-claim posture.

Per-pillar evidence-depth minimums (for `Evidence Completeness = 5.0` candidate):
- QFT: extend diversification lane through cycle-08 with at least 4 additional independently hashed checkpoints beyond cycle-04.
- QM: extend external-lane evidence through cycle-08 with at least 4 additional independently hashed checkpoints beyond cycle-04.
- GR: extend publication-bridge evidence through cycle-08 with at least 4 additional independently hashed checkpoints beyond cycle-04.
- EM: extend comparator evidence through cycle-11 with at least 4 additional independently hashed checkpoints beyond cycle-07.
- SR: extend theorem-evidence checkpoint series through cycle-10 with at least 4 additional independently hashed checkpoints beyond cycle-06.

Per-pillar closure-depth minimums (for `Closure Robustness = 5.0` candidate):
- QM/GR/EM/SR each add one closure-hardening bundle containing: explicit boundedness restatement, anti-shortcut constraints, and one new discharge-row linkage set that is hash-coupled to canonical surfaces.
- QFT retains current closure posture and must pass all new cycle gates without closure-token drift.

Per-pillar drift-resistance minimums (for `Drift Resistance = 5.0` candidate):
- Zero unresolved token drift incidents over the final 3 consecutive integrated sweeps.
- Zero duplicate authority token definitions across roadmap/state/discharge surfaces for all new cycle bundles.

### Execution sequence (minimum viable path)

Cycle block A (raise floor):
- SR cycle-07/08, EM cycle-08/09, QM cycle-05/06, GR cycle-05/06, QFT cycle-05/06.

Cycle block B (raise evidence depth to 5-candidate threshold):
- SR cycle-09/10, EM cycle-10/11, QM cycle-07/08, GR cycle-07/08, QFT cycle-07/08.

Cycle block C (closure + drift hardening for final 5.0 assignment):
- Add closure-hardening bundle artifacts for QM/GR/EM/SR.
- Run 3 consecutive full integrated sweeps with zero drift incidents.

### Promotion gate to "all-5" scoreboard
The all-5 target is considered achieved only when all of the following are true in one release note entry:
1. Per-pillar evidence and closure minimums above are complete and hash-coupled.
2. Three consecutive full integrated sweeps are green (all active coupling tests + 3 global gates).
3. The results table in this document is updated to `5.0` for every pillar/dimension with explicit trace links to the completed cycle bundles.

### Toward-all-5 maintenance protocol (minimal)

Cadence:
- Run one integrated coupling+governance sweep per release-candidate cut.
- Run one additional integrated sweep immediately after any new cycle artifact is wired.

Hold-line rules:
1. Do not assign all-5 scores unless both `EVIDENCE_CUSTODY_5X5_GATE` and `EVIDENCE_ADEQUACY_5X5_GATE` are `SATISFIED_v0`.
2. No new cycle artifact may be merged without dedicated coupling gate coverage and 3-surface token parity (discharge + roadmap + state).
3. No semantic broadening beyond bounded non-claim posture is allowed under this maintenance mode.

Degrade-and-recover rule:
- If any gate fails, mark affected pillar score(s) as `UNDER_REVIEW` in the next release note, restore green state, then reissue higher scores only after required custody + adequacy gates are green.

Trace requirement per maintenance release note:
- Include integrated sweep result line (`N passed in Ts`) and any newly added artifact IDs (if applicable).
