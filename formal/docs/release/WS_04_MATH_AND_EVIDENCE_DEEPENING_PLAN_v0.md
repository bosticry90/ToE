# WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0

## Workstream
- ID: WS-04
- Name: Math and Evidence Deepening
- Status: DONE
- Priority: COMPLETED

## Objective
Increase scientific depth by reducing tautological theorem surfaces and broadening empirical confrontation with explicit falsification criteria.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-04-T01 | Select 2-3 theorem surfaces | DONE | WS-03-T05 | Theorem shortlist | Surface list with rationale |
| WS-04-T02 | Classify each as contract, bridge, derivation | DONE | WS-04-T01 | Classified theorem table | Classification notes |
| WS-04-T03 | Identify shallow theorem targets | DONE | WS-04-T02 | Shallow-target remediation list | Gap annotations |
| WS-04-T04 | Choose one empirical lane to broaden | DONE | WS-04-T03 | Lane selection note | Selected lane and scope |
| WS-04-T05 | Define falsification criteria | DONE | WS-04-T04 | Falsification criteria section | Criteria checklist |
| WS-04-T06 | Complete one substantive upgrade | DONE | WS-04-T05 | Upgraded theorem or evidence lane | Diff + test or result evidence |

## Theorem Shortlist (WS-04-T01)
| ID | Surface Path | Why Selected |
| --- | --- | --- |
| THM-01 | formal/toe_formal/ToeFormal/QM/EvolutionContract.lean | Central typed theorem surface referenced by active QM derivation chains. |
| THM-02 | formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean | Governs seam witness schema used in promotion-readiness logic and bridge routes. |
| THM-03 | formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md | High-impact QFT object derivation target with downstream route dependencies. |

## Theorem Classification (WS-04-T02)
| ID | Surface Path | Class | Classification Notes |
| --- | --- | --- | --- |
| THM-01 | formal/toe_formal/ToeFormal/QM/EvolutionContract.lean | contract | Defines typed evolution contract interfaces and admissibility constraints. |
| THM-02 | formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean | bridge | Encodes witness packaging that bridges seam constraints to route-level checks. |
| THM-03 | formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md | derivation | Derivation target surface for gauge-object claims and downstream route proof flow. |

## Shallow-Target Remediation List (WS-04-T03)
| ID | Surface Path | Gap Annotation | Planned Upgrade Direction |
| --- | --- | --- | --- |
| THM-01 | formal/toe_formal/ToeFormal/QM/EvolutionContract.lean | Strong interface typing but limited nontrivial theorem obligations in active usage. | Add at least one non-identity lemma constraining admissible evolution behavior under pinned assumptions. |
| THM-02 | formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean | Witness schema is policy-rich but light on derivational uniqueness implications. | Add bridge lemmas connecting witness constraints to measurable seam-gap monotonicity obligations. |
| THM-03 | formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md | Derivation target remains scaffold-heavy in active route flow. | Promote one concrete derivation sub-chain to explicit intermediate theorem statements and checks. |

## Empirical Lane Selection (WS-04-T04)
- Selected lane: QFT-GR seam numeric threshold measurement lane.
- Primary surface: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md.
- Broadening scope:
	- include comparator-lane threshold scoring under the same metric definitions,
	- bind predeclared fail conditions to release-gate behavior,
	- preserve non-claim boundaries while increasing discriminatory power.

## Falsification Criteria (WS-04-T05)
- F1 shrinkage failure: two consecutive cycles with S(c) < 0.05.
- F2 marginal-gain failure: two consecutive cycles with M(c) < 0.10 and N(c)=0.
- F3 stagnation failure: Streak3(c) = 3.
- F4 comparator failure: comparator lane outperforms packet lane on both S(c) and M(c) for two consecutive cycles.
- Any F1-F4 trigger forces threshold_4_pass = false and blocks release authorization.
- Trigger and comparator fields must be present in admissible measurement artifacts.

## Substantive Upgrade Completed (WS-04-T06)
- Updated surface: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md.
- Upgrade delivered:
	- Comparator and Falsification Extension section.
	- Comparator binding status token.
	- Falsification binding status token.
	- Explicit F1-F4 fail conditions with release-gate blocking semantics.

## Evidence Log
- 2026-03-17 WS-04-T01: selected theorem shortlist `THM-01` through `THM-03` in section `Theorem Shortlist (WS-04-T01)`.
- 2026-03-17 WS-04-T02: classified `THM-01` through `THM-03` in section `Theorem Classification (WS-04-T02)`.
- 2026-03-17 WS-04-T03: added `Shallow-Target Remediation List (WS-04-T03)` with explicit gaps and upgrade directions.
- 2026-03-17 WS-04-T04: selected empirical lane in section `Empirical Lane Selection (WS-04-T04)`.
- 2026-03-17 WS-04-T05: recorded explicit F1-F4 falsification criteria in section `Falsification Criteria (WS-04-T05)`.
- 2026-03-17 WS-04-T06: validated protocol upgrade with `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_toe_qft_gr_seam_packet44_numeric_threshold_measurement_protocol_gate.py` -> `3 passed in 0.72s`.

## Blockers
- none

## Exit Criteria
- Selected theorem surfaces have explicit remediation targets.
- One empirical lane has broader confrontation criteria.
- At least one theorem surface becomes materially less tautological.
