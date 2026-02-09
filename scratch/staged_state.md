STATE OF THE THEORY

Project: ToE

Purpose: Epistemic inventory and stabilization

Last updated: 2026-02-05




WORKSPACE STATUS (CANONICAL META)



ToE workspace: ACTIVE — discriminative science phase (candidate pruning under gates/locks)

Current loop focus: DR-01 -> BR-01 -> CV01 (external anchor: OV-BR-03N source.pdf; audit: OV-SEL-BR-01; pruning deliverable: OV-DR-BR-01; comparator deliverable: OV-CV-01)

Closeout checkpoint (2026-02-04): Canonical DR-01 → BR-01 verification passed under the default admissibility manifest (blocked-by-default posture preserved). OV-DR-BR-01 invariants verified: schema=OV-DR-BR-01_candidate_pruning_table/v1; observable_id=OV-DR-BR-01; summary.counts={true:2,false:1,unknown:1}; status.blocked=true.

Bridge extension checkpoint (2026-02-04): Added a second orthogonal Toy-H ↔ C6 bridge constraint (current invariance) with pinned feasibility artifact, pinned boundary report, bridge-ledger inclusion, and bridge-admissibility-manifest inclusion (bounded/report-only; no status upgrade).

Orthogonality audit checkpoint (2026-02-04): Added and pinned a shared-probe Toy-H ↔ C6 orthogonality report (summary.counts={pass_pass:12,pass_fail:1,fail_pass:1,fail_fail:1}; summary.nonredundant=true), plus manifest/ledger evidence pointers (bounded/report-only; no status upgrade).

Mismatch localization checkpoint (2026-02-04): Added and pinned a Toy-H ↔ C6 orthogonality mismatch report (pass_fail/fail_pass only) with signed margins, deterministic failure reason-codes, and a pinned robustness guard over grid/theta/tolerance variants (bounded/report-only; no status upgrade).

Toy-G feasibility checkpoint (2026-02-04): Added and pinned a Toy-G -> canonical feasibility scan across C6/C7/UCFF. Result: found=true via C6; C7/UCFF remain blocked for Toy-G invariant probes under current typed/deterministic surface requirements (bounded/report-only; no status upgrade).

Toy-G bridge checkpoint (2026-02-04): Minted BRIDGE_TICKET_TOYG_0001 (C6 phase-winding quantization proxy) with deterministic bounded tests (determinism, perturbation stability, negative controls, resolution scan) and a pinned boundary report (bounded/report-only; no status upgrade).

Bridge-program independence checkpoint (2026-02-04): Added and pinned BRIDGE_PROGRAM_ORTHOGONALITY_REPORT + BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT across Toy-H and Toy-G on C6; nonredundancy + mismatch localization now audited at program scope under pinned probes and robustness guards (bounded/report-only; no status upgrade).

Toy-G_0002 pre-gate checkpoint (2026-02-04): Added design-only BRIDGE_TICKET_TOYG_0002 targeting the dominant remaining Toy-G mismatch region (fail_not_integer_close) with a pinned feasibility artifact and orthogonality-impact plan; implementation explicitly deferred pending pre-gate completion (bounded/report-only; no status upgrade).

Toy-G_0002 implementation checkpoint (2026-02-04): Implemented BRIDGE_TICKET_TOYG_0002 (C6 mode-index quantization proxy) with deterministic bounded tests, pinned boundary report, ledger/manifest wiring, and rerun program-level orthogonality+mismatch artifacts; nonredundant remains true while targeted Toy-G `fail_not_integer_close` mismatch mass is reduced under pinned probes (bounded/report-only; no status upgrade).

Post-metrics regression lock checkpoint (2026-02-04): Added pinned-artifact regression tests that lock Toy-G_0002 program outcomes (`nonredundant=true`, `n_mismatch=4`, `resolved_by_mode_count=1`) plus boundary/failure-localization expectations for the mode-index lane (bounded/report-only; no status upgrade).

Next-target selection checkpoint (2026-02-04): Added deterministic mismatch-reason summary extraction and opened design-only BRIDGE_TICKET_TOYG_0003 targeting the remaining `mismatch_toyg_bridge_only` region (Toy-G unwrap/coherence class) with implementation explicitly deferred (bounded/report-only; no status upgrade).

Toy-G_0003 pre-gate checkpoint (2026-02-04): Added and pinned BRIDGE_TOYG_C6_unwrap_stability_feasibility.json (design-only) with deterministic implementability checks for target region `mismatch_toyg_bridge_only`, pinned probe set (`stress_toyg_unwrap` primary, `stress_toyg_integer` secondary), pinned grids/tolerances, and explicit block-reason posture (bounded/report-only; no status upgrade).

Toy-G_0003 implementation checkpoint (2026-02-04): Implemented BRIDGE_TICKET_TOYG_0003 (C6 unwrap-stability proxy) with deterministic bounded tests, pinned boundary report, ledger/manifest wiring, and rerun program-level orthogonality+mismatch artifacts; nonredundant remains true, targeted resolution now records `{mode:1, unwrap:1}`, and mismatch summary contracts to `n_mismatch=3` with reason-code counts `{mismatch_toyh_phase_only:1, mismatch_toyh_current_only:1, mismatch_toyh_pair_vs_toyg_bridge:1}` (bounded/report-only; no status upgrade).

Toy-H_0003 pre-gate checkpoint (2026-02-04): Added and pinned BRIDGE_TOYH_C6_phase_anchor_feasibility.json (design-only) with deterministic implementability checks for target region `mismatch_toyh_phase_only`, pinned probe set (`stress_toyh_phase_control` primary, `baseline_all_pass` secondary), pinned grids/tolerances, and explicit block-reason posture (bounded/report-only; no status upgrade).

Toy-H_0003 implementation checkpoint (2026-02-04): Implemented BRIDGE_TICKET_TOYH_0003 (C6 phase-anchor proxy) with deterministic bounded tests, pinned boundary report, ledger/manifest wiring, and rerun program-level orthogonality+mismatch artifacts; nonredundant remains true, targeted resolution now records `{mode:1, unwrap:1, phase_anchor:1}`, and mismatch summary contracts to `n_mismatch=2` with reason-code counts `{mismatch_toyh_current_only:1, mismatch_toyh_pair_vs_toyg_bridge:1}` (bounded/report-only; no status upgrade).

Bridge Program - v5_T2 closure restored via Lane L1 (phase stabilization) (2026-02-05): Added a pinned tolerance-ladder and tightened-profile frontier cycle with design-first decomposition and Lane L1 implementation; post-L1 `v5_t2` closure is restored under the existing 17-probe frontier with negative controls preserved (bounded/report-only; no status upgrade).
- Context: `baseline` / `v5_t1` / `v5_t2` tolerance profiles are pinned and evaluated under the same bridge-program orthogonality surface.
- Pre-L1 tight-tolerance break (historical, pinned in design package): `mismatch_phase_and_pair`, `n_mismatch=13`, with flipped probes documented in:
  - `formal/quarantine/bridge_tickets/BRIDGE_TICKET_T2_0001_phase_and_pair_tight_tol_design.md`
  - `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json`
  - `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_CAUSALITY_CLASSIFIER.md`
  - `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_LANE_PLAN.md`
- Implementation ticket (Lane L1 only):
  - `formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0005_c6_phase_stabilized_t2.md`
- Lane L1 implementation:
  - Phasor-stabilized phase residual applied to Toy-H phase/phase-anchor evaluation path.
  - Profile-gated activation: enabled only when `tolerance_profile == "v5_t2"`.
  - No tolerance-profile values changed; no schema changes; probe set remains 17.
- Post-L1 closure evidence (current artifacts):
  - `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT_v5_T2.json` (`n_mismatch=0`)
  - `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY_v5_T2.json` (`recommended_next_target.reason_code="none"`)
  - `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_TOLERANCE_TIGHTENING_DELTA_MANIFEST.json` (`baseline/v5_t1/v5_t2` all report `n_mismatch=0`)
- Test evidence (post-L1):
  - `formal/python/tests/test_bridge_toyh_phase_stabilization_unit.py`
  - `formal/python/tests/test_bridge_program_v5_t2_phase_stabilized_lane_l1.py`
  - Focused suite: `.\py.ps1 -m pytest formal/python/tests -k "bridge or state_theory_dag"` -> `143 passed, 410 deselected`
- Next: canonical-surface diversification feasibility scan (design-only first; preserve current lock/admissibility discipline).

Canonical diversification comparator-class checkpoint (2026-02-05): Design cycle accepted/frozen under blocker resolution family `R5` (UCFF classified as non-grid canonical; comparator taxonomy expanded with a UCFF-first dispersion lane; no implementation ticket minted in this cycle). C7/MT-01a remains explicitly deferred in this lane; C8 remains secondary blocker only (bounded/report-only; no status upgrade).
- Primary blocker acceptance evidence:
  - `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_BLOCKER_0002_phase_action_grid_surface.md`
  - `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_DIVERSIFY_0002_grid_shaped_target_discovery.md`
- Comparator-class design freeze:
  - `formal/quarantine/bridge_tickets/BRIDGE_TICKET_COMPARATOR_CLASS_0001_dispersion_lane_ucff.md`
  - Branch checkpoint: `design/canonical-surface-scan` @ `eff4e2d`
- Pinned feasibility artifacts:
  - `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json` (`sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`)
  - `formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json` (`sha256=81dc9cd60549861906b02b420c82c0225c794302f40d8d5c6aedf714578236a1`)
- Scheduling note: implementation is explicitly deferred; future work may mint `BRIDGE_TICKET_COMPARATOR_CLASS_IMPL_0001_dispersion_lane_ucff` only after explicit authorization.

Bridge attempts (bounded; falsifiable; structural-only)
- BRIDGE_TICKET_0001 (C6↔UCFF dispersion square): formal/quarantine/bridge_tickets/BRIDGE_TICKET_0001_c6_ucff_dispersion_square.md
	Evidence: formal/python/tests/test_bridge_c6_ucff_dispersion_square.py
- BRIDGE_TICKET_0002 (OV-BR-05↔UCFF low-k slope compatibility): formal/quarantine/bridge_tickets/BRIDGE_TICKET_0002_br05_ucff_lowk_slope.md
	Evidence: formal/python/tests/test_bridge_br05_ucff_lowk_slope.py
- BRIDGE_TICKET_0003 (BRIDGE_TICKET_0002 guard: robustness + falsification): formal/quarantine/bridge_tickets/BRIDGE_TICKET_0003_br05_ucff_lowk_slope_robustness.md
	Evidence: formal/python/tests/test_bridge_br05_ucff_lowk_slope_robustness.py
- BRIDGE_TICKET_0004 (BR-04 low-k window ↔ UCFF curvature/convexity constraint): formal/quarantine/bridge_tickets/BRIDGE_TICKET_0004_br05_ucff_lowk_curvature.md
	Evidence: formal/python/tests/test_bridge_br05_ucff_lowk_curvature.py
- BRIDGE_TICKET_TOYH_0001 (C6 phase invariance ↔ Toy-H gauge redundancy): formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0001_c6_phase_invariance.md
	Evidence: formal/python/tests/test_bridge_toyh_c6_phase_invariance.py
	Feasibility: formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_invariance_feasibility.json
- BRIDGE_TICKET_TOYH_0002 (C6 current invariance ↔ Toy-H orthogonal gauge observable): formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0002_c6_current_invariance.md
	Evidence: formal/python/tests/test_bridge_toyh_c6_current_invariance.py
	Feasibility: formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_invariance_feasibility.json
- BRIDGE_TICKET_TOYH_0003 (C6 phase-anchor proxy ↔ Toy-H small-theta gauge observable): formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYH_0003_c6_phase_anchor.md
	Evidence: formal/python/tests/test_bridge_toyh_c6_phase_anchor_determinism.py; formal/python/tests/test_bridge_toyh_c6_phase_anchor_negative_controls.py; formal/python/tests/test_bridge_toyh_c6_phase_anchor_resolution_scan.py; formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_pointers_exist.py
	Feasibility: formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_anchor_feasibility.json
- BRIDGE_FEASIBILITY_TOYG_0001 (Toy-G -> canonical feasibility scan): formal/quarantine/bridge_tickets/BRIDGE_FEASIBILITY_TOYG_0001_canonical_surface_scan.md
	Evidence: formal/python/tests/test_bridge_toyg_canonical_feasibility_scan_determinism.py; formal/python/tests/test_bridge_toyg_canonical_feasibility_artifact_pointers_exist.py
	Feasibility: formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json
- BRIDGE_TICKET_TOYG_0001 (C6 phase-winding quantization proxy ↔ Toy-G discreteness observable): formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYG_0001_c6_phase_winding_quantization.md
	Evidence: formal/python/tests/test_bridge_toyg_c6_phase_winding_determinism.py; formal/python/tests/test_bridge_toyg_c6_phase_winding_perturbation_stability.py; formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py; formal/python/tests/test_bridge_toyg_c6_phase_winding_resolution_scan.py
	Feasibility: formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json
- BRIDGE_TICKET_TOYG_0002 (C6 mode-index quantization proxy ↔ Toy-G discreteness observable): formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYG_0002_c6_mode_index_quantization.md
	Evidence: formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_determinism.py; formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_perturbation_stability.py; formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_negative_controls.py; formal/python/tests/test_bridge_toyg_c6_mode_index_quantization_resolution_scan.py; formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist.py
	Feasibility: formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json
- BRIDGE_TICKET_TOYG_0003 (C6 unwrap-stability proxy ↔ Toy-G boundary-sensitive observable): formal/quarantine/bridge_tickets/BRIDGE_TICKET_TOYG_0003_c6_unwrap_stability.md
	Evidence: formal/python/tests/test_bridge_toyg_c6_unwrap_stability_determinism.py; formal/python/tests/test_bridge_toyg_c6_unwrap_stability_perturbation_stability.py; formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py; formal/python/tests/test_bridge_toyg_c6_unwrap_stability_resolution_scan.py; formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist.py
	Feasibility: formal/quarantine/feasibility/BRIDGE_TOYG_C6_unwrap_stability_feasibility.json

Bridge ledger (bounded evidence surface; bookkeeping)
- formal/quarantine/bridge_tickets/BRIDGE_LEDGER.json
	Evidence: formal/python/tests/test_bridge_ledger_generate_determinism.py; formal/python/tests/test_bridge_ledger_evidence_pointers_exist.py

Bridge boundary report (bounded domain scan; bookkeeping)
- formal/quarantine/bridge_tickets/BRIDGE_BOUNDARY_REPORT.json
	Evidence: formal/python/tests/test_bridge_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_boundary_report_evidence_pointers_exist.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_phase_invariance_BOUNDARY_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyh_c6_phase_invariance_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyh_c6_phase_invariance_boundary_report_pointers_exist.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_invariance_BOUNDARY_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyh_c6_current_invariance_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyh_c6_current_invariance_boundary_report_pointers_exist.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_phase_anchor_BOUNDARY_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyh_c6_phase_anchor_boundary_report_pointers_exist.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyh_c6_orthogonality_report_generate_determinism.py; formal/python/tests/test_bridge_toyh_c6_orthogonality_report_pointers_exist.py; formal/python/tests/test_bridge_toyh_c6_orthogonality_independence.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_MISMATCH_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_report_generate_determinism.py; formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_report_pointers_exist.py; formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_semantics.py; formal/python/tests/test_bridge_toyh_c6_orthogonality_robustness_guard.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_phase_winding_BOUNDARY_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyg_c6_phase_winding_boundary_report_pointers_exist.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_mode_index_BOUNDARY_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyg_c6_mode_index_boundary_report_pointers_exist.py
- formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_unwrap_stability_BOUNDARY_REPORT.json
	Evidence: formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_generate_determinism.py; formal/python/tests/test_bridge_toyg_c6_unwrap_stability_boundary_report_pointers_exist.py
- formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json
	Evidence: formal/python/tests/test_bridge_program_orthogonality_report_generate_determinism.py; formal/python/tests/test_bridge_program_orthogonality_report_pointers_exist.py; formal/python/tests/test_bridge_program_orthogonality_semantics.py; formal/python/tests/test_bridge_program_orthogonality_robustness_guard.py
- formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json
	Evidence: formal/python/tests/test_bridge_program_orthogonality_mismatch_report_generate_determinism.py; formal/python/tests/test_bridge_program_orthogonality_mismatch_report_pointers_exist.py; formal/python/tests/test_bridge_program_orthogonality_mismatch_semantics.py
- formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json
	Evidence: formal/python/tests/test_bridge_program_mismatch_reason_summary_determinism.py; formal/python/tests/test_bridge_program_post_toyg0002_regression_lock.py; formal/python/tests/test_bridge_program_post_toyh0003_regression_lock.py; formal/python/tests/test_bridge_toyg_c6_mode_index_resolution_regression_lock.py; formal/python/tests/test_bridge_toyg_c6_unwrap_resolution_regression_lock.py

Bridge admissibility manifest (pinned inputs/grids/evidence; bookkeeping)
- formal/quarantine/bridge_tickets/BRIDGE_ADMISSIBILITY_MANIFEST.json
	Evidence: formal/python/tests/test_bridge_admissibility_manifest_generate_determinism.py; formal/python/tests/test_bridge_admissibility_manifest_pointers_exist.py

Toy substrate laws (consequence-engine lane)
- TOY viability flow ledger: formal/quarantine/toy_laws/TOY_LAW_LEDGER.json
	What it is: bounded evidence ledger for toy viability flow.
	Regenerate: .\py.ps1 -m formal.python.tools.toy_law_ledger_generate --out formal/quarantine/toy_laws/TOY_LAW_LEDGER.json
	Evidence: pytest nodes listed in ledger (bounded_multi).
	Governance: consequence-engine only; no physics claim; ledger is reportable evidence surface.
	Admissibility is defined by bounded pytest evidence nodes; front doors are report-only.
- Pinned Family F report artifact: formal/output/toy_stochastic_selection_report_F1_pinned.json (generated by .\py.ps1 -m formal.python.tools.toy_stochastic_selection_report_generate --out formal/output/toy_stochastic_selection_report_F1_pinned.json; bounded evidence only).
- Pinned Family G report artifact: formal/output/toy_topological_invariants_report_G1_pinned.json (generated by .\py.ps1 -m formal.python.tools.toy_topological_invariants_report_generate --out formal/output/toy_topological_invariants_report_G1_pinned.json; bounded evidence only).
- Pinned Family H report artifact: formal/output/toy_gauge_redundancy_report_H1_pinned.json (generated by .\py.ps1 -m formal.python.tools.toy_gauge_redundancy_report_generate --out formal/output/toy_gauge_redundancy_report_H1_pinned.json; bounded evidence only).
- Pinned Family H2 report artifact: formal/output/toy_gauge_redundancy_report_H2_pinned.json (generated by .\py.ps1 -m formal.python.tools.toy_gauge_redundancy_report_generate --candidate-id H2_local_phase_gauge --out formal/output/toy_gauge_redundancy_report_H2_pinned.json; bounded evidence only).
- TOY coherence transport front door + bounded tests: see formal/quarantine/toy_laws/TOY_LAW_LEDGER.json
- TOY topological invariants front door + bounded tests: see formal/quarantine/toy_laws/TOY_LAW_LEDGER.json
- TOY gauge redundancy front door + bounded tests: see formal/quarantine/toy_laws/TOY_LAW_LEDGER.json

Repo hygiene baselines (non-git snapshots):
Pipeline baseline pointer: formal/tooling_snapshots/LATEST_BASELINE_PIPELINE.txt
Evidence baseline pointer: formal/tooling_snapshots/LATEST_BASELINE_EVIDENCE.txt

Governance methodology paper: COMPLETE — externalized (publication track)

Legacy reincorporation (bookkeeping)
- Register: Legacy_Reintegration_Register.md
- Latest triage artifacts: formal/output/legacy_archive_triage_20260201_130457_477894.md; formal/output/legacy_archive_triage_20260201_130457_477894.json


LEGACY QUARANTINE INDEX (GOVERNANCE; DOCS-ONLY)

Rule: Items under archive/ are reference-only by default and are non-authoritative; reintegration requires new front-door observables/tools with explicit typed input artifacts, fingerprinted outputs, and pytest/lock enforcement. Do not import/archive-execute legacy Python modules.

Entry points:
- Legacy reintegration register: Legacy_Reintegration_Register.md
- Latest archive triage report (md): formal/output/legacy_archive_triage_20260201_130457_477894.md
- Latest archive triage report (json): formal/output/legacy_archive_triage_20260201_130457_477894.json






HOW TO READ THIS DOCUMENT



This file is the single source of truth for the epistemic status of all major theory components.



This file does NOT:



Argue correctness

Prove results

Justify interpretation



This file ONLY records:



What exists

What it claims

How confident we are

Why that confidence level is assigned



If an item is unclear, it is marked Hypothesis by default.





STATUS LEGEND (CANONICAL)



Use ONLY the following status labels.



Locked

Behavior validated and structure formalized.



Structural (Lean)

Formally consistent definitions or identities. No behavioral claim.



Behavioral (Python)

Numerically observed behavior. No structural guarantee.



Spec-backed

Assumed bridge or interpretation. Explicitly labeled.



Hypothesis

Proposed but not validated or formalized.



Deprecated

Superseded, unused, or intentionally abandoned.



Empirically Anchored

Matched to external experimental data with repeatable quantitative agreement under a declared, test-gated pipeline.

Evidence must cite external experiments.

Operational meaning (scope guardrail)

This status records that a claim has repeatable quantitative support under a declared, test-gated pipeline using declared external evidence (citations + frozen artifacts/fingerprints where applicable). It does NOT, by itself, assert that any specific physical interpretation is established; interpretation bridges must be recorded separately (e.g., Hypothesis / Spec-backed) and may be wrong even if the operational match is stable.



Derived-from-Established-Physics

Formally derived as a limit, reduction, or reformulation of an accepted

physical theory (e.g., GrossPitaevskii, Maxwell, NavierStokes).



Open-to-Test

Physically interpretable with clearly defined observables, but not yet

tested or matched to data.



Experimentally Refuted

Shown to disagree with experiment in its claimed domain.



These statuses may only be assigned in State\_of\_the\_Theory.md and must cite evidence external to the repository.





GLOBAL CONSTRAINTS



No item may appear in Lean unless it appears in this file.

No item may be upgraded in status without updating this file.

All Markdown claims must reference an item defined here.



External epistemic statuses record correspondence to physical reality.

They are never established by Markdown, Python, or Lean artifacts and must

be supported by evidence outside this repository.



Canonical inventory IDs (e.g., CT-01, DR-01) may not be reused as IDs for

evidence sections. Evidence blocks must use derived IDs (e.g., CT-01-EVIDENCE-\*).



Dependencies field MUST reference only inventory IDs (or None). No free text or external references.

Evidence field may contain (a) derived evidence-block IDs or (b) repository file paths.



Evidence blocks are bookkeeping artifacts, not claims.

For evidence blocks, Status indicates artifact modality (e.g., Behavioral (Python), Structural (Lean), Deprecated) and does not assert any external epistemic status.

External epistemic statuses (e.g., Empirically Anchored) apply only to inventory claim items, not to evidence blocks.





INVENTORY ENTRY FORMAT (CANONICAL)



Each epistemic object MUST be recorded using the following format.

Do not deviate.



ID:

Name:

Category:

Short description:

Status:

LEAN GATE ENABLEMENT POLICY (CANONICAL)

Some downstream observables (e.g., cross-lane comparability audits) are explicitly gated by admissibility predicates (e.g., CT01 / SYM01 / CAUS01).

Policy:

- Lean is the source of truth for gate definitions and for the repository-declared enablement intent.
- Gates are disabled-by-default unless explicitly enabled by a deliberate action aligned with Lean intent.
- The generated admissibility manifest is an enforcement artifact; it must not be edited to silently enable gates.
- Enabling a gate requires an explicit allow-enable step in the manifest updater (disabling is always permitted).

Operational effect:

- If required gates are disabled, affected observables must report `blocked` and must not compute cross-lane comparison rows.

Enforcement artifact:

- `formal/markdown locks/gates/admissibility_manifest.json`
- `formal/python/tests/tools/update_admissibility_manifest.py`



Evidence:

Scope / limits:

Dependencies:

Notes:

External anchor:

External evidence:





PLANNED VIABILITY MILESTONES (ROADMAP ONLY; UNEXECUTED)



This section is planning-only.

Guardrails (non-negotiable):

- No item in this section creates a lock.
- Nothing in this section alters gate enablement, admissibility pruning, or enforcement logic.
- Interpretive mappings in this section are Spec-backed and must not feed back into FN pruning.
- Status labels here record intent only; they do not promote any inventory entry.
- No empirical validation performed.



GapID: COMP-PRED-FALS
Layer: Governance
Item: At least one unique falsifier/prediction path
Status: In progress (at least one explicit FAIL-mode lane now recorded; additional lanes encouraged)
Owner ticket/module: State_of_the_Theory.md
Evidence path: State_of_the_Theory.md; formal/python/tests/test_phaseB_dispersion_preservation_expanded.py; formal/python/tests/test_phaseB_solver_omega_shift.py; formal/python/tests/test_sym01_phase_violation_lane.py; formal/python/tests/test_bc01_boundary_mismatch_lane.py; formal/python/tests/test_tr01_par01_symmetry_violation_lane.py; formal/python/tests/test_en01_energy_monotonicity_lane.py; formal/python/tests/test_st01_soliton_shape_preservation_lane.py; formal/python/tests/test_tg01_trapped_ground_state_lane.py; formal/python/tests/test_st01_soliton_resolution_convergence_lane.py; formal/output/PTC_NLSE_V1_HOOKS.json; formal/output/PTC_NLSE_V1_HOOKS_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_REPORT_SOLITON.json; formal/output/PTC_NLSE_V1_REPORT_SOLITON_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_HOOKS_SOLITON.json; formal/output/PTC_NLSE_V1_HOOKS_SOLITON_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_REPORT_TRAP.json; formal/output/PTC_NLSE_V1_REPORT_TRAP_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_HOOKS_TRAP.json; formal/output/PTC_NLSE_V1_HOOKS_TRAP_DISSIPATIVE.json; formal/python/toe/comparators/cv01_bec_bragg_v0.py; formal/python/tests/test_cv01_bec_bragg_v0_front_door.py; formal/python/tests/test_cv01_bec_bragg_v0_surface_contract_freeze.py; formal/python/tests/test_cv01_v1_discriminative_design_gate_doc.py; formal/docs/cv01_bec_bragg_v0_front_door_contract.md; formal/docs/cv01_v1_discriminative_design_gate.md; formal/docs/first_empirical_comparator_domain_bec_bragg.md; formal/python/tests/test_first_empirical_comparator_domain_selection.py; formal/python/toe/comparators/cv01_bec_bragg_v1.py; formal/python/tests/test_cv01_bec_bragg_v1_front_door.py; formal/python/tests/test_cv01_bec_bragg_v1_surface_contract_freeze.py; formal/python/tests/test_cv01_numeric_tolerance_policy_doc.py; formal/docs/cv01_bec_bragg_v1_front_door_contract.md; formal/docs/cv01_numeric_tolerance_policy.md; formal/python/toe/observables/ovcvbr01_cv01_v1_pruning_bridge_record.py; formal/python/toe/observables/cv01_v1_pruning_reason_policy.json; formal/python/tests/test_ov_cv_br01_cv01_v1_pruning_bridge_lock.py; formal/python/tests/test_ov_cv_br01_cv01_v1_elimination_attribution.py; formal/python/tests/test_cv01_v1_pruning_reason_policy.py; formal/markdown/locks/observables/OV-CV-BR-01_cv01_v1_pruning_bridge.md; formal/markdown/locks/observables/OV-CV-BR-01_cv01_v1_pruning_bridge_NEG_CONTROL.md; formal/docs/second_empirical_comparator_domain_bec_bragg_b1.md; formal/python/tests/test_second_empirical_comparator_domain_selection.py; formal/python/toe/comparators/cv02_bec_bragg_b1_v0.py; formal/python/tests/test_cv02_bec_bragg_b1_v0_front_door.py; formal/python/tests/test_cv02_bec_bragg_b1_v0_surface_contract_freeze.py
Exit criteria: At least one lane with a real FAIL mode (not only unknown), or a pinned justification for why unknown is acceptable in that lane.
Notes: CT-01 probe/dispersion and solver-level ω-shift lanes are front-door-backed on pinned PTC cases (including conservative baseline, dissipative break case, and conservative amplitude/coupling/k variants). SYM01/PAR01/BC01 are now front-door-backed via deterministic B1 hooks artifacts (phase/pass + conjugation/fail, parity/pass + advection/fail, periodic-vs-Dirichlet boundary residuals). TR01 is report-backed via `time_reversal_error`; EN01 is report-backed via regime-specific `energy_delta` behavior. ST01 is front-door-backed via pinned bright-soliton cases and report shape metrics (`shape_residual`, `shape_peak_delta`, `shape_peak_ratio`) and now includes an n64 -> n128 resolution/convergence lane as a numerical adequacy check. TG01 is front-door-backed via pinned harmonic-trap ground-state cases and report trap metrics (`trap_shape_residual`, `trap_peak_ratio`, `trap_m2_delta`). OV-CV-01 is now dual-lane on typed DR-01 artifacts: v0 integrity-only front-door records, and v1 discriminative-candidate records with non-tautological cross-artifact speed residual (`abs(c_s-c0)`), profile-scoped tolerances, and deterministic negative controls. OV-CV-BR-01 adds explicit CV01 reason-code to pruning-atom mapping with deterministic lock records (canonical + negative-control) and attribution tests. OV-CV-02 pins a second comparator domain lane (`DRBR-DOMAIN-02`) with integrity-only front-door checks and deterministic blocked/negative-control behavior.
Falsifier/comparator families: dispersion/probe (CT01), solver consequence (ω-shift), symmetry (SYM01, PAR01, TR01), boundary handling (BC01), conservation/monotonicity (EN01), soliton structure/shape preservation plus resolution/convergence adequacy (ST01), trapped ground-state structure/shape stability under harmonic confinement (TG01), BEC-Bragg comparator lanes (OV-CV-01 v0 integrity + v1 discriminative-candidate), explicit CV01-to-pruning bridge lane (OV-CV-BR-01), and second-domain comparator lane (OV-CV-02).
EN01 regime note: the FAIL case corresponds to a dissipative regime, not a universal “wrongness” claim; conservative vs. dissipative admissibility is now tracked as a named regime class.
ST01 regime note: PASS corresponds to conservative-regime shape stability under the pinned v1 soliton run; FAIL corresponds to dissipative damping with measurable shape degradation.
ST01 resolution note: the n64 -> n128 convergence lane is a pinned numerical adequacy check on the benchmark surface, not a universal physical claim.
TG01 regime note: PASS corresponds to conservative trapped-state shape stability under pinned harmonic confinement; FAIL corresponds to dissipative damping with measurable trap-shape degradation.
OV-CV-01 role note: v0 remains integrity-only (`comparator_role=integrity_only`); v1 is a discriminative-candidate lane (`comparator_role=discriminative_candidate`) with cross-artifact residual checks under declared pinned/portable tolerance profiles and no external truth-claim upgrade.
OV-CV-BR-01 coupling note: BR pruning does not consume CV01 implicitly; coupling is explicit via policy mapping (`cv01_v1_pruning_reason_policy.json`) and lock-tested bridge records only.
OV-CV-02 scope note: Domain-02 lane is pinned as integrity-only (`DRBR-DOMAIN-02`) and does not upgrade external truth posture.

GapID: PTC-NLSE-V1
Layer: Physics Execution
Item: NLSE-like Physics Target Contract v1 front door
Status: Implemented (deterministic front door + pinned manifest + locked conservative/dissipative outputs; now includes plane-wave + bright-soliton benchmark locks, trapped-ground-state benchmark locks (TG01), and ST01 shape-preservation + resolution/convergence lanes)
Owner ticket/module: formal/python/tools/ptc_nlse_v1_run.py
Evidence path: formal/quarantine/physics_target/PTC_NLSE_V1_MANIFEST.json; formal/python/tools/ptc_nlse_v1_run.py; formal/output/PTC_NLSE_V1_REPORT.json; formal/output/PTC_NLSE_V1_REPORT_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_HOOKS.json; formal/output/PTC_NLSE_V1_HOOKS_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_REPORT_SOLITON.json; formal/output/PTC_NLSE_V1_REPORT_SOLITON_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_HOOKS_SOLITON.json; formal/output/PTC_NLSE_V1_HOOKS_SOLITON_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_REPORT_TRAP.json; formal/output/PTC_NLSE_V1_REPORT_TRAP_DISSIPATIVE.json; formal/output/PTC_NLSE_V1_HOOKS_TRAP.json; formal/output/PTC_NLSE_V1_HOOKS_TRAP_DISSIPATIVE.json; formal/python/tests/test_ptc_nlse_v1_front_door_determinism.py; formal/python/tests/test_st01_soliton_shape_preservation_lane.py; formal/python/tests/test_st01_soliton_resolution_convergence_lane.py; formal/python/tests/test_tg01_trapped_ground_state_lane.py
Exit criteria: Deterministic report generation under pinned inputs; regime-specific energy behavior (conservative ~ invariant, dissipative monotone) validated via tests.
Notes: v1 surface is 1D periodic NLSE-like dynamics with cubic nonlinearity and optional damping; intended as the first executable physics target contract (not a proof of physical correctness). Report outputs include `time_reversal_error` in addition to dispersion/energy/norm/phase diagnostics. Policy B1 hooks are emitted as separate deterministic artifacts (`PTC_NLSE_V1_HOOKS*.json`) for SYM01/PAR01/BC01 so report schema remains stable while falsifier lanes stay front-door-driven. Manifest now includes plane-wave contract cases, bright-soliton benchmark cases, and harmonic-trap ground-state benchmark cases; soliton IC is keyed by case_id substring ('soliton') and reports shape metrics (`shape_residual`, `shape_peak_delta`, `shape_peak_ratio`). Trap cases are keyed by `V_kind="harmonic"` and report trap metrics (`trap_shape_residual`, `trap_peak_ratio`, `trap_m2_delta`). ST01 now includes a pinned n64 vs n128 resolution/convergence check as a numerical adequacy lane.

Planned Structural Validations (Unexecuted)

- Reduction target: FN core dynamics → NLS/GPE under limits (λ→0, β→0, ρ→ρ₀)
	Status: Hypothesis
	Planned evidence: Lean limit proof (unwritten)
	Notes: Planning target only; not asserted as a result.

- Noether quantities from declared Lagrangian forms
	Status: Hypothesis
	Planned evidence: Lean derivation + invariant export lemma(s) (unwritten)



Planned Constraint + Verification Extensions (Unexecuted)

- FN02_DispersionAdditivity (planned)
	Status: Hypothesis
	Role: Structural filter over FN-01 candidate set (additive closure / compatibility)
	Notes: Placeholder name; does not create an FN inventory ID yet.

- Invariance regression battery expansion (phase/translation/rotation)
	Status: Hypothesis
	Role: Behavioral (Python) evidence only; no structural promotion implied.

- Observability / representation-invariance audit (OV-OBS-01)
	Status: Hypothesis
	Role: Behavioral (Python) hygiene guardrail: observable outputs must be invariant under metadata-only perturbations.
	Evidence: formal/python/toe/observables/ovobs01_observability_metadata_invariance.py; formal/python/tests/test_ovobs01_metadata_invariance.py
	Notes: Operationalizes “wavefunction/state unknowability” as an engineering constraint (no dependence on unobservable provenance strings).

- Graph/Fourier mode consistency audit (OV-FG-01)
	Status: Hypothesis
	Role: Behavioral (Python) internal consistency scaffold (continuum Fourier reasoning vs discrete graph Laplacian modes).
	Evidence: formal/python/toe/observables/ovfg01_graph_fourier_mode_audit.py; formal/python/tests/test_ovfg01_graph_fourier_mode_audit.py
	Notes: Not an external anchor; used to surface hidden continuum-limit assumptions.

- Many-body orthogonality catastrophe trend audit (OV-MB-01)
	Status: Hypothesis
	Role: Behavioral (Python) toy-model trend check; does not constitute empirical anchoring.
	Evidence: formal/python/toe/observables/ovmb01_orthogonality_catastrophe_audit.py; formal/python/tests/test_ovmb01_orthogonality_trend.py
	Notes: Tight-binding ring + single-site impurity; validates overlap trend only.

- Phase-transition window detector (OV-PT-01)
	Status: Hypothesis
	Role: Behavioral (Python) audit mechanism for hexatic-style two-step transitions on supplied data.
	Evidence: formal/python/toe/observables/ovpt01_phase_transition_window_audit.py; formal/python/tests/test_ovpt01_hexatic_window_detector.py
	Notes: Does not simulate melting; detects the signature window in provided order-parameter curves.

- Quantum geometry (Berry/Chern) audit scaffold (OV-QC-01)
	Status: Hypothesis
	Role: Behavioral (Python) computational primitive for Berry curvature / Chern number checks in simplified lattice models.
	Evidence: formal/python/toe/observables/ovqc01_berry_curvature_audit.py; formal/python/tests/test_ovqc01_chern_number_qiwuzhang.py
	Notes: Not an EWT claim; a reusable audit primitive for future bridge models.

- Brain–ZPF resonance overlap scaffold (OV-ZPF-01)
	Status: Hypothesis
	Role: Behavioral (Python) quarantine-safe audit scaffold: records frequency-band overlap geometry only (no coupling/feasibility claim).
	Evidence: formal/python/toe/observables/ovzpf01_brain_zpf_resonance_audit.py; formal/python/tests/test_ovzpf01_brain_zpf_resonance.py
	Notes: Synthetic/demo inputs by default; intended as a front-door quantitative harness for any future revalidation work.

- UCFF jitter-structure audit scaffold (OV-UCFF-01)
	Status: Hypothesis
	Role: Behavioral (Python) low-risk audit scaffold: symbolic term-presence checks plus a bounded numeric non-negativity scan for a UCFF-like ω²(k) polynomial under small parameter jitter.
	Evidence: formal/python/toe/observables/ovucff01_jitter_structure_audit.py; formal/python/tests/test_ovucff01_jitter_structure_audit.py
	Notes: Demonstration-only; not an empirical anchor and not a physics claim. Provides a disciplined front-door harness for reincorporating legacy UCFF symbolic structure work.

- UCFF core front door (non-archive)
	Status: Hypothesis
	Role: Behavioral (Python) minimal typed-input, deterministic-output front door for UCFF-like dispersion bookkeeping (no implicit I/O; no archive imports).
	Evidence: formal/python/toe/ucff/core_front_door.py; formal/python/tests/test_ucff_core_front_door_roundtrip.py; formal/python/tests/test_ucff_core_front_door_symbolic_invariant_01.py; formal/python/tests/test_ucff_core_front_door_symbolic_invariant_02.py; formal/docs/ucff_core_front_door_contract.md
	Notes: Governance primitive only; enables clean-room porting of legacy UCFF core invariants against a non-archive surface. Bounded symbolic-family evidence is recorded via pytest nodes in the listed tests.

- Framewise cross-variation audit scaffold (OV-UCFF-02)
	Status: Hypothesis
	Role: Behavioral (Python) numeric-only audit: summarizes frame-to-frame variation in a supplied (frames × bins) matrix, including a normalized outer-product cross-variation score.
	Evidence: formal/python/toe/observables/ovucff02_framewise_variation_audit.py; formal/python/tests/test_ovucff02_framewise_variation_audit.py
	Notes: Demonstration-only; intended as a safe front-door harness for any future pinned legacy "framewise cross-variation" artifacts.

- Band energy distribution audit scaffold (OV-UCFF-03)
	Status: Hypothesis
	Role: Behavioral (Python) numeric-only audit: summarizes rFFT band energy distribution across frames and reports shape metrics (entropy/flatness/slope) for traceable comparisons.
	Evidence: formal/python/toe/observables/ovucff03_band_energy_distribution_audit.py; formal/python/tests/test_ovucff03_band_energy_distribution_audit.py
	Notes: Bookkeeping only; supports a pinned legacy-derived internal input artifact for deterministic re-porting.

- Band energy tolerance audit scaffold (OV-UCFF-03B)
	Status: Hypothesis
	Role: Behavioral (Python) numeric-only audit: recomputes the OV-UCFF-03 spectral fingerprint on pinned input and compares it against a pinned reference report under numeric tolerances, emitting PASS/FAIL plus error metrics.
	Evidence: formal/python/toe/observables/ovucff03b_band_energy_tolerance_audit.py; formal/python/tests/test_ovucff03b_band_energy_tolerance_audit.py
	Notes: Bookkeeping only; reference is an internal frozen report (not external evidence) intended to preserve legacy-compatible continuity across refactors.

- Spectral evolution audit scaffold (OV-UCFF-04)
	Status: Hypothesis
	Role: Behavioral (Python) numeric-only audit: computes per-frame rFFT band-energy distributions and summarizes adjacent-frame spectral drift (L2 / cosine distance / Jensen–Shannon divergence) plus time-differenced shape scalars (entropy/slope).
	Evidence: formal/python/toe/observables/ovucff04_spectral_evolution_audit.py; formal/python/tests/test_ovucff04_spectral_evolution_audit.py
	Notes: Bookkeeping only; supports a pinned legacy-derived internal input artifact for deterministic re-porting.

- Temporal band modulation audit scaffold (OV-UCFF-05)
	Status: Hypothesis
	Role: Behavioral (Python) numeric-only audit: builds per-band energy time series and summarizes temporal modulation (per-band mean/std/CV, mean abs delta, dominant temporal harmonic via rFFT over time) plus a simple cross-band correlation coherence summary.
	Evidence: formal/python/toe/observables/ovucff05_temporal_band_modulation_audit.py; formal/python/tests/test_ovucff05_temporal_band_modulation_audit.py
	Notes: Bookkeeping only; supports a pinned legacy-derived internal input sequence (deterministically derived from the Phase-51 2-frame fixture) for deterministic re-porting.

- Temporal spectral entropy trends audit scaffold (OV-UCFF-06)
	Status: Hypothesis
	Role: Behavioral (Python) numeric-only audit: computes per-frame normalized band-energy entropy (0..1) and summarizes entropy trend behavior across time (mean/min/max, mean abs delta, linear slope vs time).
	Evidence: formal/python/toe/observables/ovucff06_temporal_spectral_entropy_trends_audit.py; formal/python/tests/test_ovucff06_temporal_spectral_entropy_trends_audit.py
	Notes: Bookkeeping only; supports a pinned legacy-derived internal input sequence (carried forward from OV-UCFF-05) for deterministic re-porting.

- Cross-metric coupling audit scaffold (OV-UCFF-07)
	Status: Hypothesis
	Role: Behavioral (Python) numeric-only audit: computes deterministic coupling metrics between spectral entropy time series and spectral band-fraction modulation/drift (per-band correlations, entropy–modulation correlations, and lag-scan coupling).
	Evidence: formal/python/toe/observables/ovucff07_cross_metric_coupling_audit.py; formal/python/tests/test_ovucff07_cross_metric_coupling_audit.py
	Notes: Bookkeeping only; intended to connect standalone UCFF spectral monitors (entropy/modulation/drift) into cross-dimensional comparability signals without asserting any physical interpretation.



Interpretability Dictionary (Non-binding; Spec-backed)

- MAP-01 is recorded in the inventory as Spec-backed. It is an interpretive aid only.



Proxy Falsifiability Pressure (Non-binding)

- EMP-01 is recorded in the inventory as a Hypothesis proxy claim.




RECENT SCIENTIFIC FINDINGS — INTEGRATION TRIAGE (2026-02-01)

This section records intake decisions for external synthesis items.

- Brain–ZPF resonance proposals: Status Hypothesis; quarantined (no empirical anchoring). Integrated only as OV-ZPF-01 overlap audit scaffold. See evidence: [OV-ZPF-01-EVIDENCE-ARTIFACT](#OV-ZPF-01-EVIDENCE-ARTIFACT).
- Vacuum-resonance unification models: Status Hypothesis; quarantined pending distinct, testable predictions (no curve-fit anchoring accepted).
- Wavefunction/state unknowability: treated as a methodological constraint; operationalized via OV-OBS-01 (metadata invariance guardrail). See evidence: [OV-OBS-01-EVIDENCE-ARTIFACT](#OV-OBS-01-EVIDENCE-ARTIFACT).
- Fourier–graph structural links: treated as internal consistency work; operationalized via OV-FG-01 scaffold. See evidence: [OV-FG-01-EVIDENCE-ARTIFACT](#OV-FG-01-EVIDENCE-ARTIFACT).
- Hexatic melting observations: observationally anchorable externally, but currently integrated only as OV-PT-01 detection tooling (no simulation claim). See evidence: [OV-PT-01-EVIDENCE-ARTIFACT](#OV-PT-01-EVIDENCE-ARTIFACT).
- Fermi polaron / orthogonality catastrophe: integrated only as OV-MB-01 toy trend audit (no empirical anchoring claim). See evidence: [OV-MB-01-EVIDENCE-ARTIFACT](#OV-MB-01-EVIDENCE-ARTIFACT).
- Quantum metric/curvature effects: integrated only as OV-QC-01 audit primitive (no EWT correspondence claim). See evidence: [OV-QC-01-EVIDENCE-ARTIFACT](#OV-QC-01-EVIDENCE-ARTIFACT).
- Neural stochastic cell dynamics: deferred as application-layer target; no new core primitives added here.




INVENTORY





4.1 CORE DYNAMICAL EQUATIONS





ID: EQ-01

Name: CP-NLSE (base)

Category: Equation

Short description: Core nonlinear wave equation

Status: Behavioral (Python)

Evidence: formal/python/crft/cp\_nlse\_2d.py; formal/python/crft/tests/test\_c6\_cp\_nlse\_2d\_dispersion.py

Scope / limits: Weakly nonlinear regime

Dependencies: None

Notes: Linearization used for dispersion analysis

Operational validation ledger (bounded evidence only; no status upgrade): formal/quarantine/validation/CRFT_validation_queue_extended_crft_test_family_v1.json (claim_family=C6_CP_NLSE_2D, evidence_strength=bounded_multi). Protocol: formal/docs/crft_validation_queue_protocol.md.

CRFT surface gating (descriptive): C8 turbulence diagnostics are blocked pending a canonical non-archive front door; see formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json.

CRFT Validation Status (bounded evidence only; no status upgrade): C6 = bounded_multi (CP–NLSE 2D); C7 = bounded_multi (MT-01a); C8 = blocked (see feasibility artifact).

External anchor: None

External evidence: None




<a id="OV-UCFF-03-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-03-EVIDENCE-ARTIFACT

Name: OV-UCFF-03 diagnostic artifact (band energy distribution demo)

Category: Evidence block

Short description: Frozen JSON artifact for the OV-UCFF-03 audit scaffold, recording rFFT band energy distribution summaries on a pinned legacy-derived internal input (if present) plus synthetic regression demos, with an optional locked turbulence-style 3-band (k_low/k_mid) partition for legacy continuity.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-03/ucff_band_energy_distribution.json; formal/python/artifacts/input/OV-UCFF-03/legacy_phase51_coherence_drift_pair_density.json; formal/python/toe/observables/ovucff03_band_energy_distribution_audit.py; formal/python/tools/ovucff03_band_energy_distribution_audit.py

Scope / limits: Bookkeeping only; not external data. Records deterministic spectral band-energy shape metrics; does not assert UCFF physical interpretation.

Dependencies: None

Notes: Intended as a disciplined front-door harness for legacy "energy slope" / "energy spread" style metrics. Includes an opt-in 3-band partition with E_k = |rfft|^2/N^2 and k-threshold masks matching the turbulence diagnostics lock convention. Tighten only via explicit pinned artifacts and tests.

External anchor: None

External evidence: None


<a id="OV-UCFF-03B-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-03B-EVIDENCE-ARTIFACT

Name: OV-UCFF-03B diagnostic artifact (band energy tolerance revalidation)

Category: Evidence block

Short description: Frozen JSON artifact for OV-UCFF-03B, comparing a freshly computed OV-UCFF-03 band-energy distribution report on pinned internal input against a pinned reference OV-UCFF-03 report, emitting numeric error metrics plus a PASS/FAIL consistency result under fixed tolerances.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-03B/ucff_band_energy_tolerance.json; formal/python/artifacts/input/OV-UCFF-03B/reference_ovucff03_pinned_report.json; formal/python/toe/observables/ovucff03b_band_energy_tolerance_audit.py; formal/python/tools/ovucff03b_band_energy_tolerance_audit.py; formal/python/tests/test_ovucff03b_band_energy_tolerance_audit.py

Scope / limits: Bookkeeping only; not external data. PASS/FAIL indicates internal numeric consistency vs a pinned reference report, not empirical validation.

Dependencies: OV-UCFF-03-EVIDENCE-ARTIFACT

Notes: The pinned reference report is extracted from the canonical OV-UCFF-03 diagnostic artifact and then frozen as an internal stability anchor. Tighten only via explicit pinned reference updates accompanied by test and artifact regeneration.

External anchor: None

External evidence: None


<a id="OV-UCFF-04-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-04-EVIDENCE-ARTIFACT

Name: OV-UCFF-04 diagnostic artifact (spectral evolution demo)

Category: Evidence block

Short description: Frozen JSON artifact for OV-UCFF-04, recording adjacent-frame spectral drift metrics computed from per-frame rFFT band-energy distributions on a pinned legacy-derived internal input (if present) plus synthetic demo regressions.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-04/ucff_spectral_evolution.json; formal/python/artifacts/input/OV-UCFF-04/legacy_phase51_coherence_drift_pair_density.json; formal/python/toe/observables/ovucff04_spectral_evolution_audit.py; formal/python/tools/ovucff04_spectral_evolution_audit.py; formal/python/tests/test_ovucff04_spectral_evolution_audit.py

Scope / limits: Bookkeeping only; not external data. Records deterministic spectral-evolution summaries; does not assert UCFF physical interpretation.

Dependencies: None

Notes: Intended as a disciplined front-door harness for legacy "spectral drift" / "spectral evolution" style diagnostics. Includes an opt-in locked turbulence-style 3-band (k_low/k_mid) partition for continuity when k-thresholds are explicitly provided.

External anchor: None

External evidence: None


<a id="OV-UCFF-05-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-05-EVIDENCE-ARTIFACT

Name: OV-UCFF-05 diagnostic artifact (temporal band modulation demo)

Category: Evidence block

Short description: Frozen JSON artifact for OV-UCFF-05, recording temporal modulation summaries of per-band energy time series (dominant temporal harmonics, adjacent deltas, and cross-band correlation) on a pinned legacy-derived internal input sequence (if present) plus synthetic demo regressions.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-05/ucff_temporal_band_modulation.json; formal/python/artifacts/input/OV-UCFF-05/legacy_phase51_coherence_drift_density_sequence.json; formal/python/toe/observables/ovucff05_temporal_band_modulation_audit.py; formal/python/tools/ovucff05_temporal_band_modulation_audit.py; formal/python/tests/test_ovucff05_temporal_band_modulation_audit.py

Scope / limits: Bookkeeping only; not external data. Records deterministic temporal modulation summaries; does not assert UCFF physical interpretation.

Dependencies: None

Notes: Intended as a disciplined front-door harness for legacy temporal-coherence / modulation-window style diagnostics. The pinned input sequence is derived deterministically from a legacy 2-frame fixture to make temporal harmonics measurable without inventing new external evidence.

External anchor: None

External evidence: None


<a id="OV-UCFF-06-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-06-EVIDENCE-ARTIFACT

Name: OV-UCFF-06 diagnostic artifact (temporal spectral entropy trends demo)

Category: Evidence block

Short description: Frozen JSON artifact for OV-UCFF-06, recording temporal summaries of per-frame normalized spectral band-energy entropy (mean/min/max, mean abs delta, linear slope vs time) on a pinned legacy-derived internal input sequence (if present) plus synthetic demo regressions.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-06/ucff_entropy_trends.json; formal/python/artifacts/input/OV-UCFF-06/legacy_phase51_coherence_drift_density_sequence.json; formal/python/toe/observables/ovucff06_temporal_spectral_entropy_trends_audit.py; formal/python/tools/ovucff06_temporal_spectral_entropy_trends_audit.py; formal/python/tests/test_ovucff06_temporal_spectral_entropy_trends_audit.py

Scope / limits: Bookkeeping only; not external data. Records deterministic entropy-trend summaries; does not assert UCFF physical interpretation.

Dependencies: None

Notes: Intended as a disciplined front-door harness for legacy "entropy flow" / "spectral disorder" style time-trend bookkeeping. The pinned input sequence is derived deterministically from the Phase-51 2-frame fixture (via OV-UCFF-05) to enable measurable temporal trends without inventing new external evidence.

External anchor: None

External evidence: None


<a id="OV-UCFF-07-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-07-EVIDENCE-ARTIFACT

Name: OV-UCFF-07 diagnostic artifact (cross-metric coupling demo)

Category: Evidence block

Short description: Frozen JSON artifact for OV-UCFF-07, recording deterministic coupling summaries between spectral entropy time series and spectral band-fraction modulation/drift (per-band correlations, entropy–modulation correlations, and lag-scan coupling) on a pinned legacy-derived internal input sequence (if present) plus synthetic demo regressions.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-07/ucff_cross_metric_coupling.json; formal/python/artifacts/input/OV-UCFF-07/legacy_phase51_coherence_drift_density_sequence.json; formal/python/toe/observables/ovucff07_cross_metric_coupling_audit.py; formal/python/tools/ovucff07_cross_metric_coupling_audit.py; formal/python/tests/test_ovucff07_cross_metric_coupling_audit.py

Scope / limits: Bookkeeping only; not external data. Records deterministic cross-metric coupling summaries; does not assert UCFF physical interpretation.

Dependencies: OV-UCFF-05-EVIDENCE-ARTIFACT, OV-UCFF-06-EVIDENCE-ARTIFACT

Notes: Intended as a low-risk bridge from standalone trend monitors to cross-dimensional pattern recognition primitives (correlation and lag coupling only; no causal claims). Tighten only via explicit pinned artifacts and tests. Lock: formal/markdown locks/constraints/LOCK_UCFF_PHASE51_SPECTRAL_DYNAMICS.md

External anchor: None

External evidence: None


ID: EQ-02

Name: CP-NLSE (linearized)

Category: Equation
Short description: Small-amplitude limit of CP-NLSE
Status: Locked

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/LinearizedEquation.lean; formal/python/tests/test\_dr01\_eq02\_dispersion.py; EQ-02-EVIDENCE-LEAN-BUILD

Scope / limits: small-amplitude (linearized) regime about ψ=0

Dependencies: EQ-01

Notes: Lean evidence is restricted to a dedicated EQ-02 definition module (LinearizedEquation.lean). Plane-wave reductions live under OP-PW-\*.

External anchor: None

External evidence: None



ID: EQ-02-EVIDENCE-LEAN-BUILD

Name: EQ-02 Lean build target (bookkeeping)

Category: Evidence block

Short description: Bookkeeping record of the intended Lean module build target for EQ-02.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/LinearizedEquation.lean

Scope / limits: Records build-target intent only; does not include build logs.

Dependencies: None

Notes: Intended build target: ToeFormal.CPNLSE2D.LinearizedEquation.

External anchor: None

External evidence: None





4.2 DISPERSION RELATIONS





ID: DR-01

Name: CP-NLSE dispersion

Category: Dispersion relation

Short description: Omega(k) relation for linearized CP-NLSE

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Derivation/DR01\_Redundant.lean; formal/python/tests/test\_dr01\_eq02\_dispersion.py

Scope / limits: Linearization about ψ=0 (vacuum/small-amplitude limit); does not encode finite-density phonon slope; A3 operator reductions rely on explicit axioms Dt\_planeWave and Delta\_planeWave; no Mathlib-analytic derivative proof is present.

Dependencies: EQ-02, OP-PW-01, OP-PW-02, OP-PW-03

Notes: Reduction is conditional on Dt\_planeWave / Delta\_planeWave axioms (quarantined in OP-PW-02). Plane-wave reduction scaffolding is tracked under OP-PW-\* (e.g., OP-PW-03) to keep EQ-02 definition evidence separate from operator reduction evidence.

External anchor: None

External evidence: None



ID: DR-01a

Name: DR-01 fit artifact is provenance-stamped (data-backed)

Category: Evidence block

Short description: Defines a minimal DR-01 fit artifact type that carries deterministic provenance fields and a content-based data fingerprint (sha256 of a canonical (k, ω) sample encoding). This prevents “anonymous” fits from being used in downstream bridge locks.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit.py; formal/python/tests/test_dr01_fit_artifact_provenance.py

Scope / limits: Provenance and hashing contract only; does not assert the fit is empirically anchored to any external dataset.

Dependencies: DR-01

Notes: `data_fingerprint` is computed from `sample_kw` using sorted-by-k fixed-format encoding; library code does not read CSV files.

External anchor: None

External evidence: None



ID: DR-01b

Name: DR-01 curved fit artifact is provenance-stamped (data-backed)

Category: Evidence block

Short description: Defines a second, deterministic DR fit artifact type (`DR01FitCurved1D`) for curvature-aware low-k modeling using the proxy fit ω/k = c0 + βk², preserving provenance fields and `data_fingerprint` discipline and enabling lockable fit-quality metadata in y=ω/k space.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_curved.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Fit-object contract and deterministic fitter only; does not by itself freeze new external-evidence JSON artifacts.

Dependencies: DR-01

Notes: Designed to test whether strict through-origin linearization is too rigid in low-k windows.

External anchor: None

External evidence: None





ID: DR-02

Name: Bogoliubov/LDA dispersion (Steinhauer Fig. 3a)

Category: Dispersion relation

Short description: LDA Bogoliubov excitation dispersion evaluated using μ/h = 1.91 kHz from paper and compared to digitized Fig. 3a points.

Status: Empirically Anchored

Evidence: DR-02-EVIDENCE-DIGITIZATION; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/0111438v1.pdf

Scope / limits: Finite-density trapped BEC excitation regime; LDA/trap-averaging built in; uses σ proxies derived from reported broadening scales; not the paper’s pointwise experimental uncertainties

Dependencies: None

Notes: Derived-from-Established-Physics (Bogoliubov + LDA) used as the model form for the empirical anchor; anchoring is to Steinhauer Fig. 3a under stated σ proxies. χ² is diagnostic only under the σ proxy derived from reported broadening scales; not a definitive goodness-of-fit without pointwise experimental uncertainties.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a





ID: DR-02-EVIDENCE-DIGITIZATION

Name: Steinhauer Fig. 3a digitization and Bogoliubov/LDA evaluation trace

Category: Evidence block

Short description: Internal reconstruction artifacts and outputs supporting DR-02 empirical anchor.

Status: Behavioral (Python)

Evidence: formal/external\_evidence/bec\_bragg\_steinhauer\_2001/omega\_k\_data.csv; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/extracted\_params.md; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/compare\_omega\_k.py; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/comparison\_results.csv; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/comparison\_plot.png; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/evidence\_summary.txt; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/0111438v1.pdf

Scope / limits: Digitization + parameter-fixed evaluation only; σ proxies used; no pointwise experimental uncertainties; digitization uncertainty not independently quantified.

Dependencies: None

Notes: Supports DR-02 empirical anchor; internal reconstruction artifact set. Empirically Anchored status applies to DR-02 only; this evidence block remains Behavioral (Python). χ² is diagnostic under σ proxy; no definitive goodness-of-fit claim.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-04a

Name: DR-04 fit artifact (third low-k window from Steinhauer Fig. 3a)

Category: Evidence block

Short description: Freezes a third `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using a deliberately tighter low-k window choice, with provenance fields and a content-based data fingerprint.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact.md; formal/python/toe/dr01_fit.py

Scope / limits: Encodes one alternate window rule (k <= 1.6 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: This is an intentionally different “fit choice” intended for multi-fit robustness bookkeeping; no claim is made that it is more correct than DR-02a or DR-03a.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-04c

Name: DR-04c fit artifact (upgraded window from Steinhauer Fig. 3a; N≥5)

Category: Evidence block

Short description: Freezes an additional `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using a k-max choice that yields N≥5 (k <= 2.5 um^-1). Intended to replace DR-04a (k <= 1.6, N=4) in decision-grade 4-window robustness loops that require strict curved-fit adequacy.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact.md; formal/python/toe/dr01_fit.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Encodes one alternate window rule (k <= 2.5 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: Introduced to eliminate reliance on the DQ-01_v2 low-N exception in fit-family selection, while retaining a 4-window set.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-04d

Name: DR-04d fit artifact (minimal feasible low-k window; N=5)

Category: Evidence block

Short description: Freezes an additional `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using the **smallest available k-max cutoff that yields N≥5** under the frozen digitization (k <= 1.75000027210818 um^-1). Intended as the least-invasive replacement for DR-04a (k <= 1.6, N=4) when strict curved-fit adequacy (DQ-01_v1) is required.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04d_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04d_fit_artifact.md; formal/python/toe/dr01_fit.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Encodes one alternate window rule (k <= 1.75000027210818 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: Justification: under frozen digitization, k<=1.6 um^-1 is infeasible for N≥5 (N=4). The smallest feasible cutoff for N≥5 is k_max=1.75000027210818 um^-1 (N=5).

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-04b

Name: DR fit-quality diagnostics (DR-02a vs DR-03a vs DR-04a)

Category: Evidence block

Short description: Adds minimal deterministic fit-quality instrumentation (N_points, RMSE, slope stderr, R^2 through-origin) for the frozen DR-01 low-k linearization artifacts and compares DR-02a/DR-03a/DR-04a to separate methodological undersampling effects from true fit-window sensitivity.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_quality.py; formal/python/tests/test_dr_fit_quality_present_and_reasonable.py; formal/markdown/locks/bridges/DR_fit_quality_comparison_DR02_DR03_DR04.md

Scope / limits: Diagnostics are for the forced through-origin model omega ~= c_s*k using each artifact’s frozen `sample_kw`; they do not establish external error models or absolute goodness-of-fit.

Dependencies: DR-02a, DR-03a, DR-04a

Notes: This resolves ambiguity in interpreting multi-fit drift gates by making fit-quality visible and lockable.

External anchor: None

External evidence: None



ID: DR-05a

Name: DR-05 fit artifact (intermediate low-k window from Steinhauer Fig. 3a)

Category: Evidence block

Short description: Freezes a fourth `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using an intermediate low-k window (k <= 1.8 um^-1) intended to distinguish monotone drift vs isolated-window outliers. Includes deterministic fit-quality instrumentation and a content-based data fingerprint.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact.md; formal/python/toe/dr01_fit.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Encodes one alternate window rule (k <= 1.8 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02, DR-04b

Notes: This is an intentionally different “fit choice” intended for monotonicity diagnosis over k-max.

Alias note: Under the frozen Steinhauer Fig. 3a digitization, DR-05 selects the same underlying 5-point sample as DR-04d (same `data_fingerprint`). For mainline multi-window robustness computations, DR-05 must not be treated as independent evidence relative to DR-04d (see DR-05c).

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-05c

Name: DR-04d/DR-05 alias note (identical frozen sample)

Category: Evidence block

Short description: Locks the bookkeeping fact that DR-04d and DR-05 select the same underlying 5-point sample under the frozen Steinhauer Fig. 3a digitization (same data_fingerprint), so they must not be treated as independent evidence in mainline robustness computations.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_window_alias_DR04d_DR05.md

Scope / limits: Bookkeeping-only; does not introduce new fitting or a physics claim.

Dependencies: DR-04d, DR-05a

Notes: Used to keep the robustness DAG logically clean while retaining both window-definition semantics for audit.

External anchor: None

External evidence: None



ID: DR-05b

Name: DR fit-quality diagnostics (DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Extends the DR-04b fit-quality comparison by adding the intermediate-window DR-05a artifact to enable monotonicity/outlier diagnosis over k-max.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/DR_fit_quality_comparison_DR02_DR03_DR04_DR05.md

Scope / limits: Evidence-only table/interpretation; does not establish an external noise model.

Dependencies: DR-05a

Notes: See also the corresponding BR-01 metric comparison extended to DR-05.

External anchor: None

External evidence: None



ID: DR-06a

Name: Curvature-aware DR fit artifacts (DR-02a/DR-03a/DR-04a/DR-05a curved)

Category: Evidence block

Short description: Freezes four curvature-aware DR fit artifacts for the same Steinhauer Fig. 3a digitized samples as DR-02a/03a/04a/05a by fitting ω/k = c0 + βk² on each window’s frozen `sample_kw`. Includes deterministic fit-quality diagnostics in y-space and the derived BR-01 metric fields (unit-density gauge using c0 as c_s(k→0)).

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.md; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.md; formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.md; formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.md

Scope / limits: Minimal proxy model upgrade only; does not assert a best-fit external physics model.

Dependencies: DR-01b, DR-02a, DR-03a, DR-04a, DR-05a, BR-01

Notes: Intended as the canonical frozen input set for curved BR/OV robustness scans.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-06c

Name: Curvature-aware DR fit artifact (DR-04c curved)

Category: Evidence block

Short description: Freezes a curvature-aware DR fit artifact for the DR-04c window sample by fitting ω/k = c0 + βk² on the frozen `sample_kw`. Includes deterministic fit-quality diagnostics in y-space and the derived BR-01 metric fields (unit-density gauge using c0 as c_s(k→0)).

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact_curved.md; formal/python/toe/dr01_fit_curved.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Minimal proxy model upgrade only; does not assert a best-fit external physics model.

Dependencies: DR-01b, DR-04c, BR-01

Notes: This is the curved companion artifact enabling strict DQ-01_v1 adequacy across the 4-window set used by OV-01g/POL-01.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-06d

Name: Curvature-aware DR fit artifact (DR-04d curved; minimal N=5 window)

Category: Evidence block

Short description: Freezes a curvature-aware DR fit artifact for the DR-04d window sample by fitting ω/k = c0 + βk² on the frozen `sample_kw`. Includes deterministic fit-quality diagnostics in y-space and the derived BR-01 metric fields (unit-density gauge using c0 as c_s(k→0)).

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04d_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04d_fit_artifact_curved.md; formal/python/toe/dr01_fit_curved.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Minimal proxy model upgrade only; does not assert a best-fit external physics model.

Dependencies: DR-01b, DR-04d, BR-01

Notes: This is the minimal-N=5 curved companion artifact intended to enable strict DQ-01_v1 adequacy without any N=4 special-casing.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-06b

Name: DR fit-quality diagnostics (curved proxy; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Curvature-aware fit-quality comparison for the four DR window choices, computed deterministically in y=ω/k space (RMSE(y), stderr(c0), stderr(β), R²(y)). Intended to separate model-form effects from sampling/conditioning effects.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/DR_fit_quality_comparison_curved_DR02_DR03_DR04_DR05.md; formal/python/toe/dr01_fit_quality.py; formal/python/toe/dr01_fit_curved.py

Scope / limits: Diagnostic bookkeeping only; R² in y-space can be numerically small when y variation is tiny relative to its mean.

Dependencies: DR-01b, DR-02a, DR-03a, DR-04a, DR-05a

Notes: Curved window artifacts are frozen under DR-06a; this report summarizes their fit-quality diagnostics.

External anchor: None

External evidence: None



ID: DR-β-01

Name: β relevance verdict (DR curved windows)

Category: Evidence block

Short description: Evidence-only verdict on whether the curvature parameter β in the proxy model ω/k = c0 + βk² is inferentially meaningful across the frozen curvature-aware DR window artifacts. Records β, stderr(β), SNR(β), sign stability, and compatibility-with-zero diagnostics using only the frozen curved artifacts.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_beta_relevance_verdict_DR02_DR03_DR04d_DR05.md

Scope / limits: Uses only frozen curved artifacts’ stamped parameters and fit-quality fields; does not introduce new fitting or a physical claim that the proxy curvature model is correct.

Dependencies: DR-06a, DR-06d

Notes: Under the frozen Steinhauer Fig. 3a digitization, DR-04d and DR-05 select the same underlying 5-point sample (same data_fingerprint), so they are not statistically independent evidence about β.

External anchor: None

External evidence: None



ID: DQ-01

Name: DQ-01 curved-fit adequacy gate (DR-01 curved artifacts)

Category: Evidence block

Short description: Defines a deterministic adequacy gate for curvature-aware DR-01 fit artifacts (`DR01FitCurved1D`). Checks N, RMSE(ω/k), stderr(c0), and a conservative β identifiability condition (β SNR or small β stderr). Intentionally does not use R²(y) as a required check.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_adequacy.py; formal/python/tests/test_dr01_fit_adequacy_curved_gate.py

Scope / limits: Adequacy is a workflow gate (data-support check), not a claim that the curved proxy is the correct physical model. Thresholds are provisional and should be tightened as additional evidence accumulates.

Dependencies: DR-01b, DR-06a, DR-06c, DR-06d

Notes: Designed to prevent POL-01 from operationalizing “curved” when curvature inference is underpowered in a given window.

External anchor: None

External evidence: None



ID: DQ-01a

Name: DQ-01 curved-fit adequacy table (DR-02/03/04/05 curved)

Category: Evidence block

Short description: Evidence-only table applying DQ-01 adequacy checks to the four frozen curved window artifacts corresponding to DR-02a/03a/04a/05a. Records N, RMSE(ω/k), stderr(c0), β, β_stderr, β_snr, pass/fail, and reason codes.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_DR02_DR03_DR04_DR05.md

Scope / limits: Uses only the frozen curved artifacts’ stamped diagnostics; does not introduce new fitting.

Dependencies: DQ-01, DR-06a

Notes: Under default thresholds, DR-04 curved fails due to N=4 and β identifiability.

External anchor: None

External evidence: None



ID: DQ-01a2

Name: DQ-01 curved-fit adequacy table (DR-02/03/04c/05 curved)

Category: Evidence block

Short description: Evidence-only table applying DQ-01 adequacy checks (DQ-01_v1 strict) to the upgraded 4-window curved artifact set that replaces DR-04a (N=4) with DR-04c (N=7). Records N, RMSE(ω/k), stderr(c0), β, β_stderr, β_snr, pass/fail, and reason codes.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_DR02_DR03_DR04c_DR05.md

Scope / limits: Uses only the frozen curved artifacts’ stamped diagnostics; does not introduce new fitting.

Dependencies: DQ-01, DR-06a, DR-06c

Notes: Under default strict thresholds, all four windows pass; DQ-01_v2 is no longer required for fit-family selection on this set.

External anchor: None

External evidence: None



ID: DQ-01a3

Name: DQ-01 curved-fit adequacy table (DR-02/03/04d/05 curved)

Category: Evidence block

Short description: Evidence-only table applying DQ-01 adequacy checks (DQ-01_v1 strict) to the minimal-feasible low-k upgraded 4-window curved artifact set that replaces DR-04a (N=4) with DR-04d (N=5 at k_max=1.75000027210818 um^-1). Records N, RMSE(ω/k), stderr(c0), β, β_stderr, β_snr, pass/fail, and reason codes.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_DR02_DR03_DR04d_DR05.md

Scope / limits: Uses only the frozen curved artifacts’ stamped diagnostics; does not introduce new fitting.

Dependencies: DQ-01, DR-06a, DR-06d

Notes: Under default strict thresholds, the DR-04d-upgraded set passes without any low-N special-casing. Under the frozen digitization, DR-04d is the smallest feasible cutoff that yields N≥5.

External anchor: None

External evidence: None



ID: DQ-01c

Name: DQ-01c (Evidence, Variant A / DR-04 only)

Category: Evidence block

Short description: Evidence-only delta for the explicitly-scoped Variant A adjudication: admit DR-04 curved at N=4 only under strict RMSE/stderr(c0) bounds while recording β as not used for inference (reason code `beta_ignored_low_n`).

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_variantA_DR04.md

Scope / limits: Scope: DR-04 only, N=4 only; β ignored-for-inference; strict rmse/c0_stderr bounds. This is a rehabilitation attempt with guardrails, not a general low-N allowance.

Dependencies: DQ-01, DR-06a

Notes: Variant A records β as not used for inference at N=4; β identifiability is not a failure mode under this scoped policy.

External anchor: None

External evidence: None



ID: DQ-01b

Name: DQ-01 policy comparison table (v1 vs v2; DR-02/03/04/05 curved)

Category: Evidence block

Short description: Evidence-only delta report comparing DQ-01 curved-fit adequacy pass/fail and reason codes under DQ-01_v1 (strict) vs DQ-01_v2 (tiered low-N admissibility with β ignored) for the frozen DR-02/03/04/05 curved artifacts.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_policy_comparison_v1_v2_DR02_DR03_DR04_DR05.md

Scope / limits: Comparison uses the same frozen curved artifacts and the same adequacy reporting surface; only the policy parameter differs.

Dependencies: DQ-01, DQ-01a

Notes: Under DQ-01_v2, DR-04 curved becomes admissible as low-N with β ignored for inference.

External anchor: None

External evidence: None



ID: DQ-01v2

Name: DQ-01_v2 tiered curved-fit adequacy policy (N=4 conditional)

Category: Policy

Short description: Tiered variant of DQ-01 that preserves strict defaults (N>=5) but allows N==4 conditional admissibility under stricter RMSE and stderr(c0) thresholds and explicitly ignores β identifiability at low N (records `beta_ignored_low_n`).

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_adequacy.py; formal/python/tests/test_dr01_fit_adequacy_curved_gate.py; formal/markdown/locks/bridges/DR_fit_adequacy_curved_policy_comparison_v1_v2_DR02_DR03_DR04_DR05.md

Scope / limits: Operational workflow policy only; the low-N exception is meant to be temporary until a higher-N smallest-window artifact is generated.

Dependencies: DQ-01b

Notes: Retained for auditability/back-compat; no longer required for live fit-family selection once a strict-adequacy upgraded window set is used (e.g., DR-04d minimal-N=5, or DR-04c N=7).


External anchor: None

External evidence: None



ID: DQ-01_variantA

Name: DQ-01_variantA scoped curved-fit adequacy policy (DR-04@N=4 only)

Category: Policy

Short description: Explicitly-scoped adequacy overlay that allows N=4 only for DR-04, applies strict RMSE/stderr(c0) bounds at N=4, and treats β as not used for inference at N=4 (cannot fail via identifiability) while recording `beta_ignored_low_n`.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_adequacy.py; formal/python/tests/test_dr01_fit_adequacy_curved_gate.py; formal/markdown/locks/bridges/DR_fit_adequacy_curved_variantA_DR04.md

Scope / limits: Scope: DR-04 only, N=4 only; β ignored-for-inference; strict rmse/c0_stderr bounds. All other windows evaluated under DQ-01_v1 (no general N=4 allowance).

Dependencies: DQ-01c

Notes: Deprecated/superseded on the mainline: DR-04d + DQ-01_v1 removes the need for any N=4 special-casing. This policy tag remains to keep Variant A auditable and explicitly opt-in; it is not the default adequacy policy.

External anchor: None

External evidence: None



ID: DQ-01d

Name: DQ-01 next-step plan — retire low-N exceptions via DR-04′ (N≥5 near k≤1.6)

Category: Evidence block

Short description: Planning/feasibility note documenting that DQ-01_v2 and DQ-01_variantA low-N admissibility are temporary scaffolds. The replacement is a new DR-04′-class curved artifact with N≥5 in the “near k≤1.6 µm^-1” band, implemented by relaxing the low-k cutoff to the smallest feasible k-max under frozen digitization (DR-04d/DR-06d; k<=1.75000027210818 um^-1, N=5).

Status: Hypothesis

Evidence: formal/markdown/locks/bridges/DR_lowk_window_point_counts_Steinhauer_Fig3a.md

Scope / limits: Under the currently frozen digitization (`omega_k_data.csv`), k≤1.6 µm^-1 contains only 4 points. The minimal feasible N≥5 window is therefore the discrete cutoff at the 5th point’s k value (k_max=1.75000027210818 µm^-1). This avoids adding new digitization points while keeping the window “as low-k as the data allows.”

Dependencies: DR-02-EVIDENCE-DIGITIZATION, DR-04a, DR-04d, DR-06d, DQ-01_variantA

Notes: Success criteria for retiring low-N exceptions: (1) DR-06d passes DQ-01_v1 strict adequacy (including β identifiability policy), (2) OV-01g prefers curved under DQ-01_v1 on the chosen 4-window set, and (3) POL-01 no longer needs to reference DQ-01_v2 or DQ-01_variantA for live selection. Variant A remains as deprecated/audit evidence.

External anchor: None

External evidence: None



ID: DR-02a

Name: Canonical DR-01 fit artifact (low-k linearization from DR-02)

Category: Evidence block

Short description: Freezes a canonical `DR01Fit1D`-compatible linearization derived from the DR-02 digitized Steinhauer Fig. 3a dataset using a deterministic low-k window and a data-backed provenance hash. Intended as a stable input artifact for downstream bridge runs (e.g., BR-01 → MT-01) during the discriminative science phase.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.md; formal/python/toe/dr01_fit.py

Scope / limits: Encodes one specific low-k linearization rule (k <= 3.2 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: The artifact carries a content-based `data_fingerprint` (sha256) computed from the canonical (k, omega) sample encoding; no library code reads CSV files.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-03a

Name: DR-03 fit artifact (alternate low-k window from Steinhauer Fig. 3a)

Category: Evidence block

Short description: Freezes a second `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using a deliberately different low-k window choice, with provenance fields and a content-based data fingerprint.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.md; formal/python/toe/dr01_fit.py

Scope / limits: Encodes one alternate window rule (k <= 2.1 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: This is an intentionally different “fit choice” intended for cross-fit sensitivity bookkeeping; no claim is made that it is more correct than DR-02a.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a





4.3 FUNCTIONALS





ID: FN-01

Name: Admissible deformation class P\[ψ] (candidate family)

Category: Functional / Deformation class

Short description: Family of candidate nonlinear deformation terms gated by CT-01 and source-free admissibility

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreConsumer.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreBridge.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_DeformationClass.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateMembership.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateAPI.lean; formal/markdown/locks/functionals/FN-01\_deformation\_class.md; formal/python/tests/test\_fn01\_candidate\_table.py; formal/python/tests/test\_fn01\_near\_plane\_wave\_regression.py; formal/python/tests/test\_fn01\_candidate\_api\_enforced.py; CT-01-EVIDENCE-PHB; CT-01-EVIDENCE-SOLVER-OMEGA

Scope / limits: Organizational pruning framework for candidate deformations under CT-01 + source-free admissibility; probe-relative only.

Dependencies: EQ-01, CT-01, SYM-01, CAUS-01

Notes: No physical interpretation implied; member-level outcomes recorded externally.

External anchor: None

External evidence: None



ID: OV-01c

Name: OV-01 multi-fit stability gate (DR-02a vs DR-03a vs DR-04a)

Category: Evidence block

Short description: Extends OV-01b from a 2-fit cross-fit stability residual to a 3-fit robustness discriminator over three data-backed DR fit choices. Computes all pairwise normalized residuals on the OV-01 observable, summarizes with R_max/R_rms, applies a provisional gate (retain iff R_max ≤ tau), and records a g-grid scan.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_multi_fit_stability.py; formal/python/tests/test_ov01_multi_fit_stability.py; formal/markdown/locks/observables/OV-01_multi_fit_stability_DR02_DR03_DR04.md

Scope / limits: Provisional robustness gate only (tau is not claimed “true”); normalized residual cancels multiplicative g for g>0 under the current OV-01 Option A definition.

Dependencies: OV-01b, DR-04a

Notes: This is intended as a stronger robustness stress-test under fit-window perturbations; if it proves too strict or non-discriminating over FN parameter grids, it motivates either (i) revising the observable form (OV-02) or (ii) introducing absolute (non-normalized) residual reporting.

External anchor: None

External evidence: None



ID: OV-01d

Name: OV-01 multi-fit stability gate (DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Extends the OV-01 multi-fit stability envelope to four DR window choices by adding DR-05a (intermediate k-max). Locks the 4-fit R_max/R_rms values and records an interpretation for monotone drift vs isolated-window outliers.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_multi_fit_stability.py; formal/python/tests/test_ov01_multi_fit_stability_4fit.py; formal/markdown/locks/observables/OV-01_multi_fit_stability_DR02_DR03_DR04_DR05.md; formal/markdown/locks/observables/OV-01_multi_fit_stability_DR02_DR03_DR04c_DR05.md

Scope / limits: Provisional robustness gate only (tau is not claimed “true”); normalized residual cancels multiplicative g for g>0 under the current OV-01 Option A definition.

Dependencies: OV-01c, DR-05a, DR-04c

Notes: With DR-05a included, the c_s drift appears monotone in k-max, motivating curvature-aware DR modeling as the next science step. DR-04c provides an upgraded N≥5 window set for strict adequacy workflows.

External anchor: None

External evidence: None



ID: OV-01e

Name: OV-01 multi-fit stability gate (curved DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Curvature-aware variant of OV-01d that first fits ω/k = c0 + βk² on each frozen DR window sample and then computes the OV-01 observable values via the curved BR-01 front door. Locks the resulting 4-fit R_max/R_rms envelope and applies the same provisional retain/prune gate.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_multi_fit_stability_curved.py; formal/python/tests/test_ov01_multi_fit_stability_curved_4fit.py; formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04_DR05.md; formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04c_DR05.md

Scope / limits: Curved fit is a minimal proxy model upgrade; BR-01 mapping currently uses c0 as the k→0 sound-speed proxy under the existing unit-density gauge.

Dependencies: OV-01d, DR-01b

Notes: Curvature-aware modeling reduces but does not eliminate cross-window drift under the current τ=0.10 gate.

External anchor: None

External evidence: None



ID: OV-01f

Name: OV-01 multi-fit stability g-grid discriminator (linear vs curved; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Evidence-only g-grid scan for the 4-fit OV-01 envelope, presented as a direct linear-vs-curved comparison. Includes g=0.0 explicitly, reports per-g observable values and the locked R_max/R_rms envelope values, and reuses the same provisional τ=0.10 gate for retain/prune.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04_DR05_ggrid.md; formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04c_DR05_ggrid.md

Scope / limits: Under OV-01 Option A (O = g*c_s^2), the normalized residual cancels multiplicative g for all g>0; the scan is included for completeness and explicit g=0 handling.

Dependencies: OV-01d, OV-01e

Notes: Intended to be read alongside OV-01d and OV-01e. Curved fitting reduces the 4-fit envelope but does not pass the current τ=0.10 robustness gate.

External anchor: None

External evidence: None



ID: OV-01g

Name: OV-01 fit-family robustness gate (linear vs curved; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Observable

Short description: Promotes the “curved reduces multi-window spread” observation into an explicit fit-family admissibility gate. Computes the OV-01 stability envelope for both the linear and curved DR families (deduplicating by underlying `data_fingerprint` so alias windows are not double-counted), forms Q = R_max(curved)/R_max(linear), and prefers curved iff Q <= 0.9 and curved fit-quality is admissible under explicit y-space diagnostic thresholds.

Status: Empirically Anchored

Evidence: formal/python/toe/observables/ov01_fit_family_robustness.py; formal/python/tests/test_ov01_fit_family_robustness_gate.py; formal/markdown/locks/observables/OV-01_fit_family_robustness_DR02_DR03_DR04_DR05.md; formal/markdown/locks/observables/OV-01_fit_family_robustness_DR02_DR03_DR04c_DR05.md; formal/markdown/locks/observables/OV-01_fit_family_robustness_DR02_DR03_DR04d_DR05.md

Scope / limits: This selects a preferred DR-fit family for downstream OV bookkeeping; it does not claim the robustness gate itself is “true,” and it does not imply the underlying τ=0.10 retain criterion is satisfied. Under OV-01 Option A (O = g*c_s^2), normalized residuals cancel multiplicative g for g>0.

Dependencies: OV-01d, OV-01e, OV-01f, DR-06b, DQ-01, DQ-01a2, DQ-01a3, FN-01k, EA-01a

Notes: If the gate cannot prefer curved under the provisional thresholds, downstream should treat OV-based family selection as non-decisive (robustness failed). “Prefer curved” is an operational robustness decision (reduced window brittleness) and must not be interpreted as a β-detection / curvature-parameter inference claim; see DR-β-01.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: EA-01a

Name: EA-01 evaluation note — OV-01g (robustness-only)

Category: Evidence block

Short description: Evidence-only application of EA-01 to OV-01g, recording that OV-01g satisfies the EA-01 checklist as a robustness-only result and that β is not inferred (compatible with 0 in DR-β-01).

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/policy/EA-01a_evaluation_OV-01g.md

Scope / limits: Evaluation note only; does not introduce new data or modeling.

Dependencies: DR-β-01, DR-04d, DR-05a

Notes: This is the promotion record used to prevent accidental Empirically Anchored upgrades without a declared EA-01 application artifact.

External anchor: None

External evidence: None



ID: OV-01x

Name: OV-01x (Evidence, Variant A family robustness)

Category: Evidence block

Short description: Evidence-only run of the OV-01g fit-family robustness gate over DR-02/03/04/05 under the explicitly-scoped adequacy policy tag `DQ-01_variantA`. Documents that DR-04 is admitted only under β-not-used-for-inference at N=4 with strict RMSE/stderr(c0) bounds.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/observables/OV-01_fit_family_robustness_DR02_DR03_DR04_DR05_variantA.md

Scope / limits: Variant A evidence is explicitly policy-tagged; it is not the default selection path. Curved preference under this report must not be treated as a curvature-parameter (β) inference claim.

Dependencies: OV-01g, DQ-01_variantA

Notes: Required statement: “DR-04 passes Variant A only under β-not-used-for-inference at N=4.”

Deprecated status: Audit-only evidence; mainline fit-family selection uses DQ-01_v1 with an N≥5 low-k window (DR-04d) and does not require Variant A.

External anchor: None

External evidence: None



ID: POL-01

Name: Policy — use curved DR family for OV-based pruning when OV-01g prefers curved

Category: Policy

Short description: Makes the OV-01g fit-family robustness gate operational by defining a single front-door selector used by downstream loops: prefer the curved DR family for OV-based pruning iff OV-01g prefers curved and robustness_failed=False; otherwise treat OV pruning as non-decisive for family selection.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_family_policy.py; formal/python/tests/test_ov01_family_policy.py

Scope / limits: This is an operational workflow policy, not a physics claim. If selection is undecided, downstream must not silently fall back to linear for OV-based pruning. “Prefer curved” is about robustness against window brittleness; it does not imply a β-detection claim (see DR-β-01).

Dependencies: OV-01g, DQ-01, DR-β-01

Notes: This prevents silent drift back to linear DR family in OV-based robustness bookkeeping. DQ-01_v2 and DQ-01_variantA remain available for audit/back-compat but are not required on the DR-04d minimal-N=5 upgraded window set.

Non-inference rule: β is treated as nuisance/placeholder in mainline. No mainline claim may treat β as physically inferred until new data or a new measurement regime exists.

Authoring note (mainline): Do not assert or imply that β differs from 0, or make any curvature-claim language, in mainline (Behavioral / Structural) nodes. Use robustness-only language (e.g., “β not inferred,” “compatible with 0,” “robustness preference only”). Any claim that β is statistically resolved must be explicitly labeled Hypothesis or Spec-backed and gated by new evidence.

External anchor: None

External evidence: None



ID: EA-01

Name: Empirical anchor adequacy (pre-registered upgrade criteria)

Category: Policy

Short description: Defines pre-registered, science-facing criteria for upgrading a candidate correspondence from internal behavioral evidence to Empirically Anchored. EA-01 answers one question only: when may a Behavioral (Python) result be promoted to Empirically Anchored?

Status: Hypothesis

Evidence: None

Scope / limits: Criteria only; does not itself upgrade any item. External anchoring requires external evidence outside this repository.

Dependencies: OV-01g, DR-β-01, DR-04d, DR-05a

Notes: Operational rule: any policy/promotion wording or dependency edit must pass the 4 risk tests (stop-the-line).

Acceptance criteria (all required for promotion to Empirically Anchored):

- Frozen external data: input dataset is frozen, fingerprinted, and cited; no digitization/preprocessing ambiguity remains.
- Model-independent robustness: result survives at least one robustness discriminator (e.g., OV-01 class) that compares multiple admissible windows/fits and does not rely on a single hand-picked subset.
- No parameter over-interpretation: no parameter is inferred beyond its statistical support; if a parameter is not significant (e.g., β per DR-β-01), phrasing must not rely on it.
- Deterministic reproduction: regeneration from frozen inputs reproduces the result bit-for-bit (or within a declared numeric tolerance) and a locked determinism test exists.
- Negative result admissible: null/absence conclusions (e.g., “no evidence that β differs from 0”) are allowed and may still qualify if the above criteria are met.

Non-dependencies: EA-01 must not depend on Variant A or any speculative/Hypothesis evidence blocks intended only for audit.

External anchor: None

External evidence: None



ID: EA-02

Name: Empirical anchor adequacy (digitization / instrument invariance)

Category: Policy

Short description: Defines pre-registered, science-facing criteria for upgrading a digitization/instrument invariance claim (OV-02x) to Empirically Anchored. EA-02 answers one question only: when may a robustness/stability claim about digitization perturbations be treated as an empirical anchor?

Status: Hypothesis

Evidence: None

Scope / limits: Criteria only; does not itself upgrade any item. This gate is explicitly *robustness-only* and must not be used to imply any parameter inference (e.g., treating β as resolved away from 0).

Dependencies: OV-02x, DR-β-01

Notes: Acceptance criteria (all required for promotion to Empirically Anchored):

- Frozen external data: input dataset is frozen, fingerprinted, and cited; no untracked digitization drift.
- Pre-registered perturbation model: the digitization perturbation/tolerance is declared in advance (bounded, deterministic, and auditable).
- Model-independent robustness discriminator: the downstream decision uses an explicit robustness gate (e.g., OV-01g) and must not rely on a single hand-picked subset.
- No parameter over-interpretation: no parameter is inferred beyond its statistical support; β remains non-inferred/compatible with 0 (see DR-β-01).
- Deterministic reproduction: regeneration under the declared perturbations reproduces the same pass/fail outcomes (and stable fingerprints) within the declared tolerance.
- Negative result admissible: failures (preference flips) are allowed and must be recorded as negative results.

External anchor: None

External evidence: None




ID: OV-02x

Name: OV-02x digitization invariance of OV-01g preference (bounded perturbations)

Category: Observable

Short description: Metamorphic stability check: under small, pre-registered perturbations to the frozen Steinhauer Fig. 3a digitization, the OV-01g fit-family robustness preference (prefer_curved) must not flip.

Status: Empirically Anchored

Evidence: formal/python/toe/observables/ov02_digitization_invariance.py; formal/python/tests/test_ov02_digitization_invariance_gate.py; formal/markdown/locks/observables/OV-02x_digitization_invariance.md

Scope / limits: Anchors stability of the robustness selector under bounded digitization perturbations. This is not a physics claim and must not be used for β inference; see DR-β-01.

Dependencies: OV-01g, DR-β-01, DR-02-EVIDENCE-DIGITIZATION, EA-02a

Notes: If invariance fails (preference flips under declared perturbations), treat OV-01g-based family selection as non-decisive for any downstream science claims until a new measurement regime or independent evidence family is added.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a




ID: EA-02a

Name: EA-02 evaluation note — OV-02x (digitization invariance)

Category: Evidence block

Short description: Evidence-only application of EA-02 to OV-02x, recording that OV-02x satisfies the EA-02 checklist as a robustness-only digitization-invariance result and that β is not inferred (compatible with 0 in DR-β-01).

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/policy/EA-02a_evaluation_OV-02x.md

Scope / limits: Evaluation note only; does not introduce new data or modeling.

Dependencies: DR-β-01, DR-02-EVIDENCE-DIGITIZATION, OV-01g

Notes: This is the promotion record used to prevent accidental Empirically Anchored upgrades without a declared EA-02 application artifact.

External anchor: None

External evidence: None




<a id="OV-OBS-01-EVIDENCE-ARTIFACT"></a>

ID: OV-OBS-01-EVIDENCE-ARTIFACT

Name: OV-OBS-01 diagnostic artifact (metadata invariance)

Category: Evidence block

Short description: Frozen JSON record of the OV-OBS-01 audit run, asserting that OV-01 observable outputs are invariant under metadata-only perturbations of the FN/DR input artifacts.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-OBS-01/metadata_invariance.json; formal/python/toe/observables/ovobs01_observability_metadata_invariance.py; formal/python/tools/ovobs01_metadata_invariance.py

Scope / limits: Diagnostic-only software guardrail; does not create a lock and does not assert any physics claim.

Dependencies: DR-01, FN-01

Notes: Operationalizes “observability / unknowability” as an engineering constraint: observable computations must not depend on unobservable provenance strings (tags/source_ref).

External anchor: None

External evidence: None



<a id="OV-FG-01-EVIDENCE-ARTIFACT"></a>

ID: OV-FG-01-EVIDENCE-ARTIFACT

Name: OV-FG-01 diagnostic artifact (ring graph Fourier mode)

Category: Evidence block

Short description: Frozen JSON record of the OV-FG-01 audit run, confirming that discrete Fourier modes are eigenmodes of the ring-graph Laplacian and that the observed eigenvalue matches the closed-form expectation.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-FG-01/ring_graph_fourier_mode_audit.json; formal/python/toe/observables/ovfg01_graph_fourier_mode_audit.py; formal/python/tools/ovfg01_graph_fourier_mode_audit.py

Scope / limits: Internal structural consistency scaffold only (graph ↔ Fourier correspondence on a ring). Not an external empirical anchor.

Dependencies: None

Notes: Intended to surface hidden continuum-limit assumptions by providing a discrete spectral cross-check.

External anchor: None

External evidence: None



<a id="OV-MB-01-EVIDENCE-ARTIFACT"></a>

ID: OV-MB-01-EVIDENCE-ARTIFACT

Name: OV-MB-01 diagnostic artifact (orthogonality trend)

Category: Evidence block

Short description: Frozen JSON record of the OV-MB-01 toy many-body audit run, computing the finite-size Slater-determinant overlap between ground states with and without a single-site impurity on a 1D tight-binding ring.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-MB-01/orthogonality_trend.json; formal/python/toe/observables/ovmb01_orthogonality_catastrophe_audit.py; formal/python/tools/ovmb01_orthogonality_trend.py

Scope / limits: Toy-model trend audit only; does not constitute empirical anchoring for polaron/OC physics and is not claimed as a faithful condensed-matter model.

Dependencies: None

Notes: Intended as a minimal harness for “overlap sensitivity to local perturbation” bookkeeping; finite-size overlaps can oscillate with L.

External anchor: None

External evidence: None



<a id="OV-PT-01-EVIDENCE-ARTIFACT"></a>

ID: OV-PT-01-EVIDENCE-ARTIFACT

Name: OV-PT-01 diagnostic artifact (hexatic-window detector demo)

Category: Evidence block

Short description: Frozen JSON demo artifact for the OV-PT-01 phase-transition window detector, using a synthetic two-step order-parameter curve that exhibits an orientational-only window.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-PT-01/hexatic_window_demo.json; formal/python/toe/observables/ovpt01_phase_transition_window_audit.py; formal/python/tools/ovpt01_hexatic_window_demo.py

Scope / limits: Demonstration only; not external data and not a simulation claim. Provides a deterministic, auditable detector mechanism to be applied to supplied order-parameter curves.

Dependencies: None

Notes: Use this detector on real or simulated datasets once a declared order-parameter extraction pipeline exists.

External anchor: None

External evidence: None



<a id="OV-QC-01-EVIDENCE-ARTIFACT"></a>

ID: OV-QC-01-EVIDENCE-ARTIFACT

Name: OV-QC-01 diagnostic artifact (Chern number, Qi–Wu–Zhang)

Category: Evidence block

Short description: Frozen JSON record of the OV-QC-01 Chern number computation on a minimal two-band lattice model (Qi–Wu–Zhang) using a discrete link-variable (FHS) method.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-QC-01/chern_qiwuzhang.json; formal/python/toe/observables/ovqc01_berry_curvature_audit.py; formal/python/tools/ovqc01_chern_qiwuzhang.py

Scope / limits: Mathematical audit primitive only; not an EWT claim and not an external empirical anchor.

Dependencies: None

Notes: Intended as a reusable computational primitive for future “quantum geometry” bridge experiments.

External anchor: None

External evidence: None



<a id="OV-ZPF-01-EVIDENCE-ARTIFACT"></a>

ID: OV-ZPF-01-EVIDENCE-ARTIFACT

Name: OV-ZPF-01 diagnostic artifact (brain–ZPF resonance overlap demo)

Category: Evidence block

Short description: Frozen JSON demo artifact for the OV-ZPF-01 overlap audit scaffold, recording frequency-band overlap bookkeeping between canonical beta/gamma EEG bands and synthetic candidate mode bands.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-ZPF-01/brain_zpf_resonance.json; formal/python/toe/observables/ovzpf01_brain_zpf_resonance_audit.py; formal/python/tools/ovzpf01_brain_zpf_resonance_audit.py

Scope / limits: Demonstration only; not external data and not a physical feasibility determination. Records overlap geometry and labeled heuristics only; does not assert coupling or causation.

Dependencies: None

Notes: If/when real EEG/ZPF-mode inputs are provisioned, they must be introduced via explicit input artifacts and accompanying tests; avoid direct imports from legacy or narrative docs.

External anchor: None

External evidence: None



<a id="OV-UCFF-01-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-01-EVIDENCE-ARTIFACT

Name: OV-UCFF-01 diagnostic artifact (UCFF jitter-structure demo)

Category: Evidence block

Short description: Frozen JSON demo artifact for the OV-UCFF-01 audit scaffold, recording symbolic term-presence checks and a bounded numeric ω²(k) non-negativity scan under small parameter jitter.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-01/ucff_jitter_structure.json; formal/python/toe/observables/ovucff01_jitter_structure_audit.py; formal/python/tools/ovucff01_jitter_structure_audit.py

Scope / limits: Demonstration only; not external data. Records bookkeeping about a chosen polynomial template and a chosen k-window; does not validate UCFF as a physical model.

Dependencies: None

Notes: This is intended as a low-risk port target for legacy UCFF symbolic tests: attach additional invariants only via explicit tests and pinned artifacts.

External anchor: None

External evidence: None



<a id="OV-UCFF-02-EVIDENCE-ARTIFACT"></a>

ID: OV-UCFF-02-EVIDENCE-ARTIFACT

Name: OV-UCFF-02 diagnostic artifact (framewise cross-variation demo)

Category: Evidence block

Short description: Frozen JSON artifact for the OV-UCFF-02 audit scaffold, recording framewise variation summaries on a pinned legacy-derived internal input (if present) plus synthetic regression demos.

Status: Behavioral (Python)

Evidence: formal/python/artifacts/diagnostics/OV-UCFF-02/ucff_framewise_variation.json; formal/python/artifacts/input/OV-UCFF-02/legacy_phase51_coherence_drift_pair_density.json; formal/python/artifacts/input/OV-UCFF-02/source_test_phase51_coherence_drift_metrics.py; formal/python/artifacts/input/OV-UCFF-02/legacy_ucff_framewise_roundtrip.py; formal/python/toe/observables/ovucff02_framewise_variation_audit.py; formal/python/tools/ovucff02_framewise_variation_audit.py

Scope / limits: Bookkeeping only; not external data. Records numeric summary statistics for a supplied (frames × bins) array. The pinned input is an internal legacy-derived fixture (traceability aid), not an empirical anchor.

Dependencies: None

Notes: This scaffold now supports a pinned legacy-derived internal input artifact (density pair derived from the legacy coherence-drift fixture spec). The legacy source is pinned for traceability only and is not imported/executed by OV-UCFF-02. A frozen regression reference report is maintained at formal/python/artifacts/input/OV-UCFF-02/reference_ovucff02_pinned_report.json and may be rewritten only via the guarded front-door CLI flag (--write-reference with --force and TOE_ALLOW_REFERENCE_WRITES=1). Invoking the writer does not upgrade any status; it only updates the pinned baseline for regression enforcement.

External anchor: None

External evidence: None




ID: DS-01-EVIDENCE-DIGITIZATION

Name: B1 second external dataset digitization packet (Ernst et al., 2009)

Category: Evidence block

Short description: Evidence packet for a second independent external dispersion dataset (B1), digitized from Ernst et al. (arXiv:0908.4242v1) Fig. 2a into a frozen omega(k) CSV with recorded fingerprints.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv; formal/external_evidence/bec_bragg_b1_second_dataset_TBD/source_citation.md; formal/external_evidence/bec_bragg_b1_second_dataset_TBD/data_fingerprint.md

Scope / limits: Digitization + provenance/fingerprints only. This evidence block does not itself assert an external epistemic status; it supports OV-03x anchoring.

Dependencies: None

Notes: Dataset populated from Ernst et al. (2009), Fig. 2a. The current frozen extraction targets a single high-k branch (no low-k coverage in the selected series; k starts at ~3.34 um^-1). Do not attach low-k regime claims to this dataset; treat it as a high-k robustness anchor unless a different digitization target/dataset is introduced. See `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/data_fingerprint.md` for the frozen hashes.

External anchor: None

External evidence: None




ID: DR-β-02

Name: β non-inference posture (B1 second dataset)

Category: Policy

Short description: Mirrors DR-β-01 for the B1 dataset: β is treated as non-inferred/compatible with 0 in mainline for this evidence family unless and until a new measurement regime supports inference.

Status: Behavioral (Python)

Evidence: None

Scope / limits: Guardrail only; does not assert β=0, and does not permit β inference without new evidence.

Dependencies: DS-01-EVIDENCE-DIGITIZATION

Notes: Authoring note (mainline): use only β-null language (“β not inferred”, “compatible with 0”, “not significant”).

External anchor: None

External evidence: None




ID: EA-03

Name: Empirical anchor adequacy (B1 second external dataset)

Category: Policy

Short description: Defines pre-registered, science-facing criteria for upgrading OV-03x (robustness-only fit-family preference on a second dataset) to Empirically Anchored.

Status: Hypothesis

Evidence: None

Scope / limits: Criteria only; does not itself upgrade any item. Robustness-only; must not be used to imply parameter inference.

Dependencies: OV-03x, DR-β-02

Notes: Acceptance criteria (all required for promotion to Empirically Anchored):

- Frozen external data: dataset is frozen, fingerprinted, and cited (DS-01-EVIDENCE-DIGITIZATION).
- Model-independent robustness: decision uses an explicit robustness gate (OV-03x) across multiple admissible windows.
- No parameter over-interpretation: β is not inferred / compatible with 0 (see DR-β-02).
- Deterministic reproduction: regeneration from frozen inputs reproduces the result deterministically.
- Negative result admissible: null/absence and preference-flip outcomes are allowed and must be recorded.

External anchor: None

External evidence: None




ID: OV-03x

Name: OV-03x fit-family robustness gate on B1 second dataset (linear vs curved)

Category: Observable

Short description: Applies the same robustness-only fit-family preference structure as OV-01g to a second external dataset (B1), using frozen window artifacts derived from DS-01.

Status: Locked

Evidence: formal/python/toe/observables/ov03_fit_family_robustness.py; formal/python/tests/test_ov03_fit_family_robustness_gate_b1_dataset.py; formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md

Scope / limits: Robustness-only selector evaluation on a second dataset. Not a physics claim; must not be used for β inference (see DR-β-02).

Dependencies: DS-01-EVIDENCE-DIGITIZATION, DR-β-02, EA-03a

Notes: Robustness-only result on an independent external dataset. β is not inferred (compatible with 0; see DR-β-02). Under the current frozen Fig. 2a digitization + declared windows, the robustness gate records a negative / non-preference outcome (see lock); promotion under EA-03 is therefore not satisfied. The current frozen extraction is high-k only (k starts at ~3.34 um^-1); do not treat this as supporting any low-k regime statements.

External anchor: Bragg spectroscopy in an optical lattice (momentum-resolved excitation spectrum)

External evidence: Ernst et al., arXiv:0908.4242v1 (2009), Fig. 2a




ID: EA-03a

Name: EA-03 evaluation note — OV-03x (B1 second dataset)

Category: Evidence block

Short description: Evidence-only application record for OV-03x under EA-03. Required before promoting OV-03x to Empirically Anchored.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/policy/EA-03a_evaluation_OV-03x.md

Scope / limits: Evidence-only application record; does not introduce new data or modeling.

Dependencies: DS-01-EVIDENCE-DIGITIZATION, DR-β-02

Notes: Keep this record robustness-only and β-null (β not inferred / compatible with 0).

External anchor: None

External evidence: None




ID: DS-02-EVIDENCE-DIGITIZATION

Name: DS-02 low-k external dataset digitization packet (TBD)

Category: Evidence block

Short description: Evidence packet scaffold for a new independent low-k external dispersion dataset (DS-02), intended to provide multiple ω(k) points near k→0 and serve as a disciplined low-k anchor slot.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv; formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/source_citation.md; formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/digitization_notes.md; formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/data_fingerprint.md

Scope / limits: Digitization + provenance/fingerprints only. This evidence block does not itself assert an external epistemic status; it supports OV-04x anchoring.

Dependencies: None

Notes: Source designated: Shammass et al. (2012), arXiv:1207.3440v2, Fig. 2 (ω_k/2π vs k). Selection rules are pre-registered in the packet: (1) many low-k points near k→0 (target ≥10), (2) independent source (not Steinhauer/Ernst), (3) freely accessible (arXiv or equivalent). Until populated, the CSV is header-only and tests must remain green via explicit skips.

External anchor: None

External evidence: None



ID: DR-β-03

Name: β non-inference posture (DS-02 low-k dataset)

Category: Policy

Short description: Mirrors DR-β-01/DR-β-02 for DS-02: β is treated as non-inferred/compatible with 0 in mainline for this evidence family unless and until a new measurement regime supports inference.

Status: Behavioral (Python)

Evidence: None

Scope / limits: Guardrail only; does not assert β=0, and does not permit β inference without new evidence.

Dependencies: DS-02-EVIDENCE-DIGITIZATION

Notes: Authoring note (mainline): use only β-null language (“β not inferred”, “compatible with 0”, “not significant”).

External anchor: None

External evidence: None



ID: EA-04

Name: Empirical anchor adequacy (DS-02 low-k external dataset)

Category: Policy

Short description: Defines pre-registered, science-facing criteria for upgrading OV-04x (robustness-only fit-family preference on DS-02 low-k dataset) to Empirically Anchored.

Status: Hypothesis

Evidence: None

Scope / limits: Criteria only; does not itself upgrade any item. Robustness-only; must not be used to imply parameter inference.

Dependencies: OV-04x, DR-β-03

Notes: Acceptance criteria (all required for promotion to Empirically Anchored):

- Frozen external data: dataset is frozen, fingerprinted, and cited (DS-02-EVIDENCE-DIGITIZATION).
- Model-independent robustness: decision uses an explicit robustness gate (OV-04x) across multiple admissible windows.
- No parameter over-interpretation: β is not inferred / compatible with 0 (see DR-β-03).
- Deterministic reproduction: regeneration from frozen inputs reproduces the result deterministically.
- Negative result admissible: null/absence and preference-flip outcomes are allowed and must be recorded.

External anchor: None

External evidence: None



ID: OV-04x

Name: OV-04x fit-family robustness gate on DS-02 low-k dataset (linear vs curved)

Category: Observable

Short description: Applies the same robustness-only fit-family preference structure as OV-01g to a new independent low-k external dataset (DS-02), using frozen window artifacts generated from the DS-02 packet.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov04_fit_family_robustness_lowk_ds02.py; formal/python/tests/test_ov04_fit_family_robustness_gate_ds02_dataset.py; formal/python/tests/test_ov04x_empirically_anchored_requires_ea04a.py; formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md

Scope / limits: Robustness-only selector evaluation on a low-k dataset. Not a physics claim; must not be used for β inference (see DR-β-03). Low-k dataset; does not generalize; no continuity claim.

Dependencies: DS-02-EVIDENCE-DIGITIZATION, DR-β-03, EA-04a

Notes: OV-04x is intended as an independent low-k anchor slot. β is not inferred (compatible with 0; see DR-β-03). Until DS-02 artifacts exist, the gate test must explicitly skip.

External anchor: Bragg spectroscopy of BEC excitations (low-k external dataset)

External evidence: TBD (see DS-02 packet)



ID: OV-DQ-01

Name: OV-DQ-01 DQ-01_v1 diagnostic/audit record (OV-04x DS-02; OV-03x B1)

Category: Observable

Short description: Deterministic auditability record for DQ-01 curved-fit adequacy (metrics + reason codes per window) plus robustness summary fields (q-ratio, thresholds, deterministic failure reasons) for OV-04x and OV-03x.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ovdq01_dq01_diagnostics_record.py; formal/python/tests/test_ov_dq01_dq01_diagnostics_record_lock.py; formal/markdown/locks/observables/OV-DQ-01_dq01_diagnostics_record.md

Evidence (drilldown): formal/python/toe/observables/ovdq01_adequacy_drilldown_record.py; formal/python/tools/ovdq01_adequacy_drilldown_record.py; formal/python/tests/test_ov_dq01_adequacy_drilldown_artifact.py; formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_adequacy_drilldown.json

Evidence (DS-02 units invariant): formal/python/toe/observables/ovdq01_ds02_units_invariant.py; formal/python/tools/ovdq01_ds02_units_invariant.py; formal/python/tests/test_ov_dq01_ds02_units_invariant_artifact.py; formal/python/artifacts/diagnostics/OV-DQ-01/DS02_units_invariant.json

Evidence (q_ratio decomposition): formal/python/toe/observables/ovdq01_qratio_decomposition_record.py; formal/python/tools/ovdq01_qratio_decomposition_record.py; formal/python/tests/test_ov_dq01_qratio_decomposition_artifact.py; formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_qratio_decomposition.json

Evidence (policy sensitivity): formal/python/toe/observables/ovdq01_policy_sensitivity_record.py; formal/python/tools/ovdq01_policy_sensitivity_record.py; formal/python/tests/test_ov_dq01_policy_sensitivity_artifact.py; formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json

Scope / limits: Diagnostic/bookkeeping record only; per-dataset diagnostics (no cross-dataset comparability claim). No continuity claim; no averaging across regimes; β not inferred / β-null posture; must not be used for β inference.

Dependencies: OV-04x, OV-03x, DR-β-02, DR-β-03

Notes: This record does not change DQ-01 policy; it exposes the deterministic metrics/reason codes already used by DQ-01_v1 (and the robustness summaries that consume them) to make gate outcomes auditable.

External anchor: None

External evidence: None



ID: OV-SEL-01

Name: OV-SEL-01 selection status narrative (DQ-01_v1; OV-04x vs OV-03x; overlap-only)

Category: Observable

Short description: Single, policy-interpretable, locked narrative of the current DQ-01_v1 selection consequences: OV-04x (DS-02 low-k) is decisive; OV-03x (B1) remains undecided only due to q_ratio gating; overlap-only comparison (OV-XD-04) is one-decisive with no continuity claim.

Status: Locked

Evidence: formal/python/toe/observables/ovsel01_selection_status_record.py; formal/python/tools/ovsel01_selection_status_record.py; formal/python/tests/test_ov_sel01_selection_status_lock.py; formal/markdown/locks/observables/OV-SEL-01_selection_status.md

Scope / limits: Bookkeeping/narrative only; no physics claim; no policy change. Computed from existing locks. No continuity claim; no averaging across regimes; overlap-only comparability; β not inferred / β-null posture.

Dependencies: OV-04x, OV-03x, OV-DQ-01, OV-XD-03, OV-XD-04

Notes: This record is the canonical “current truth” snapshot after clearing curved adequacy via windowing (Path 2). Further changes should not be additional windowing; policy evolution (e.g., DQ-01_v2) requires explicit justification via pinned diagnostics (policy sensitivity + q_ratio decomposition).

External anchor: None

External evidence: None



ID: OV-SEL-02

Name: OV-SEL-02 selection status comparison (DQ-01_v1 vs DQ-01_v2; OV-01g/OV-02x/OV-03x/OV-04x)

Category: Observable

Short description: Computed, locked narrative comparing selection status under DQ-01_v1 (q_threshold=0.90) vs DQ-01_v2 (q_threshold=1.05) for the evaluated set {OV-01g, OV-02x, OV-03x, OV-04x} using the pinned OV-DQ-01 policy sensitivity artifact.

Status: Locked

Evidence: formal/python/toe/observables/ovsel02_selection_status_record.py; formal/python/tools/ovsel02_selection_status_record.py; formal/python/tests/test_ov_sel02_selection_status_policy_compare_lock.py; formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md

Scope / limits: Bookkeeping/narrative only; no physics claim; evaluated set limited to the observables represented in the pinned policy sensitivity artifact. No continuity claim; no averaging across regimes; β not inferred / β-null posture.

Dependencies: OV-DQ-01

Notes: This record is intended as a stable narrative basis for proposing DQ-01_v2 as a threshold-only evolution (in observed effect set) after adequacy confounds were cleared (Path 2).

Policy selector convention: canonical DQ-01_v1 corresponds to (adequacy_policy='DQ-01_v1', q_threshold=0.90); the parallel threshold-only variant labeled DQ-01_v2 corresponds to (adequacy_policy='DQ-01_v2', q_threshold=1.05), with non-canonical locks suffixed `_DQ-01_v2.md`.

External anchor: None

External evidence: None



ID: OV-DQ-02

Name: OV-DQ-02 DQ-01_v2 threshold update policy lock (q_threshold 0.90 -> 1.05)

Category: Observable

Short description: Computed policy-change lock documenting the proposed DQ-01_v2 threshold update (q_threshold=1.05 vs 0.90) and citing pinned diagnostic evidence showing the observed impact set in the evaluated suite.

Status: Locked

Evidence: formal/python/toe/observables/ovdq02_dq01_v2_threshold_update_record.py; formal/python/tools/ovdq02_dq01_v2_threshold_update_record.py; formal/python/tests/test_ov_dq02_dq01_v2_threshold_update_lock.py; formal/markdown/locks/policies/DQ-01_v2_threshold_update.md

Scope / limits: Bookkeeping/policy documentation only; no physics claim. Does not mutate canonical selection.

Dependencies: OV-DQ-01

Notes: This lock records that, within the evaluated set {OV-01g, OV-02x, OV-03x, OV-04x}, only OV-03x changes status when q_threshold is increased from 0.90 to 1.05.

Policy selector convention: canonical DQ-01_v1 corresponds to (adequacy_policy='DQ-01_v1', q_threshold=0.90); the parallel threshold-only variant labeled DQ-01_v2 corresponds to (adequacy_policy='DQ-01_v2', q_threshold=1.05), with non-canonical locks suffixed `_DQ-01_v2.md`.

External anchor: None

External evidence: None



ID: OV-DQ-03

Name: OV-DQ-03 DQ-01 active policy activation record (DQ-01_v2 active; v1 baseline)

Category: Policy

Short description: Computed activation lock explicitly declaring the active DQ-01 policy posture (DQ-01_v2 active while retaining DQ-01_v1 as baseline), with a pinned guardrail on the observed impact set and no implicit selection mutation.

Status: Locked

Evidence: formal/python/toe/observables/ovdq03_dq01_active_policy_activation_record.py; formal/python/tools/ovdq03_dq01_active_policy_activation_record.py; formal/python/tests/test_ov_dq03_dq01_active_policy_activation_lock.py; formal/markdown/locks/policies/DQ-01_active_policy_activation.md

Scope / limits: Bookkeeping/policy activation only; no physics claim. Does not itself change any selection outputs except by explicitly choosing which already-defined policy selector is treated as active in narrative bookkeeping.

Dependencies: OV-DQ-02, OV-SEL-02

Notes: This is the explicit, auditable “active policy” switch required for canonical bookkeeping to follow DQ-01_v2.

External anchor: None

External evidence: None



ID: OV-BM-01

Name: OV-BM-01 benchmark — mean-field line shift scaling (symbolic; non-validating)

Category: Benchmark

Short description: Baseline benchmark observable encoding a symbolic mean-field density–shift proportionality (first moment, not a dispersion curve) used solely to stress-test regime handling and provenance preservation without digitization or fitting.

Status: Structural (symbolic)

Evidence: formal/python/toe/observables/ovbm01_mean_field_line_shift_scaling_benchmark.py; formal/python/tools/ovbm01_mean_field_line_shift_scaling_benchmark.py; formal/python/tests/test_ov_bm01_mean_field_line_shift_scaling_benchmark_lock.py; formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling.md

Scope / limits: Symbolic-only; no digitization; no extracted points; no curve fitting; no regime averaging; no continuity claim; no cross-observable inference. Non-decisive by design; does not participate in fit-family selection.

Dependencies: None

Notes: Reference provenance only (Stenger 1999); benchmark-only classification; does not validate any ToE mechanism or imply continuity across regimes.

External anchor: None

External evidence: None



ID: OV-BM-01N

Name: OV-BM-01N digitized benchmark — mean-field mean shift vs peak density (benchmark-only)

Category: Benchmark

Short description: Minimal numeric digitization target for OV-BM-01 (panel a, filled-circle series) stored as a frozen CSV + JSON metadata wrapper under formal/external_evidence; intended solely to stress-test numeric ingestion determinism and provenance preservation.

Status: Locked

Evidence: formal/python/toe/observables/ovbm01_mean_field_line_shift_scaling_digitized.py; formal/python/tools/ovbm01_mean_field_line_shift_scaling_digitized.py; formal/python/tests/test_ov_bm01_digitized_mean_shift_lock.py; formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling_digitized.md; formal/external_evidence/bec_bragg_stenger_1999/ovbm01_digitization/mean_shift_vs_peak_density.csv; formal/external_evidence/bec_bragg_stenger_1999/ovbm01_digitization/mean_shift_vs_peak_density.metadata.json

Scope / limits: Benchmark-only numeric ingestion; no fitting; no regime averaging; no continuity claim; no cross-observable inference. Non-decisive by design.

Dependencies: OV-BM-01

Notes: This is the “smallest acceptable target” under BM-DIG-01; values are approximate (manual transcription from a pinned screenshot) and are not used for validation.

External anchor: None

External evidence: formal/external_evidence/bec_bragg_stenger_1999/9901109v1.pdf; formal/external_evidence/bec_bragg_stenger_1999/Screenshot 2026-01-23 234806.png



ID: OV-BM-02

Name: OV-BM-02 benchmark — linewidth quadrature composition (symbolic; non-validating)

Category: Benchmark

Short description: Baseline benchmark observable encoding a symbolic quadrature linewidth composition rule (sum of squares of independent contributions) used to stress-test preservation of separated mechanisms without forced averaging or regime blending.

Status: Structural (symbolic)

Evidence: formal/python/toe/observables/ovbm02_linewidth_quadrature_composition_benchmark.py; formal/python/tools/ovbm02_linewidth_quadrature_composition_benchmark.py; formal/python/tests/test_ov_bm02_linewidth_quadrature_composition_benchmark_lock.py; formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition.md

Scope / limits: Symbolic-only; no digitization; no extracted points; no curve fitting; no dominance/crossover claims; no regime averaging; no continuity claim; no cross-observable inference. Non-decisive by design; does not participate in fit-family selection.

Dependencies: None

Notes: Reference provenance only (Stenger 1999); benchmark-only classification; does not validate any ToE mechanism or imply continuity across regimes.

External anchor: None

External evidence: None



ID: OV-BM-02N

Name: OV-BM-02N digitized benchmark — linewidth vs peak density (triangles; benchmark-only)

Category: Benchmark

Short description: Minimal numeric digitization target for OV-BM-02 (triangle-marker series) stored as a frozen CSV + JSON metadata wrapper under formal/external_evidence; intended solely to stress-test numeric ingestion determinism and provenance preservation.

Status: Locked

Evidence: formal/python/toe/observables/ovbm02_linewidth_quadrature_composition_digitized.py; formal/python/tools/ovbm02_linewidth_quadrature_composition_digitized.py; formal/python/tests/test_ov_bm02_digitized_linewidth_lock.py; formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition_digitized.md; formal/external_evidence/bec_bragg_stenger_1999/ovbm02_digitization/linewidth_vs_peak_density_triangles.csv; formal/external_evidence/bec_bragg_stenger_1999/ovbm02_digitization/linewidth_vs_peak_density_triangles.metadata.json

Scope / limits: Benchmark-only numeric ingestion; no fitting; no regime averaging; no continuity claim; no cross-observable inference. Non-decisive by design.

Dependencies: OV-BM-02

Notes: Deterministic extraction from a pinned screenshot with an exact-marker-count gate; values are approximate and are not used for validation.

External anchor: None

External evidence: formal/external_evidence/bec_bragg_stenger_1999/9901109v1.pdf



ID: OV-SW-01

Name: OV-SW-01 shallow-water low-k slope (schema-only; Axis C lane)

Category: Observable

Short description: Schema-only definition for an independent third lane (Axis C) recording a low-k dispersion slope and a purely dimensional unit-identity export to a velocity-like quantity (m/s), with explicit non-claims and no cross-lane mapping.

Status: Hypothesis

Evidence: formal/docs/lanes/OV-SW-01_shallow_water_lowk_slope_schema.md; formal/external_evidence/shallow_water_TBD/ovsw01_digitization/README.md

Scope / limits: Schema/infrastructure only; no computation yet; no external anchoring; no physics claim; no cross-lane comparability; no mapping tuples.

Dependencies: None

Notes: Intended solely as a method-generalization lane to stress-test “blocked” and “absence-preserving” governance behavior without importing interpretation.

External anchor: None

External evidence: None



ID: OV-SND-01

Name: OV-SND-01 anchor — BEC sound-speed scaling (symbolic; non-validating)

Category: Observable

Short description: Symbolic-first external anchor defining the dependency structure for sound propagation in a dilute BEC (phonon regime), recording the qualitative scaling $c \propto \sqrt{n}$ under a pinned external source; explicitly non-decisive and non-validating.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd01_sound_speed_scaling_record.py; formal/python/tools/ovsnd01_sound_speed_scaling_record.py; formal/python/tests/test_ov_snd01_sound_speed_scaling_lock.py; formal/markdown/locks/observables/OV-SND-01_sound_speed_scaling_anchor.md

Scope / limits: Symbolic-only; no fitting; no parameter inference; no continuity claim; no regime averaging; no cross-observable inference. Non-decisive by design; does not participate in selection.

Dependencies: None

Notes: Uses the pinned arXiv:9711224v1 note (Kavoulakis & Pethick, 1997), which discusses sound propagation in elongated condensates and references the Andrews et al. experiment.

External anchor: None

External evidence: formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf



ID: OV-SND-01N

Name: OV-SND-01N digitized anchor — sound propagation distance vs time (squares)

Category: Observable

Short description: Minimal numeric digitization of Fig. 2 (square-marker series) from the pinned arXiv:9711224v1 PDF; stored as frozen CSV + JSON metadata wrapper under formal/external_evidence; intended solely to stress-test deterministic ingestion of a second external anchor.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd01_sound_propagation_distance_time_digitized.py; formal/python/tools/ovsnd01_sound_propagation_distance_time_digitized.py; formal/python/tests/test_ov_snd01_digitized_distance_time_lock.py; formal/markdown/locks/observables/OV-SND-01_sound_propagation_distance_time_digitized.md; formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.csv; formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.metadata.json

Scope / limits: Anchor numeric ingestion only; no fitting; no parameter inference; no continuity claim; no regime averaging; no cross-observable inference. Non-decisive by design.

Dependencies: OV-SND-01

Notes: Digitization is deterministic marker extraction from a pinned cropped render (fig2_region_page4_z4.png) with an exact-marker-count gate.

External anchor: None

External evidence: formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf; formal/external_evidence/bec_sound_andrews_1997/fig2_region_page4_z4.png



ID: OV-SND-01N2

Name: OV-SND-01N2 digitized anchor — split square-marker propagation series (deterministic)

Category: Observable

Short description: Deterministic ingestion record that reuses the pinned Andrews propagation plot render and applies a pinned split rule to separate the square-marker distance-vs-time points into two series (seriesA/seriesB) without manual intervention; remains blocked if separation is not justified by the pinned rule.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd01n2_sound_propagation_distance_time_digitized.py; formal/python/tools/ovsnd01n2_sound_propagation_distance_time_digitized.py; formal/python/tests/test_ov_snd01n2_sound_propagation_distance_time_digitized_lock.py; formal/markdown/locks/observables/OV-SND-01N2_sound_propagation_distance_time_digitized.md

Scope / limits: Bookkeeping only; no physics claim. Deterministic split; no manual clicking; no fabricated points.

Dependencies: OV-SND-01

Notes: Intended to provide a second sound-speed condition path without changing the OV-SND-01N extraction rule; acts as a prerequisite for OV-SND-02B.

External anchor: None

External evidence: formal/external_evidence/bec_sound_andrews_1997/page4_z4.png



ID: OV-SND-02

Name: OV-SND-02 derived sound speed from propagation (slope; conservative)

Category: Observable

Short description: Deterministic derived sound-speed observable computed from the frozen OV-SND-01N distance-vs-time points using a pinned through-origin slope rule plus a pinned uncertainty estimate (slope standard error). Intended as a directly interpretable anchor quantity without density inference.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd02_sound_speed_from_propagation_record.py; formal/python/tools/ovsnd02_sound_speed_from_propagation_record.py; formal/python/tests/test_ov_snd02_sound_speed_from_propagation_lock.py; formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md

Scope / limits: Derived from frozen points only; pinned slope rule (no free creativity); no density inference; no continuity claim; no regime averaging; no cross-observable inference. Non-decisive by design.

Dependencies: OV-SND-01N

Notes: Density dependence is not inferred here; symbolic scaling remains recorded separately in OV-SND-01.

External anchor: None

External evidence: None



ID: OV-SND-02B

Name: OV-SND-02B derived sound speed from propagation (seriesB; conservative)

Category: Observable

Short description: Deterministic derived sound-speed observable computed from the frozen OV-SND-01N2 seriesB distance-vs-time points using a pinned through-origin slope rule plus a pinned uncertainty estimate (slope standard error).

Status: Locked

Evidence: formal/python/toe/observables/ovsnd02b_sound_speed_from_propagation_seriesb_record.py; formal/python/tools/ovsnd02b_sound_speed_from_propagation_seriesb_record.py; formal/python/tests/test_ov_snd02b_sound_speed_from_propagation_seriesb_lock.py; formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md

Scope / limits: Derived from frozen points only; pinned slope rule (no free creativity); no density inference; no continuity claim; no regime averaging; no cross-observable inference. Non-decisive by design.

Dependencies: OV-SND-01N2

Notes: Provides a second sound-speed condition derived from the same pinned Andrews source under a deterministic series split.

External anchor: None

External evidence: None



ID: OV-SND-03N

Name: OV-SND-03N digitized anchor — central density from pinned sound PDF

Category: Observable

Short description: Minimal numeric digitization of a single explicitly stated central density value from the pinned arXiv:9711224v1 sound PDF; stored as frozen CSV + JSON metadata wrapper under formal/external_evidence; intended solely to introduce density as a second independent variable without implying density dependence.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd03n_central_density_digitized.py; formal/python/tools/ovsnd03n_central_density_digitized.py; formal/python/tests/test_ov_snd03n_central_density_digitized_lock.py; formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md; formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.csv; formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.metadata.json

Scope / limits: Anchor numeric ingestion only; single-condition density anchor only; no fitting; no imputation; no density-dependence inference; no regime averaging; no continuity claim; no cross-observable inference. Non-decisive by design.

Dependencies: OV-SND-01, SND-DIG-01

Notes: Digitization is deterministic PDF text extraction + pinned regex; the extractor collapses typeset $10^{14}$ to “1014”, which is explicitly interpreted as $10^{14}\,\mathrm{cm}^{-3}$ in the record.

External anchor: None

External evidence: formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf



ID: OV-SND-03

Name: OV-SND-03 sound speed density scaling (derived; bookkeeping)

Category: Observable

Short description: Deterministic derived observable combining OV-SND-02 sound speed with OV-SND-03N density anchor to compute density-scaled quantities (e.g., $c/\sqrt{n_0}$ and $c^2/n_0$) under explicit unit conversions; single-condition only.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd03_sound_speed_density_scaling_record.py; formal/python/tools/ovsnd03_sound_speed_density_scaling_record.py; formal/python/tests/test_ov_snd03_sound_speed_density_scaling_lock.py; formal/markdown/locks/observables/OV-SND-03_sound_speed_density_scaling.md

Scope / limits: Derived bookkeeping only; single-condition only; no inference of density dependence; no continuity claim; no regime averaging; no cross-observable inference. Non-decisive by design.

Dependencies: OV-SND-02, OV-SND-03N

Notes: Reports both SI-scaled and cm-scaled forms to avoid silent unit confusion; does not test constancy across multiple densities.

External anchor: None

External evidence: None



ID: OV-SND-03N-COV

Name: OV-SND-03N-COV density coverage report (decision gate)

Category: Observable

Short description: Deterministic coverage report declaring how many density conditions are supported by the currently frozen sound-lane density artifact(s), how many speed conditions are supported by the current sound speed lane, and whether a multi-condition constancy check is feasible without cross-source mapping.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd03n_density_coverage_report_record.py; formal/python/tools/ovsnd03n_density_coverage_report_record.py; formal/python/tests/test_ov_snd03n_density_coverage_report_lock.py; formal/markdown/locks/observables/OV-SND-03N_density_coverage_report.md

Scope / limits: Bookkeeping only; no physics claim. Coverage + blockers only; no digitization performed.

Dependencies: OV-SND-02, OV-SND-03N

Notes: Intended to prevent “planning multi-condition” when the pinned density source supports only one explicit density value.

External anchor: None

External evidence: None



ID: OV-SND-03N2

Name: OV-SND-03N2 secondary-source multi-density conditions (digitization gate)

Category: Observable

Short description: Governance-safe ingestion record for a pinned secondary density source intended to provide multiple explicit density conditions as a frozen CSV + metadata; remains blocked until the secondary PDF and multi-row density table are pinned and hashed.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd03n2_secondary_density_conditions_digitized.py; formal/python/tools/ovsnd03n2_secondary_density_conditions_digitized.py; formal/python/tests/test_ov_snd03n2_secondary_density_conditions_digitized_lock.py; formal/markdown/locks/observables/OV-SND-03N2_secondary_density_conditions_digitized.md

Scope / limits: Bookkeeping only; no physics claim. No fabricated values; no cross-source condition identity assumptions.

Dependencies: OV-SND-03N-COV, OV-BR-SND-02

Notes: Unblocks only after a pinned secondary source exists under formal/external_evidence/bec_sound_density_secondary_TBD/.

External anchor: None

External evidence: formal/external_evidence/bec_sound_density_secondary_TBD/source.pdf (expected)



ID: OV-BR-SND-02

Name: OV-BR-SND-02 cross-source density mapping record (computed)

Category: Observable

Short description: Bookkeeping record declaring explicit mapping tuples linking sound-propagation condition keys (OV-SND-02 / OV-SND-02B) to density-condition keys (from pinned density tables). Used as a prerequisite for any density-conditioned sound analysis; does not infer density and does not assert condition identity beyond the explicit tuples.

Status: Locked

Evidence: formal/python/toe/observables/ovbr_snd02_cross_source_density_mapping_record.py; formal/python/tools/ovbr_snd02_cross_source_density_mapping_record.py; formal/python/tests/test_ov_br_snd02_cross_source_density_mapping_lock.py; formal/markdown/locks/observables/OV-BR-SND-02_cross_source_density_mapping.md

Scope / limits: Bookkeeping only; no physics claim. No implied condition identity across sources; no continuity claim; no averaging.

Dependencies: OV-SND-02, OV-SND-03N-COV

Notes: Current record is unblocked and includes explicit mapping tuples (see OV-BR-SND-02 lock). This mapping is necessary but not sufficient for Bragg↔Sound cross-anchor pairing (which requires separate explicit pairing tuples).

External anchor: None

External evidence: None



ID: OV-BR-SND-03

Name: OV-BR-SND-03 cross-lane low-k consistency audit (computed)

Category: Observable

Short description: Conservative audit ingesting locked Sound-lane derived speeds (OV-SND-02/02B) and Bragg-lane derived low-k slopes (OV-BR-04A/04B) and emitting either (i) a quantitative consistency check under pinned unit conversion + tolerance, or (ii) an explicit “absent” conclusion if no justified Bragg↔Sound pairing mapping exists.

Status: Locked

Evidence: formal/python/toe/observables/ovbr_snd03_cross_lane_lowk_consistency_audit_record.py; formal/python/tests/test_ov_br_snd03_cross_lane_lowk_consistency_audit_lock.py; formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit.md

Scope / limits: Bookkeeping/audit only; no physics claim. Runs even without mapping; “absent” comparability is a valid conclusion. May be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: OV-SND-02, OV-SND-02B, OV-BR-04A, OV-BR-04B, OV-BR-02, CT-01, SYM-01, CAUS-01

Notes: Conversion chain and tolerance are pinned in the record; pairing mappings are explicitly optional external-evidence inputs under TBD slots.

Scientific status note (2026-02-01)
- Two-mode cross-anchor reporting exists:
	- justified_only gated report (+ suppressed reasons): formal/output/cross_anchor_bragg_vs_sound_20260201_123051_720171.md
	- (older runs retained under formal/output/cross_anchor_bragg_vs_sound_20260129_*.md)
- Current state is mapping-backed: JUSTIFIED=2, SUPPRESSED=2 (TOTAL=4).
- Evidence inputs now present (fail-closed for unmapped combinations):
	- OV-BR-SND-03 audit comparability.status is established (pinned conversion + tolerance; computed only for explicitly paired rows)
	- OV-BR-SND-01 comparability gate is OK (comparable_in_principle=True, current_blockers=[])
	- Explicit Bragg↔Sound pairing tuples (v4): formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json (mapping_tuples_count=2)
- Suppression logic is active: unpaired Bragg↔Sound combinations remain SUPPRESSED with explicit reasons.

External anchor: Bragg ↔ Sound low-k consistency (cross-lane audit)

External evidence: None



ID: OV-BR-03

Name: OV-BR-03N digitized Bragg dispersion ω(k) under two explicit conditions

Category: Observable

Short description: Deterministic digitization of Shammass et al. Fig. 2 Bragg dispersion points (ω/2π vs k) under two explicitly declared conditions (filled vs open circles), producing frozen CSV + metadata artifacts and a locked audit record.

Status: Locked

Evidence: formal/python/toe/observables/ovbr03n_bragg_dispersion_k_omega_digitized.py; formal/python/tests/test_ov_br03n_bragg_dispersion_digitized_lock.py; formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md; formal/external_evidence/bec_bragg_shammass_2012/source.pdf; formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png; formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/condition_A.csv; formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/condition_B.csv; formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/k_omega_digitization.metadata.json

Scope / limits: Anchor numeric ingestion only; render-based extraction (axis text is rasterized); no fitting; no regime averaging; no continuity claim; no cross-observable inference.

Dependencies: None

Notes: Axis ranges are pinned as constants; deterministic pixel→data affine mapping; inset panels are excluded by heuristic masks.

External anchor: Bragg spectroscopy dispersion (Shammass et al. 2012)

External evidence: formal/external_evidence/bec_bragg_shammass_2012/source.pdf



ID: OV-BR-04A

Name: OV-BR-04A derived low-k Bragg slope (condition_A)

Category: Observable

Short description: Deterministic derived low-k slope estimate from OV-BR-03 condition_A using a pinned selection window and pinned through-origin OLS rule, including a conservative slope standard error.

Status: Locked

Evidence: formal/python/toe/observables/ovbr04a_bragg_lowk_slope_conditionA_record.py; formal/python/tests/test_ov_br04_lowk_slope_locks.py; formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md

Scope / limits: Derived from frozen OV-BR-03 points only; pinned selection + estimator; no ToE validation claim; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: OV-BR-03, CT-01, SYM-01, CAUS-01

Notes: Pinned selection rule is lowk_window_v1 (k<=1.0, 0.1<=ω/2π<=1.3). Unit bookkeeping pins 1 (kHz)/(um^-1) = 1 mm/s.

External anchor: Bragg spectroscopy dispersion (Shammass et al. 2012)

External evidence: formal/external_evidence/bec_bragg_shammass_2012/source.pdf



ID: OV-BR-04B

Name: OV-BR-04B derived low-k Bragg slope (condition_B)

Category: Observable

Short description: Same as OV-BR-04A, but for OV-BR-03 condition_B.

Status: Locked

Evidence: formal/python/toe/observables/ovbr04b_bragg_lowk_slope_conditionB_record.py; formal/python/tests/test_ov_br04_lowk_slope_locks.py; formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md

Scope / limits: Derived from frozen OV-BR-03 points only; pinned selection + estimator; no ToE validation claim; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: OV-BR-03, CT-01, SYM-01, CAUS-01

Notes: Shares the same pinned lowk_window_v1 rule and estimator as OV-BR-04A.

External anchor: Bragg spectroscopy dispersion (Shammass et al. 2012)

External evidence: formal/external_evidence/bec_bragg_shammass_2012/source.pdf



ID: OV-BR-05

Name: OV-BR-05 Bragg low-k slope summary (computed)

Category: Observable

Short description: Summary-only table derived from locked OV-BR-04A/04B exporting the primary low-k slopes (and unit-converted velocity candidates) for condition_A and condition_B under the pinned lowk_window_v1 selection.

Status: Locked

Evidence: formal/python/toe/observables/ovbr05_bragg_lowk_slope_summary_record.py; formal/python/tests/test_ov_br05_bragg_lowk_slope_summary_lock.py; formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary.md

Scope / limits: Bookkeeping/summary only; no physics claim; no refitting; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: OV-BR-04A, OV-BR-04B, CT-01, SYM-01, CAUS-01

Notes: Intended as a Phase-3 “candidate table” surface for Bragg low-k slope outcomes, without introducing any new selection policy.

External anchor: Bragg spectroscopy dispersion (Shammass et al. 2012)

External evidence: formal/external_evidence/bec_bragg_shammass_2012/source.pdf



ID: OV-DR-BR-01

Name: OV-DR-BR-01 candidate pruning table (DR-01 → BR-01; summary-only)

Category: Observable

Short description: Deterministic eliminative bookkeeping table for the DR-01 → BR-01 loop that enumerates the canonical BR-01 candidate IDs and reports per-candidate status as {true,false,unknown} with reason codes, using OV-BR-05 as the single canonical Bragg slope summary input.

Status: Locked

Evidence: formal/python/toe/observables/ovdrbr01_candidate_pruning_table_record.py; formal/python/tests/test_ov_dr_br01_candidate_pruning_table_lock.py; formal/markdown/locks/observables/OV-DR-BR-01_candidate_pruning_table.md; formal/python/toe/observables/ovdrbr01_lane_profile.py; formal/python/tests/test_ov_dr_br01_elimination_without_override_lane.py

Scope / limits: Summary-only / eliminative-only; unknown is not fail; no numeric interpretation; no new claims; blocked-by-default if OV-BR-05 or OV-DR-BR-00 lock missing; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: OV-BR-05, OV-DR-BR-00, CT-01, SYM-01, CAUS-01

Notes: Candidate ID surface is structural: BR01_* function names extracted from formal/python/toe/bridges/br01_candidates.py. Current pruning outcome (2026-01-25): BR01_metric_from_DR01_fit_unit_density survives_br01_constraints=true (declared_br05_structure_satisfied) per OV-DR-BR-01 lock. Canonical closeout verification (2026-02-04): summary.counts={true:2,false:1,unknown:1}; true=[BR01_metric_from_DR01_fit_constant_density, BR01_metric_from_DR01_fit_unit_density]; false=[BR01_metric_from_DR01_fit_unit_density_structural_fail]; unknown=[BR01_metric_from_DR01_fit_rest_frame_u0]; status.blocked=true under formal/markdown locks/gates/admissibility_manifest.json. A2 hardening checkpoint (2026-02-08): canonical non-override lane is manifest-parsed via OVDRBR01LaneProfile, with eliminator existence, controlled reason-code atoms, and survivor guard lock-enforced.



ID: OV-CV-01

Name: OV-CV-01 BEC-Bragg comparator lanes (v0 integrity + v1 discriminative candidate)

Category: Observable

Short description: Deterministic comparator record for pinned domain DRBR-DOMAIN-01 that consumes typed/fingerprinted DR-01 linear+curved artifacts through BR-01 front-door mappings and emits pass/fail rows with explicit reason codes.

Status: Locked

Evidence: formal/python/toe/comparators/cv01_bec_bragg_v0.py; formal/python/tests/test_cv01_bec_bragg_v0_front_door.py; formal/python/tests/test_cv01_bec_bragg_v0_surface_contract_freeze.py; formal/python/tests/test_cv01_v1_discriminative_design_gate_doc.py; formal/docs/cv01_bec_bragg_v0_front_door_contract.md; formal/docs/cv01_v1_discriminative_design_gate.md; formal/docs/first_empirical_comparator_domain_bec_bragg.md; formal/python/tests/test_first_empirical_comparator_domain_selection.py; formal/python/toe/comparators/cv01_bec_bragg_v1.py; formal/python/tests/test_cv01_bec_bragg_v1_front_door.py; formal/python/tests/test_cv01_bec_bragg_v1_surface_contract_freeze.py; formal/python/tests/test_cv01_numeric_tolerance_policy_doc.py; formal/docs/cv01_bec_bragg_v1_front_door_contract.md; formal/docs/cv01_numeric_tolerance_policy.md

Scope / limits: Dual-lane comparator surface: v0 integrity-only (`comparator_role=integrity_only`) and v1 discriminative-candidate (`comparator_role=discriminative_candidate`) with cross-artifact residual `abs(c_s-c0)` under `TOE_CV01_TOLERANCE_PROFILE` (`pinned`/`portable`); deterministic records only; typed artifacts only; no external truth claim; blocked when pinned domain artifacts are missing; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: DR-01, BR-01, OV-DR-BR-01, CT-01, SYM-01, CAUS-01

Notes: CV01 v0 remains frozen as a pipeline-integrity comparator. CV01 v1 is implemented as a separate schema surface with non-tautological cross-artifact speed residual checks, deterministic cross/curved negative controls, and contract-complete blocked-output shape; tolerance policy is explicitly governed by `formal/docs/cv01_numeric_tolerance_policy.md` (`TOE_CV01_TOLERANCE_PROFILE`). Domain pin source is `formal/docs/first_empirical_comparator_domain_bec_bragg.md` with canonical artifacts `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json` and `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json`.

External anchor: BEC Bragg low-k dispersion domain (Steinhauer 2001 family)

External evidence: formal/external_evidence/bec_bragg_steinhauer_2001/0111438v1.pdf


ID: OV-CV-BR-01

Name: OV-CV-BR-01 CV01 v1 -> pruning bridge (explicit reason-atom mapping)

Category: Observable

Short description: Deterministic bridge lane that maps CV01 v1 reason codes to pruning reason atoms via a versioned policy artifact and emits a summary-only eliminative record with attribution fields.

Status: Locked

Evidence: formal/python/toe/observables/ovcvbr01_cv01_v1_pruning_bridge_record.py; formal/python/toe/observables/cv01_v1_pruning_reason_policy.json; formal/python/tests/test_ov_cv_br01_cv01_v1_pruning_bridge_lock.py; formal/python/tests/test_ov_cv_br01_cv01_v1_elimination_attribution.py; formal/python/tests/test_cv01_v1_pruning_reason_policy.py; formal/markdown/locks/observables/OV-CV-BR-01_cv01_v1_pruning_bridge.md; formal/markdown/locks/observables/OV-CV-BR-01_cv01_v1_pruning_bridge_NEG_CONTROL.md

Scope / limits: Summary-only / eliminative-only bookkeeping; explicit policy mapping only; no implicit coupling with BR-only pruning lanes; no numeric interpretation; no external truth claim.

Dependencies: OV-CV-01, OV-DR-BR-01, CT-01, SYM-01, CAUS-01

Notes: Canonical lock currently yields zero CV01-attributed eliminations under domain-01; negative-control lock proves deterministic attributed elimination with survivor guard preserved.



ID: DRBR-DOMAIN-02

Name: DRBR-DOMAIN-02 second empirical comparator domain pin (BEC Bragg B1)

Category: Governance

Short description: Pinned second comparator domain record for BEC Bragg secondary-source artifacts (B1 lane), including canonical artifact paths and non-claim posture.

Status: Locked

Evidence: formal/docs/second_empirical_comparator_domain_bec_bragg_b1.md; formal/python/tests/test_second_empirical_comparator_domain_selection.py

Scope / limits: Domain pin only; no truth upgrade; no automatic pruning activation.

Dependencies: DR-01

Notes: Domain-02 is explicitly pinned but remains constrained by front-door comparator contracts and blocked-on-missing-input behavior.



ID: OV-CV-02

Name: OV-CV-02 BEC-Bragg B1 comparator v0 (front-door deterministic record)

Category: Observable

Short description: Deterministic comparator record on DRBR-DOMAIN-02 artifacts with integrity-only semantics, blocked-on-missing-input behavior, schema freeze tests, and deterministic negative control coverage.

Status: Locked

Evidence: formal/python/toe/comparators/cv02_bec_bragg_b1_v0.py; formal/python/tests/test_cv02_bec_bragg_b1_v0_front_door.py; formal/python/tests/test_cv02_bec_bragg_b1_v0_surface_contract_freeze.py; formal/python/tests/test_second_empirical_comparator_domain_selection.py; formal/docs/second_empirical_comparator_domain_bec_bragg_b1.md

Scope / limits: Integrity-only comparator surface (`comparator_role=integrity_only`); deterministic record only; typed artifacts only; blocked when pinned domain artifacts are missing; no external truth claim.

Dependencies: DRBR-DOMAIN-02, DR-01, BR-01

Notes: This lane is domain-expansion governance and integrity instrumentation only; it does not assert cross-domain equivalence or physics truth.


ID: OV-DR-BR-00

Name: OV-DR-BR-00 BR-01 prediction declarations (structural)

Category: Observable

Short description: Schema-validated, hash-tracked declaration surface that records the formally declared BR-05-based prediction structure (if any) for each canonical BR-01 candidate ID. Used as a governance input to OV-DR-BR-01; produces eliminations only via declared prediction vs locked OV-BR-05 values (no inference).

Status: Locked

Evidence: formal/python/toe/observables/ovdrbr00_br01_prediction_declarations_record.py; formal/python/tests/test_ov_dr_br00_br01_prediction_declarations_lock.py; formal/markdown/locks/observables/OV-DR-BR-00_br01_prediction_declarations.md; formal/python/toe/bridges/br01_prediction_declarations.json

Scope / limits: Structural-only; no physics claim; blocked-by-default if the declaration source file is missing; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: CT-01, SYM-01, CAUS-01

Notes: The declaration source file is treated as governance input and is hash-tracked in the record inputs.



ID: OV-SEL-BR-01

Name: OV-SEL-BR-01 Bragg low-k slope audit (computed)

Category: Observable

Short description: Single governance/audit record for the Bragg lane that asserts lock==computed for OV-BR-03 and OV-BR-04A/04B, checks frozen artifact existence, and pins the low-k selection parameters used by the derived slope records.

Status: Locked

Evidence: formal/python/toe/observables/ovsel_br01_bragg_lowk_slope_audit_record.py; formal/python/tests/test_ov_sel_br01_bragg_lowk_slope_audit_lock.py; formal/markdown/locks/observables/OV-SEL-BR-01_bragg_lowk_slope_audit.md

Scope / limits: Bookkeeping/narrative only; no physics claim; does not select between conditions; asserts determinism and pinned parameters.

Dependencies: OV-BR-03, OV-BR-04A, OV-BR-04B

Notes: Intended as the Bragg-lane “current truth” snapshot used for safe re-entry (determinism + pinned window rule).

External anchor: Bragg spectroscopy dispersion (Shammass et al. 2012)

External evidence: formal/external_evidence/bec_bragg_shammass_2012/source.pdf



ID: OV-BR-FN-00

Name: OV-BR-FN-00 FN-01 metric-residual prediction declarations (structural)

Category: Observable

Short description: Schema-validated, hash-tracked declaration surface for FN-01 metric-residual predictions keyed by BR-01 candidate ID. Used as a governance input to OV-BR-FN-01; produces eliminations only via declared structure vs locked residual (no inference).

Status: Locked

Evidence: formal/python/toe/observables/ovbrfn00_fn01_metric_residual_prediction_declarations_record.py; formal/python/tests/test_ov_br_fn00_metric_residual_prediction_declarations_lock.py; formal/markdown/locks/observables/OV-BR-FN-00_fn01_metric_residual_prediction_declarations.md; formal/python/toe/bridges/brfn01_prediction_declarations.json

Scope / limits: Structural-only; no physics claim; blocked-by-default if the declaration source file is missing; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: CT-01, SYM-01, CAUS-01

Notes: The declaration source file is treated as governance input and is hash-tracked in the record inputs.



ID: OV-BR-FN-01

Name: OV-BR-FN-01 FN-01 metric-residual pruning table (BR→FN; summary-only)

Category: Observable

Short description: Deterministic eliminative bookkeeping table derived from the FN-01 cross-fit metric residual lock and OV-BR-FN-00 declarations, reporting per-candidate status as {true,false,unknown} with reason codes; unknown is not fail.

Status: Locked

Evidence: formal/python/toe/observables/ovbrfn01_fn01_metric_residual_pruning_table_record.py; formal/python/tests/test_ov_br_fn01_metric_residual_pruning_table_lock.py; formal/python/tests/test_ov_br_fn01_override_manifest_true_false.py; formal/markdown/locks/observables/OV-BR-FN-01_fn01_metric_residual_pruning_table.md

Scope / limits: Summary-only / eliminative-only; unknown is not fail; no refitting; no new claims; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: FN-01l, OV-BR-FN-00, CT-01, SYM-01, CAUS-01

Notes: Default posture remains blocked-by-default; explicit enabled-manifest runs are written to *_OVERRIDE.md locks.



ID: OV-FN-WT-00

Name: OV-FN-WT-00 FN-01 weight-policy declarations (structural)

Category: Observable

Short description: Schema-validated, hash-tracked declaration surface for FN-01 weight policy candidates (declared scalar weights + thresholds). Used as governance input to OV-FN-WT-01.

Status: Locked

Evidence: formal/python/toe/observables/ovfnwt00_fn01_weight_policy_declarations_record.py; formal/python/tests/test_ov_fn_wt00_weight_policy_declarations_lock.py; formal/markdown/locks/observables/OV-FN-WT-00_fn01_weight_policy_declarations.md; formal/python/toe/bridges/fnwt01_weight_policy_declarations.json

Scope / limits: Structural-only; no physics claim; blocked-by-default if the declaration source file is missing; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: CT-01, SYM-01, CAUS-01

Notes: The declaration source file is treated as governance input and is hash-tracked in the record inputs.



ID: OV-FN-WT-01

Name: OV-FN-WT-01 pruning table (FN weight policies; summary-only)

Category: Observable

Short description: Deterministic eliminative bookkeeping table that applies the declared FN weight policies to the locked FN-01 cross-fit residual scalar and reports per-policy status as {true,false,unknown} with reason codes; unknown is not fail.

Status: Locked

Evidence: formal/python/toe/observables/ovfnwt01_fn01_weight_policy_pruning_table_record.py; formal/python/tests/test_ov_fn_wt01_weight_policy_pruning_table_lock.py; formal/python/tests/test_ov_fn_wt01_override_manifest_true_false.py; formal/markdown/locks/observables/OV-FN-WT-01_fn01_weight_policy_pruning_table.md

Scope / limits: Summary-only / eliminative-only; unknown is not fail; applies declared thresholds to a locked scalar; no new claims; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: FN-01l, OV-BR-FN-01, OV-FN-WT-00, CT-01, SYM-01, CAUS-01

Notes: This stage is intentionally eliminative-only; selection is recorded separately by OV-FN-WT-02.



ID: OV-FN-WT-02

Name: OV-FN-WT-02 selected FN weight policy (computed selection)

Category: Observable

Short description: Deterministically selects the unique surviving FN weight policy from OV-FN-WT-01. If 0 or >1 policies survive, the record is blocked with explicit reason codes.

Status: Locked

Evidence: formal/python/toe/observables/ovfnwt02_selected_weight_policy_record.py; formal/python/tests/test_ov_fn_wt02_selected_weight_policy_lock.py; formal/markdown/locks/observables/OV-FN-WT-02_selected_weight_policy.md

Scope / limits: Selection-only bookkeeping; no new claims; deterministic; consumes only existing locks; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: OV-FN-WT-01, CT-01, SYM-01, CAUS-01

Notes: This is the first place where eliminations become a recorded downstream choice.



ID: OV-FN-02

Name: OV-FN-02 weighted residual audit (computed)

Category: Observable

Short description: Downstream audit record that consumes OV-FN-WT-02 and the FN-01 residual lock, then records the declared-weighted score and threshold outcome. Exists to make upstream eliminations propagate into a downstream reported consequence.

Status: Locked

Evidence: formal/python/toe/observables/ovfn02_weighted_residual_audit_record.py; formal/python/tests/test_ov_fn02_weighted_residual_audit_lock.py; formal/python/tests/test_ov_fn_wt02_override_policy_switch_changes_audit.py; formal/markdown/locks/observables/OV-FN-02_weighted_residual_audit.md

Scope / limits: Audit-only bookkeeping; applies declared weights to a locked scalar; no new claims; may be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).

Dependencies: FN-01l, OV-FN-WT-02, CT-01, SYM-01, CAUS-01

Notes: Under an enabled-manifest run, changing which policy survives changes this audit deterministically.



ID: OV-SND-04

Name: OV-SND-04 sound speed density constancy check (multi-condition; scaffold)

Category: Observable

Short description: Derived observable intended to compute $c/\sqrt{n_0}$ (and $c^2/n_0$) across multiple (c_i, n0_i) condition pairs and report pinned spread metrics (e.g., coefficient of variation and max fractional deviation) without fitting; currently blocked until >=2 condition pairs exist.

Status: Locked

Evidence: formal/python/toe/observables/ovsnd04_sound_speed_density_constancy_record.py; formal/python/tools/ovsnd04_sound_speed_density_constancy_record.py; formal/python/tests/test_ov_snd04_sound_speed_density_constancy_lock.py; formal/markdown/locks/observables/OV-SND-04_sound_speed_density_constancy.md

Scope / limits: Derived bookkeeping only; no universality claim; no continuity claim; no regime averaging; no cross-observable inference. Non-decisive by design.

Dependencies: OV-SND-02, OV-SND-03N, OV-SND-03N-COV

Notes: This is a scaffold that becomes the first true cross-condition scaling record once >=2 condition pairs are available.

External anchor: None

External evidence: None



ID: OV-SEL-SND-01

Name: OV-SEL-SND-01 sound anchor ingestion audit narrative (bookkeeping)

Category: Observable

Short description: OV-SEL-style locked narrative confirming that adding OV-SND-01 (symbolic) and OV-SND-01N (digitized) does not trigger any policy/threshold changes, regime bridge behavior changes, selection consequences, continuity claims, or averaging; includes deterministic lock==computed and artifact existence self-checks.

Status: Locked

Evidence: formal/python/toe/observables/ovsel_snd01_sound_anchor_ingestion_audit_record.py; formal/python/tools/ovsel_snd01_sound_anchor_ingestion_audit_record.py; formal/python/tests/test_ov_sel_snd01_sound_anchor_ingestion_audit_lock.py; formal/markdown/locks/observables/OV-SEL-SND-01_sound_anchor_ingestion_audit.md

Scope / limits: Bookkeeping/narrative only; no physics claim. Anchor numeric ingestion; no fitting; no regime averaging; no continuity claim; no cross-observable inference.

Dependencies: OV-SND-01, OV-SND-01N, OV-SEL-01, OV-SEL-02, OV-DQ-03

Notes: Passing requires OV-SND locks remain lock==computed, artifact paths present, and referenced governance locks remain lock==computed.

External anchor: None

External evidence: None



ID: OV-SEL-SND-03

Name: OV-SEL-SND-03 derived sound-speed ingestion audit narrative (bookkeeping)

Category: Observable

Short description: OV-SEL-style locked narrative confirming that adding the derived sound-speed observable OV-SND-02 does not trigger any policy/threshold changes, regime bridge behavior changes, selection consequences, continuity claims, or averaging; includes deterministic lock==computed and negative token checks.

Status: Locked

Evidence: formal/python/toe/observables/ovsel_snd03_sound_speed_derived_audit_record.py; formal/python/tools/ovsel_snd03_sound_speed_derived_audit_record.py; formal/python/tests/test_ov_sel_snd03_sound_speed_derived_audit_lock.py; formal/markdown/locks/observables/OV-SEL-SND-03_sound_speed_derived_audit.md

Scope / limits: Bookkeeping/narrative only; no physics claim. Derived anchor ingestion; no fitting beyond pinned slope rule; no regime averaging; no continuity claim.

Dependencies: OV-SND-02, OV-SEL-01, OV-SEL-02, OV-DQ-03

Notes: Passing requires OV-SND locks remain lock==computed and governance locks remain lock==computed.

External anchor: None

External evidence: None



ID: OV-SEL-SND-04

Name: OV-SEL-SND-04 density dependence audit narrative (bookkeeping)

Category: Observable

Short description: OV-SEL-style locked narrative confirming that adding SND-DIG-01, OV-SND-03N (density digitization), and OV-SND-03 (density-scaled derived quantities) does not trigger any policy/threshold changes, regime bridge behavior changes, selection consequences, continuity claims, or averaging; includes deterministic lock==computed, artifact existence, and negative token checks.

Status: Locked

Evidence: formal/python/toe/observables/ovsel_snd04_density_dependence_audit_record.py; formal/python/tools/ovsel_snd04_density_dependence_audit_record.py; formal/python/tests/test_ov_sel_snd04_density_dependence_audit_lock.py; formal/markdown/locks/observables/OV-SEL-SND-04_density_dependence_audit.md

Scope / limits: Bookkeeping/narrative only; no physics claim. Density digitization and derived scaling are non-decisive by design; no selection/regime effects.

Dependencies: SND-DIG-01, OV-SND-03N, OV-SND-03, OV-SEL-01, OV-SEL-02, OV-DQ-03

Notes: Passing requires sound-lane locks remain lock==computed, density artifacts exist, and negative token checks pass.

External anchor: None

External evidence: None



ID: OV-SEL-SND-05

Name: OV-SEL-SND-05 multi-density constancy audit narrative (bookkeeping)

Category: Observable

Short description: OV-SEL-style locked narrative confirming that adding OV-SND-03N-COV, OV-BR-SND-02, and OV-SND-04 does not trigger any policy/threshold changes, regime bridge behavior changes, selection consequences, continuity claims, or averaging; includes deterministic lock==computed and negative token checks.

Status: Locked

Evidence: formal/python/toe/observables/ovsel_snd05_multi_density_constancy_audit_record.py; formal/python/tools/ovsel_snd05_multi_density_constancy_audit_record.py; formal/python/tests/test_ov_sel_snd05_multi_density_constancy_audit_lock.py; formal/markdown/locks/observables/OV-SEL-SND-05_multi_density_constancy_audit.md

Scope / limits: Bookkeeping/narrative only; no physics claim. New mapping/constancy records are non-decisive by design; no selection/regime effects.

Dependencies: OV-SND-03N-COV, OV-BR-SND-02, OV-SND-04, OV-SEL-01, OV-SEL-02, OV-DQ-03

Notes: Passing requires lock==computed for new records and negative token checks for selection/governance locks.

External anchor: None

External evidence: None



ID: OV-BR-SND-01

Name: OV-BR-SND-01 sound vs low-k Bragg comparability record (scope-fenced)

Category: Observable

Short description: Explicit bookkeeping record declaring the conditions under which a sound-propagation speed anchor (OV-SND-02) could be comparable to the low-k Bragg anchor (OV-04x / DS-02), and the current blockers preventing a quantitative comparison; forbids continuity/averaging.

Status: Locked

Evidence: formal/python/toe/observables/ovbr_snd01_sound_vs_bragg_lowk_comparability_record.py; formal/python/tools/ovbr_snd01_sound_vs_bragg_lowk_comparability_record.py; formal/python/tests/test_ov_br_snd01_sound_vs_bragg_lowk_comparability_lock.py; formal/markdown/locks/observables/OV-BR-SND-01_sound_vs_bragg_lowk_comparability.md

Scope / limits: Bookkeeping only; no physics claim. No continuity claim; no cross-regime averaging; non-decisive by design.

Dependencies: OV-SND-02, OV-04x

Notes: Conservative by design: does not compute cross-anchor agreement; it records comparability criteria and why the comparison is not performed under current artifacts.

Scientific status note (2026-01-29)
- OV-BR-SND-01 comparability.status is not_compared_quantitatively and gate_ok is False under current blockers.
- This is the intended “no pairing, no claim” boundary for cross-anchor comparison: numerical deltas can be computed in numeric_only mode, but justified_only comparisons remain suppressed until comparability + mapping evidence is produced.

External anchor: None

External evidence: None



ID: OV-SEL-SND-02

Name: OV-SEL-SND-02 sound anchor interaction stress test narrative (bookkeeping)

Category: Observable

Short description: Interaction stress test asserting absence of forbidden benchmark/anchor interactions: no selection/regime locks reference OV-SND or OV-BM tokens; governance locks remain lock==computed.

Status: Locked

Evidence: formal/python/toe/observables/ovsel_snd02_sound_anchor_interaction_stress_test_record.py; formal/python/tools/ovsel_snd02_sound_anchor_interaction_stress_test_record.py; formal/python/tests/test_ov_sel_snd02_sound_anchor_interaction_stress_test_lock.py; formal/markdown/locks/observables/OV-SEL-SND-02_sound_anchor_interaction_stress_test.md

Scope / limits: Bookkeeping/narrative only; no physics claim. Negative checks only; no fitting; no continuity claim.

Dependencies: OV-SND-01, OV-SND-01N, OV-SEL-01, OV-SEL-02, OV-XD-03, OV-XD-04, OV-BR-02, OV-DQ-03, OV-BM-01, OV-BM-01N, OV-BM-02, OV-BM-02N

Notes: Passing requires all lock==computed checks and token-negative checks.

External anchor: None

External evidence: None



ID: OV-SEL-BM-01

Name: OV-SEL-BM-01 benchmark ingestion stress test narrative (symbolic-only; bookkeeping)

Category: Observable

Short description: OV-SEL-style locked narrative confirming that introducing symbolic-only benchmark observables (OV-BM-01, OV-BM-02) does not trigger regime averaging, model selection, preference flips, or policy/threshold changes; includes deterministic lock==computed self-checks for canonical and DQ-01_v2-parallel downstream bookkeeping locks.

Status: Locked

Evidence: formal/python/toe/observables/ovselbm01_benchmark_ingestion_stress_test_record.py; formal/python/tools/ovselbm01_benchmark_ingestion_stress_test_record.py; formal/python/tests/test_ov_sel_bm01_benchmark_ingestion_stress_test_lock.py; formal/markdown/locks/observables/OV-SEL-BM-01_benchmark_ingestion_stress_test.md

Scope / limits: Bookkeeping/narrative only; no physics claim. Symbolic-only benchmarks; no digitization; no fitting. No regime averaging; no continuity claim; no cross-observable inference.

Dependencies: OV-BM-01, OV-BM-02, OV-SEL-01, OV-SEL-02, OV-XD-04, OV-BR-02, OV-DQ-02

Notes: Passing requires all self-checks to report lock==computed and benchmark-only scope fences to remain explicit.

External anchor: None

External evidence: None



ID: OV-SEL-BM-02

Name: OV-SEL-BM-02 numeric benchmark ingestion audit narrative (benchmark-only; bookkeeping)

Category: Observable

Short description: OV-SEL-style locked narrative confirming that adding the minimal numeric benchmark artifact OV-BM-01N does not trigger any policy/threshold changes, regime bridge behavior changes, selection consequences, continuity claims, or averaging; includes deterministic lock==computed and artifact existence self-checks.

Status: Locked

Evidence: formal/python/toe/observables/ovselbm02_numeric_benchmark_ingestion_record.py; formal/python/tools/ovselbm02_numeric_benchmark_ingestion_record.py; formal/python/tests/test_ov_sel_bm02_numeric_benchmark_ingestion_lock.py; formal/markdown/locks/observables/OV-SEL-BM-02_numeric_benchmark_ingestion_audit.md

Scope / limits: Bookkeeping/narrative only; no physics claim. Benchmark-only numeric ingestion; no fitting; no regime averaging; no continuity claim; no cross-observable inference.

Dependencies: OV-BM-01N, OV-SEL-01, OV-SEL-02, OV-XD-04, OV-BR-02, OV-DQ-02

Notes: Passing requires OV-BM-01N lock==computed, artifact paths present, and all referenced governance locks to remain lock==computed.

External anchor: None

External evidence: None



ID: BM-DIG-01

Name: BM-DIG-01 minimal numeric benchmark digitization acceptance criteria (computed)

Category: Policy

Short description: Specifies the smallest acceptable numeric digitization target and acceptance criteria for converting exactly one benchmark (OV-BM-01 or OV-BM-02) into a frozen, typed numeric artifact while preserving benchmark-only scope fences (no fitting, no regime blending, no selection/validation claims).

Status: Locked

Evidence: formal/python/toe/observables/bmdig01_minimal_numeric_benchmark_digitization_record.py; formal/python/tools/bmdig01_minimal_numeric_benchmark_digitization_record.py; formal/python/tests/test_bmdig01_minimal_numeric_benchmark_digitization_lock.py; formal/markdown/locks/policies/BM-DIG-01_minimal_numeric_benchmark_digitization.md

Scope / limits: Bookkeeping/workflow governance only; no digitization performed here. Benchmark-only: no fitting, no averaging across regimes, no continuity claim, no cross-observable inference.

Dependencies: OV-BM-01, OV-BM-02

Notes: Intended as a “smallest possible” safe next step before any benchmark digitization is attempted; requires explicit provenance and a follow-on OV-SEL-BM-style narrative lock confirming no policy/threshold changes were triggered.

External anchor: None

External evidence: None



ID: SND-DIG-01

Name: SND-DIG-01 minimal density digitization acceptance criteria (computed)

Category: Policy

Short description: Specifies the smallest acceptable density digitization target and acceptance criteria for introducing a frozen density anchor into the sound lane while preserving strict scope fences (no fitting, no regime blending, no continuity claims, no selection/validation claims).

Status: Locked

Evidence: formal/python/toe/observables/snddig01_minimal_density_digitization_record.py; formal/python/tools/snddig01_minimal_density_digitization_record.py; formal/python/tests/test_snddig01_minimal_density_digitization_lock.py; formal/markdown/locks/policies/SND-DIG-01_minimal_density_digitization.md

Scope / limits: Bookkeeping/workflow governance only; no digitization performed here. Sound-lane density anchors only: no fitting, no averaging across regimes, no continuity claim, no cross-observable inference.

Dependencies: OV-SND-01

Notes: Intended as the “smallest possible” safe next step before any multi-condition density inference is attempted; requires explicit provenance and a follow-on OV-SEL-SND-style narrative lock confirming no policy/threshold changes were triggered.

External anchor: None

External evidence: None



ID: EA-04a

Name: EA-04 evaluation note — OV-04x (DS-02 low-k dataset)

Category: Evidence block

Short description: Evidence-only application record for OV-04x under EA-04. Required before promoting OV-04x to Empirically Anchored.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/policy/EA-04a_evaluation_OV-04x.md

Scope / limits: Evidence-only application record; does not introduce new data or modeling.

Dependencies: DS-02-EVIDENCE-DIGITIZATION, DR-β-03

Notes: Keep this record robustness-only and β-null (β not inferred / compatible with 0). EA-04a must not depend on OV-04x or EA-04.

External anchor: None

External evidence: None




ID: OV-BR-01

Name: OV-BR-01 Regime Bridge Declaration + Record

Category: Observable

Short description: Pure bookkeeping bridge observable that declares two k-bands (low-k from OV-01g; high-k from OV-03x), records regime-separated preferences, and computes only the overlap/gap geometry between those bands. This record is split into sub-bands and evaluated separately, with no averaging across regimes.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ovbr01_regime_bridge_record.py; formal/python/tests/test_ov_br01_regime_bridge_record.py; formal/markdown/locks/observables/OV-BR-01_regime_bridge_record.md

Scope / limits: split into sub-bands; evaluated separately; no averaging across regimes; no continuity claim. This record explicitly maintains a β-null posture (β not inferred) and must not be used for β inference.

Dependencies: OV-01g, OV-03x, OV-XD-03

Notes: OV-BR-01 is a controlled “continuity bridge” without asserting continuity. It records separately measured preferences plus band geometry only.

External anchor: None

External evidence: None




ID: OV-XD-01

Name: OV-XD-01 cross-dataset robustness agreement (OV-01g, OV-02x, OV-03x)

Category: Observable

Short description: Bookkeeping observable that records whether robustness-only curved-vs-linear fit-family preference outcomes agree or disagree across OV-01g (Steinhauer), OV-02x (digitization invariance on Steinhauer), and OV-03x (Ernst 2009).

Status: Locked

Evidence: formal/markdown/locks/observables/OV-XD-01_cross_dataset_robustness_agreement.md

Scope / limits: Summary-only robustness record. Does not add new data, does not introduce new modeling, and must not be used for β inference.

Dependencies: OV-01g, OV-02x, OV-03x, DR-β-01, DR-β-02

Notes: This is intended as a single, auditable "what have we actually established?" record: agreement or disagreement of robustness-only outcomes under declared gates, while remaining compatible with β=0.

External anchor: None

External evidence: None



ID: OV-XD-03

Name: OV-XD-03 cross-dataset overlap band record (computed)

Category: Observable

Short description: Computed record of per-dataset k-coverage bands (k_min/k_max) and their overlap band across the datasets used by OV-XD bookkeeping.

Status: Locked

Evidence: formal/python/toe/observables/ovxd03_overlap_band_record.py; formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md

Scope / limits: Bookkeeping overlap record only. Overlap band = intersection of per-dataset k-coverage bands (k_min = max of mins, k_max = min of maxes); no physics claim.

Dependencies: OV-01g, OV-02x, OV-03x

Notes: OV-XD-03 is used to prevent silent misuse of cross-dataset agreement claims outside the k-overlap band.

External anchor: None

External evidence: None



ID: OV-XD-02

Name: OV-XD-02 cross-dataset preference agreement record (deterministic)

Category: Observable

Short description: Deterministic record (with a locked JSON summary + regression test) of whether robustness-only fit-family preference outcomes match across datasets, separate from OV-XD-01 prose.

Status: Locked

Evidence: formal/python/toe/observables/ovxd02_preference_agreement_record.py; formal/python/tests/test_ov_xd02_preference_agreement_record.py; formal/markdown/locks/observables/OV-XD-02_cross_dataset_preference_agreement_record.md

Scope / limits: Summary-only bookkeeping record. Does not add new data, does not introduce new modeling, and must not be used for β inference.

Dependencies: OV-XD-01, OV-XD-03, OV-01g, OV-02x, OV-03x, DR-β-01, DR-β-02

Notes: Records agreement or disagreement as-is (disagreement is admissible). This is not a physics claim and must not be used to assert a physical mechanism.

External anchor: None

External evidence: None





ID: OV-BR-02

Name: OV-BR-02 Regime Bridge Declaration + Record (OV-04x ↔ OV-03x)

Category: Observable

Short description: Pure bookkeeping bridge observable that declares two k-bands (low-k from OV-04x; high-k from OV-03x), records regime-separated preferences (including deterministic failure reasons), and uses OV-XD-03 as the authoritative overlap-band record. No averaging across regimes.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ovbr02_regime_bridge_record.py; formal/python/tests/test_ov_br02_regime_bridge_record.py; formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md

Scope / limits: split into sub-bands; evaluated separately; overlap-only comparability; no averaging across regimes; no continuity claim. β not inferred / β-null posture; must not be used for β inference.

Dependencies: OV-04x, OV-03x, OV-XD-03, DR-β-02, DR-β-03

Notes: This record avoids overloading OV-BR-01 by explicitly anchoring the low band to the DS-02 slot (OV-04x). Comparability is meaningful only within the OV-XD-03 overlap band; no claim is made outside that intersection.

External anchor: None

External evidence: None





ID: OV-XD-04

Name: OV-XD-04 overlap-only preferred-fit-family comparison (OV-04x vs OV-03x)

Category: Observable

Short description: Overlap-only bookkeeping record of whether the robustness-only preferred fit-family outcomes agree between OV-04x (DS-02 low-k) and OV-03x (B1), restricted to the OV-XD-03 overlap band.

Status: Locked

Evidence: formal/python/toe/observables/ovxd04_overlap_only_preference_comparison_record.py; formal/python/tests/test_ov_xd04_overlap_only_preference_comparison_record.py; formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md

Scope / limits: Overlap-only bookkeeping record; no continuity claim; no averaging across regimes; robustness-only; must not be used for β inference (β-null posture).

Dependencies: OV-XD-03, OV-04x, OV-03x, DR-β-02, DR-β-03

Notes: Agreement is operational and may be “agreement in being undecided.” The comparison is permitted only within the overlap band (intersection of k-coverage bands); no claim is made outside that intersection.

External anchor: None

External evidence: None





ID: FN-01c

Name: FN-01 CAUS-01 core tightening consumer

Category: Constraint / Criterion (Lean module)

Short description: Thin FN-layer consumer that imports only the CAUS-01 core surface and re-exports the stable admissibility lemma API.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreConsumer.lean

Scope / limits: Imports only CAUS-01 core surface; no CAUS gate-suite claims; no coupling to FN01\_DeformationClass.

Dependencies: FN-01, CAUS-01

Notes: Validates that CAUS-01 tightening is reusable across criteria layers (AD and FN) with minimal churn.

External anchor: None

External evidence: None





ID: FN-01d

Name: FN-01 CAUS-01 core bridge lemma module

Category: Constraint / Criterion (Lean module)

Short description: Bridge module importing FN-01 deformation-class definitions alongside the CAUS-01 core surface and re-exporting the core admissibility lemmas.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreBridge.lean

Scope / limits: Imports CAUS-01 core surface (not CAUS gate-suite); provides structural re-exports only.

Dependencies: FN-01, CAUS-01

Notes: Confirms FN-layer code can reference the CAUS-01 tightening surface without coupling to the CAUS gate suite.

External anchor: None

External evidence: None





ID: FN-01e

Name: FN-01 candidate outcome table (CT-01 / CAUS C1 / SYM gates)

Category: Evidence block

Short description: Deterministic table-driven test mapping representative deformation terms P[ψ] to pass/fail outcomes for CT-01, CAUS C1 (P(0)=0), and SYM-01 (phase/translation/rotation).

Status: Behavioral (Python)

Evidence: formal/python/tests/test_fn01_candidate_table.py

Scope / limits: Probe-level and grid-based numerical checks only; intended as internal pruning bookkeeping, not a physical claim.

Dependencies: FN-01, CT-01, CAUS-01, SYM-01

Notes: Front-door policy: any new FN candidate term must be added to the table with expected outcomes for CT-01, CAUS C1, SYM phase, SYM translation, and SYM rotation (prevents silent candidate sprawl).

External anchor: None

External evidence: None





ID: FN-01f

Name: FN-01 candidate membership entry points + per-candidate DR corollaries

Category: Constraint / Criterion (Lean module)

Short description: Lean-side “front door” entry-point lemmas per candidate (admit via FN01_DeformationClass or explicitly reject), plus one-liner corollaries exporting DR-01 preservation on plane waves per candidate via the existing FN→DR bridge.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateMembership.lean

Scope / limits: Structural-only; most candidates are admitted conditionally (requires the gate predicates as hypotheses) because the linearization extractor is abstract. Includes explicit rejections where a gate is violated definitionally.

Dependencies: FN-01, CT-01, SYM-01, DR-01

Notes: Intended policy: any theorem about a specific FN candidate should import this module and route through the named membership lemma (or a named rejection lemma) before consuming FN→DR consequences.

External anchor: None

External evidence: None





ID: FN-01g

Name: FN-01 near-plane-wave (wavepacket) ω(k) regression check

Category: Evidence block

Short description: Behavioral regression test estimating ω(k) from time evolution of a small Gaussian-enveloped wavepacket, comparing baseline vs perturbations to provide one notch of DR-01 tightening beyond exact plane waves.

Status: Behavioral (Python)

Evidence: formal/python/tests/test_fn01_near_plane_wave_regression.py

Scope / limits: Small-grid, short-time, deterministic numerical check only; not a PDE validation suite and not a physical claim.

Dependencies: FN-01, CT-01, DR-01

Notes: Intended as the next tightening step after the plane-wave-only structural bridge; keeps the CAUS gate-suite untouched.

External anchor: None

External evidence: None





ID: FN-01h

Name: FN-01 Lean candidate API front-door + enforcement test

Category: Evidence block

Short description: Adds a single Lean import surface for FN-01 named candidates and mechanically enforces (via pytest scan) that downstream Lean files cannot reference candidate tokens without importing the FN-01 Candidate API module.

Status: Behavioral (Python)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateAPI.lean; formal/python/tests/test\_fn01\_candidate\_api\_enforced.py

Scope / limits: Guardrail policy only; does not add new mathematical content.

Dependencies: FN-01, FN-01f

Notes: Lean-side equivalent of the Python candidate-table front door; prevents casual bypass of the membership API by direct candidate usage.

External anchor: None

External evidence: None



ID: FN-01i

Name: FN-01 plane-wave mode-closure diagnostic table

Category: Evidence block

Short description: Evidence-only diagnostic evaluating each registered FN-01 candidate representative P[ψ] on a single Fourier-mode plane wave and reporting whether the output remains mode-closed (P(ψ) proportional to ψ) along with the induced coefficient alpha. Intended as discriminative bookkeeping for candidates that definitionally break plane-wave closure.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/functionals/FN-01_plane_wave_mode_closure_diagnostic.md; formal/python/tests/test_fn01_candidate_table.py

Scope / limits: Single-mode diagnostic only (one k, one amplitude, one grid); not a PDE suite and not a physical claim.

Dependencies: FN-01, DR-01

Notes: Separates “mode-closed on plane waves” from the FN gate outcomes; candidates that leak modes are not eligible for a literal plane-wave dispersion reading.

External anchor: None

External evidence: None



ID: FN-01j

Name: FN-01 candidate pruning outcome table (mode-closure gate)

Category: Evidence block

Short description: Evidence-only pruning table derived from the FN-01 plane-wave mode-closure diagnostic, recording which registered candidates are mode-closed vs mode-leaking on the tested plane wave and identifying the leading survivor under the combined FN gate outcomes.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/functionals/FN-01_candidate_pruning_outcomes_DR02_DR03.md; formal/markdown/locks/functionals/FN-01_plane_wave_mode_closure_diagnostic.md; formal/python/tests/test_fn01_candidate_table.py

Scope / limits: Pruning bookkeeping only; does not upgrade status; mode-closure diagnostic is independent of BR-01/MT-01 metrics in the current framework.

Dependencies: FN-01, FN-01e, FN-01i

Notes: This is intended as a decision-log input for candidate elimination; any future promotion of a single FN candidate into a public artifact surface must reference this table.

External anchor: None

External evidence: None



ID: FN-01k

Name: FN-01 promoted survivor as typed artifact (P_cubic)

Category: Evidence block

Short description: Introduces a minimal, provenance-stamped FN-01 artifact type (`FN01Artifact1D`) with a deterministic sha256 fingerprint (canonical JSON encoding) and a canonical constructor for the promoted survivor `P_cubic`. This enables downstream bridges/diagnostics to consume a stable “scientific object” rather than importing candidate code or raw arrays.

Status: Behavioral (Python)

Evidence: formal/python/toe/constraints/fn01_artifact.py; formal/python/tests/test_fn01_artifact_provenance.py; formal/python/tests/test_fn01_front_door_enforced.py; formal/python/toe/constraints/fn01_candidates.py

Scope / limits: Artifact plumbing + determinism/provenance guardrail only; does not claim the candidate is physically correct.

Dependencies: FN-01, FN-01j

Notes: Policy mirror of BR-01: internal candidate implementations are quarantined and import-banned; consumers should depend on the artifact surface and named constructors.

External anchor: None

External evidence: None



ID: FN-01l

Name: FN-01 cross-fit metric discriminator (DR-02a vs DR-03a)

Category: Evidence block

Short description: Introduces a single scalar, metric-coupled discriminator that depends on BR-01/MT-01 outputs and therefore changes under DR fit choice. Computes a normalized cross-fit residual on the BR-01-derived metric component g_tt for DR-02a vs DR-03a, and threads the promoted FN artifact fingerprint for lineage.

Status: Behavioral (Python)

Evidence: formal/python/toe/constraints/fn01_metric_discriminator.py; formal/python/tests/test_fn01_cross_fit_metric_residual.py; formal/markdown/locks/functionals/FN-01_cross_fit_metric_residual_DR02_DR03.md

Scope / limits: Minimal discriminator only; currently uses the BR-01 unit-density gauge and u = 0 fits, so g_tt tracks c_s^2 drift under the bridge; does not yet use an FN-dependent weighting beyond fingerprint propagation.

Dependencies: FN-01k, BR-01d, DR-02a, DR-03a, BR-01c

Notes: This is the first explicitly metric-sensitive pruning signal in the FN loop; any future higher-value FN discriminators should reduce to or extend this residual rather than replacing it ad hoc.

External anchor: None

External evidence: None





4.4 METRICS AND GEOMETRY





ID: MT-01

Name: Acoustic metric

Category: Metric

Short description: Effective wave metric

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CRFT/Geom/AcousticMetric.lean

Scope / limits: Linear wave regime

Dependencies: DR-01

Notes: Structural object exists; usage is optional as an interpretive lens within current scope.

External anchor: None

External evidence: None





ID: MT-01a

Name: MT-01 Python front door + lock regression

Category: Evidence block

Short description: Adds a canonical Python implementation of the MT-01 acoustic-metric formulas and a deterministic regression test (including cross-check vs the archived reference implementation).

Status: Behavioral (Python)

Evidence: formal/python/crft/acoustic_metric.py; formal/python/tests/test_mt01_acoustic_metric_lock.py

Scope / limits: Tests only the locked algebraic identities pointwise; does not claim physical completeness.

Dependencies: MT-01

Notes: Python-side “front door” mirror of the Lean lock; intended to keep the locked formulas stable and executable.

Operational validation ledger (bounded evidence only; no status upgrade): formal/quarantine/validation/CRFT_validation_queue_extended_crft_test_family_v1.json (claim_family=C7_MT_01A, evidence_strength=bounded_multi). Protocol: formal/docs/crft_validation_queue_protocol.md.

For CRFT-wide validation status (C6/C7/C8), see the CRFT ledger roll-up under EQ-01.

External anchor: None

External evidence: None





ID: MT-01b

Name: MT-01 Lean consumer lemma (1D determinant reduction)

Category: Evidence block

Short description: Adds a thin Lean consumer module proving the 1D determinant reduction lemma for computed acoustic metrics, mirroring the existing 2D reduction lemma.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CRFT/Geom/MT01\_AcousticMetricConsumer.lean

Scope / limits: Purely structural lemma over the locked definitions.

Dependencies: MT-01

Notes: Establishes the “consumer” half of the MT-01 lock pattern, keeping the base definition file focused on formulas.

External anchor: None

External evidence: None





4.5 BRIDGES AND REDUCTIONS





ID: BR-01

Name: Dispersion to metric mapping

Category: Bridge

Short description: Maps dispersion relation to effective metric

Status: Spec-backed

Evidence: formal/markdown/locks/geometry/forced\_vs\_optional\_geometry.md

Scope / limits: Linear regime

Dependencies: DR-01, MT-01

Notes: No physical necessity claim

External anchor: None

External evidence: None





ID: BR-01a

Name: BR-01 Python front door + enforcement + roundtrip locks

Category: Evidence block

Short description: Adds a canonical Python import surface for BR-01 (dispersion → metric mapping), enforces that internal candidate modules are not imported directly, and provides deterministic plane-wave and near-plane-wave roundtrip locks.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit.py; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/python/toe/bridges/br01_candidates.py; formal/python/tests/test_br01_front_door_enforced.py; formal/python/tests/test_br01_candidate_table.py; formal/python/tests/test_br01_plane_wave_roundtrip.py; formal/python/tests/test_br01_near_plane_wave_roundtrip.py

Scope / limits: Uses a minimal 1D DR-01 data-backed fit artifact (u, c_s, provenance, data_fingerprint) and a deterministic wavepacket phase estimator; this is a bridge lock and policy guardrail, not a physical derivation.

Dependencies: BR-01, DR-01, MT-01

Notes: Establishes the Python-side “front door” and makes BR-01 hard to bypass in downstream code.



ID: BR-01c

Name: BR-01 upgraded to DR-01 fit artifact input (no surrogate fallback)

Category: Evidence block

Short description: Upgrades BR-01 to consume a canonical DR-01 data-backed fit artifact type (front door), implements fit-backed candidates privately, and tightens the roundtrip locks to assert the fit fingerprint and data fingerprint are actually used (preventing accidental fallback to ad-hoc surrogates).

Status: Behavioral (Python) + Structural (Lean)

Evidence: formal/python/toe/dr01_fit.py; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/python/toe/bridges/br01_candidates.py; formal/python/tests/test_br01_candidate_table.py; formal/python/tests/test_br01_plane_wave_roundtrip.py; formal/python/tests/test_br01_near_plane_wave_roundtrip.py; formal/toe_formal/ToeFormal/Bridges/BR01_DispersionToMetric.lean; formal/toe_formal/ToeFormal/Bridges/Consumers/BR01_UsesMT01.lean

Scope / limits: Still 1D and unit-density gauge; the upgrade is about dependency structure and drift-proof bridge plumbing (fit-typed assumption), not about extending BR-01’s physical scope.

Dependencies: BR-01, DR-01, MT-01

Notes: BR-01 remains hard-to-bypass: candidates are still import-banned; downstream consumers depend only on the front door.

External anchor: None

External evidence: None



ID: BR-01d

Name: BR-01 cross-fit comparison report (DR-02a vs DR-03a)

Category: Evidence block

Short description: Evidence-only report comparing BR-01 output acoustic metrics when driven by two different frozen, data-backed DR fit artifacts (DR-02a vs DR-03a) derived from the Steinhauer Fig. 3a digitization. Records what changes under the fit choice (notably c_s and thus g_tt/c_s2) and what remains invariant under the current unit-density gauge.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/BR-01_cross_fit_comparison_DR02_DR03.md; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json

Scope / limits: Cross-fit bookkeeping only; BR-01 remains 1D and unit-density; does not interpret which fit choice is "better".

Dependencies: BR-01, DR-02a, DR-03a, MT-01

Notes: Both fits satisfy BR-01 internal consistency (roundtrip) by construction; the point is sensitivity of downstream metric coefficients to the chosen DR fit window.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: BR-01e

Name: BR-01 cross-fit comparison report (curved DR; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Evidence-only report comparing BR-01 metric-driving quantities across four curvature-aware DR window fits, using c0 from ω/k = c0 + βk² as the k→0 sound-speed proxy.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/BR-01_cross_fit_comparison_curved_DR02_DR03_DR04_DR05.md; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/python/toe/dr01_fit_curved.py

Scope / limits: Bookkeeping comparison only; does not claim the curved proxy is physically necessary.

Dependencies: BR-01, DR-01b, DR-02a, DR-03a, DR-04a, DR-05a

Notes: Intended to be read alongside OV-01e.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a





ID: BR-01b

Name: BR-01 Lean structural bridge + MT-01 consumer composition

Category: Evidence block

Short description: Adds a minimal Lean BR-01 bridge mapping a DR-01 surrogate record to an MT-01 acoustic metric (unit-density gauge) and proves a downstream consumer lemma by routing through the MT-01 consumer reduction.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Bridges/BR01\_DispersionToMetric.lean; formal/toe\_formal/ToeFormal/Bridges/Consumers/BR01\_UsesMT01.lean

Scope / limits: Structural mapping only; does not claim uniqueness or physical necessity.

Dependencies: BR-01, DR-01, MT-01

Notes: Lean-side “front door” for BR-01 consumers; demonstrates immediate use by composing into MT-01.

External anchor: None

External evidence: None





4.6 OPERATORS AND AUXILIARY CONSTRUCTS





ID: OP-01

Name: UCFF operator

Category: Operator

Short description: Second-order time evolution operator

Status: Locked

Evidence: formal/toe\_formal/ToeFormal/UCFF/SecondOrderTimeDomain.lean; formal/toe\_formal/ToeFormal/UCFF/SecondOrderNumerics.lean; formal/python/tests/test\_ucff\_core\_symbolic.py; formal/python/tests/test\_ucff\_core\_roundtrip.py; OP-01-EVIDENCE-ARCHIVE-LEGACY

Scope / limits: Homogeneous media

Dependencies: EQ-02

Notes: Locked is asserted jointly: Lean formalization (UCFF modules listed in Evidence) plus Python behavioral checks (formal/python/tests/\*). Locked-status evidence is restricted to non-archived tests under formal/python/tests/\* and the listed Lean modules; OP-01-EVIDENCE-ARCHIVE-LEGACY is included for traceability only and is not part of the Locked-status evidence subset.

External anchor: None

External evidence: None





ID: OP-PW-01

Name: PlaneWave operator definitions (2D)

Category: Operator / Definitions (Lean module)

Short description: Defines opaque operator symbols (Dt, Dxx, Dyy, Delta, L), Field2D, and the planeWave template used for EQ-02 reduction proofs.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorDefs.lean

Scope / limits: Purely structural. Operators are uninterpreted at this layer; no analytic derivative content.

Dependencies: None

Notes: Serves as the definition layer for subsequent axiom and reduction modules; must remain minimal to prevent accidental analytic commitments. Underlying Lean/Mathlib libraries provide technical substrate.

External anchor: None

External evidence: None





ID: OP-PW-02

Name: PlaneWave operator action axioms (Dt/Delta)

Category: Operator / Axiom layer (Lean module)

Short description: Quarantines assumed operator action on planeWave via Dt\_planeWave and Delta\_planeWave, enabling structural reduction without Mathlib derivative development.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorAxioms.lean

Scope / limits: Axiom-only. Encodes the intended behavior of Dt and Delta on planeWave; does not justify or derive these actions from analysis.

Dependencies: OP-PW-01

Notes: This module is the explicit “axiom layer.” Any downstream result relying on these axioms must remain labeled as conditional on Dt\_planeWave / Delta\_planeWave.

External anchor: None

External evidence: None





ID: OP-PW-03

Name: PlaneWave operator reduction lock for EQ-02

Category: Operator / Reduction (Lean module)

Short description: Proves EQ-02 on planeWave reduces to coefficient-equality-times-planeWave under explicit operator-action axioms; no cancellation required.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperators.lean

Scope / limits: Linearized EQ-02 only; reduction is probe-relative to planeWave; relies on Dt\_planeWave and Delta\_planeWave axioms; no non-vanishing/cancellation lemma is assumed or proven.

Dependencies: EQ-02, OP-PW-01, OP-PW-02

Notes: Establishes the operator-level inevitability step (Phase A3). Extracting ω = eigC would require an additional non-vanishing/cancellation lemma about planeWave (not included here by design).

External anchor: None

External evidence: None





ID: OP-PW-04

Name: PlaneWave eigenstructure and selection principle A2

Category: Operator / Eigenstructure + probe-visibility (Lean module)

Short description: Proves eigenvalue addition closure for plane-wave eigen operators and the A2 selection principle: if O and O+E are dispersion-compatible, then E vanishes on plane-wave probes (probe-invisible).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/OperatorCore/PlaneWaveEigenstructure.lean

Scope / limits: Plane-wave probe family only; statement is conditional on the project’s definition of DispersionCompatible (which is probe-relative to planeWave); does not claim E=0 globally as an operator, only E.Op(planeWave …)=0.

Dependencies: OP-SIG-01, OP-PW-01, DR-01

Notes: Canonical downstream lemma is dispersionCompatible\_add\_implies\_E\_vanishes\_on\_planeWaves\_fun; use have hE0 := ... hO hOE A kx ky then simp \[hE0] or rw \[hE0].

External anchor: None

External evidence: None





ID: OP-SIG-01

Name: OperatorSignature core (Op2D + DispersionCompatible + PlaneWaveEigen)

Category: Operator / Signature (Lean module)

Short description: Defines Op2D operator signature and core predicates used by operator-core proofs.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/OperatorCore/OperatorSignature.lean

Scope / limits: Purely structural interface; no analytic commitments.

Dependencies: None

Notes: Upstream definition layer for OP-PW-04. Underlying Lean/Mathlib libraries provide technical substrate.

External anchor: None

External evidence: None





ID: PHB-01

Name: Phase B dispersion-preservation formal scaffold

Category: Constraint / Criterion (Lean module)

Short description: Lean formalization layer used by CT-01c wiring (probe-family preservation lemmas and related predicates).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PhaseB/DispersionPreservation.lean

Scope / limits: Structural scaffold only; probe-relative; conditional on OP-PW axiom layer as used downstream.

Dependencies: OP-PW-02, OP-PW-03, EQ-02, DR-01

Notes: Exists to satisfy “IDs only” dependency rule for CT-01c.

External anchor: None

External evidence: None





4.7 CONSTRAINTS





ID: CT-01
Name: DR-01 dispersion-preservation criterion (linearization rule)

Category: Constraint / Criterion

Short description: Classifies perturbations P\[ψ] by whether they introduce a linear term about ψ=0 and thus alter DR-01.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/constraints/dispersion\_preserving\_terms.md; CT-01-EVIDENCE-PHB; CT-01-EVIDENCE-SOLVER-OMEGA

Scope / limits: Linearization about ψ=0 only; CT-01 is defined and evaluated under probe-level semantics (plane-wave coefficient identity). Additional evidence includes solver-level consequence checks that ω̂(k) shifts when CT-01 fails; these do not change CT-01’s semantics.

Dependencies: EQ-02, DR-01, EQ-01

Notes: Expanded tests include a ψ-independent constant source term; it breaks the plane-wave coefficient identity unless the source is zero (evidence that “no linear part at 0” alone does not guarantee probe-level preservation without a separate source-free condition).

External anchor: None

External evidence: None





ID: CT-01a

Name: DR-01 preservation on plane-wave probes (Lean wrapper)

Category: Constraint / Criterion

Short description: Probe-relative preservation: under AdmissibleOnPlaneWave, perturbed EQ-02 on plane waves is equivalent to unperturbed EQ-02 (same reduction target).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PhaseB/DispersionPreservation.lean

Scope / limits: Plane-wave probe family only; linearized EQ-02 only; conditional on Dt\_planeWave and Delta\_planeWave axioms.

Dependencies: CT-01, DR-01, EQ-02, OP-PW-02, OP-PW-03, PHB-01

Notes: Uses lemmas EQ02Holds\_planeWave\_iff and EQ02Pert\_planeWave\_reduces\_to\_same\_coeff\_equality.

External anchor: None

External evidence: None





ID: CT-01b

Name: LinearizationAt0 probe-relative preservation lemma

Category: Constraint / Criterion (Structural bridge)

Short description: Structural bridge lemma relating abstract linearization surrogate to probe-relative preservation on plane waves.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterface.lean; formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterfaceProbe.lean; formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean

Scope / limits: Probe-relative; applies only to the plane-wave family and linearized EQ-02; linearization is axiomatized and not analytically derived.

Dependencies: CT-01a, OP-PW-02, OP-PW-03, EQ-02, DR-01

Notes: None

External anchor: None

External evidence: None





ID: CT-01c

Name: CT-01 abstract scaffold (CT01\_Abstract)

Category: Constraint / Criterion (Structural scaffold)

Short description: Introduces an abstract “no linear part at ψ=0” predicate (not tied to plane waves) and wires a probe-family preservation lemma for plane waves using PhaseB reduction lemmas.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean

Scope / limits: Structural scaffold; abstract predicate is placeholder-only; preservation statement is probe-family only (plane-wave family) and remains conditional on OP-PW axioms and the PhaseB perturbed reduction lemma.

Dependencies: CT-01a, OP-PW-02, OP-PW-03, EQ-02, DR-01, PHB-01

Notes: This is the canonical “abstract hook” for later strengthening: you can later prove NoLinearPartAt0\_Abstract P → NoLinearPartOnPlaneWaves P (if appropriate), and/or replace the probe-family surrogate with a real structural linearization operator once defined.

External anchor: None

External evidence: None





ID: CT-01d

Name: LinearizationAt0 interface (CT01\_LinearizationInterface)

Category: Constraint / Criterion (Lean interface)

Short description: Defines an abstract, non-analytic linearization-at-0 extractor for Field2D perturbations; provides NoLinearPartAt0\_Field2D predicate.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterface.lean

Scope / limits: Structural-only hook; no analytic meaning; does not imply probe-family vanishing without additional assumptions.

Dependencies: OP-PW-01

Notes: Upstream interface used by CT-01c/CT-01f to make “no linear part at 0” meaningful without analysis.

External anchor: None

External evidence: None





ID: CT-01e

Name: Probe-sound linearization interface (CT01\_LinearizationInterfaceProbe)

Category: Constraint / Criterion (Lean interface)

Short description: Packages a LinearizationAt0 extractor with a Probe predicate and a soundness axiom: NoLinearPartAt0 ⇒ perturbation vanishes on the probe family.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterfaceProbe.lean

Scope / limits: Structural-only; soundness is an explicit axiom of the interface; Probe can be specialized (e.g., plane waves).

Dependencies: CT-01d, OP-PW-01

Notes: Provides PlaneWaveProbe and lemma noLinearPartAt0\_implies\_vanishes\_onPlaneWaves for Probe=PlaneWaveProbe.

External anchor: None

External evidence: None





ID: CT-01f

Name: CT-01 abstract criterion ⇒ DR-01 unchanged on plane waves (CT01\_Abstract bridge theorem)

Category: Constraint / Criterion (Lean theorem)

Short description: Uses probe-sound linearization to derive plane-wave admissibility and proves perturbed EQ-02 is equivalent to unperturbed EQ-02 on plane-wave probes (DR-01 unchanged on probes).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean

Scope / limits: Plane-wave probe family only; relies on PhaseB probe-relative preservation lemma; does not upgrade DR-01 to a global statement.

Dependencies: CT-01c, CT-01d, CT-01e, PHB-01, OP-PW-02, OP-PW-03, EQ-02, DR-01

Notes: Theorem name: CT01\_noLinearPartAt0\_preserves\_DR01\_onPlaneWaves. CT-01 abstract bridge theorem exists and is compiled in Lean.



External anchor: None

External evidence: None



ID: CT-01g

Name: CT-01 CP-NLSE instance-layer shim (CT01\_CPNLSE2D\_Instance)

Category: Constraint / Criterion (Lean instance shim)

Short description: Instance-layer re-export of the CT-01 abstract bridge theorem for CP-NLSE downstream imports.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_CPNLSE2D\_Instance.lean

Scope / limits: Import-surface shim only; does not change CT-01 semantics; keeps CT01\_Abstract as the authority layer.

Dependencies: CT-01f

Notes: Provides CT01\_CPNLSE2D\_noLinearPartAt0\_preserves\_DR01\_onPlaneWaves as a stable downstream theorem name.

External anchor: None

External evidence: None





ID: SYM-01

Name: Symmetry Gate Suite (Phase / Translation / Rotation)

Category: Constraint / Criterion

Short description: Symmetry-based admissibility gate for deformation terms P\[ψ]; pruning constraint enforcing baseline symmetries of unperturbed linearized dynamics.

Status: Locked

Evidence: formal/toe\_formal/ToeFormal/Constraints/SYM01\_PhaseInvariant.lean; formal/python/tests/test\_sym01\_symmetry\_gates.py; formal/markdown/locks/constraints/SYM-01\_symmetry\_gates.md

Scope / limits: Organizational / pruning constraint only; probe-relative behavioral checks; passing does not imply physical correctness; failing is sufficient for exclusion. Gates: S1 (global phase invariance: ψ ↦ e^(iθ) ψ), S2 (spatial translation invariance: no explicit position dependence), S3 (spatial rotation invariance: isotropy under planar rotations). Rotation semantics: field rotated, reference grid held fixed.

Dependencies: None

Notes: No conservation-law claims; no Noether machinery imported; all symmetry notions are explicitly semantic and probe-relative; discrete numerical artifacts acknowledged and controlled by test design. Orthogonal to CT-01 (linearization) and FN-01 (admissible deformation class); composable with future constraints.

External anchor: None

External evidence: None





ID: CAUS-01

Name: Structural Causality / Well-Posedness Gate (Locality / Admissibility)

Category: Constraint / Criterion

Short description: Structural admissibility gates for candidate deformation terms and/or operator extensions; enforces causality-motivated structural rules without proving well-posedness.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CAUS01\_CausalityCore.lean; formal/toe\_formal/ToeFormal/Constraints/CAUS01\_CausalityGate.lean; formal/markdown/locks/constraints/CAUS-01\_causality\_admissibility\_gates.md

Scope / limits: Pruning constraint only; passing does not imply well-posedness or physical validity; failing is sufficient for member-level exclusion. Gates: C1 (no ψ-independent forcing: P\[0]=0), C2 (no elliptic-in-time behavior), C3 (locality as structural proxy for causal propagation intent: no nonlocal/integral/global coupling), C4 (time-order sanity: bounded differential order, no mixed time-order escalation under the declared form). All gates are semantic predicates supplied by caller in Lean; C4 is represented as TimeOrderSane(form, P) parameterized by declared EvolForm, and CAUS01\_Admissible instantiates it at the suite's declared form via TimeOrderSaneAt. Lean interface does not attempt PDE classification (hyperbolic/parabolic).

Dependencies: EQ-01, EQ-02

Notes: Makes no conservation-law claims; does not prove well-posedness or establish finite-speed propagation; performs no analytic PDE classification. Intended for conjunctive use with CT-01 and SYM-01.

External anchor: None

External evidence: None



ID: OP-01-EVIDENCE-ARCHIVE-LEGACY

Name: UCFF legacy archive tests (non-canonical)

Category: Evidence block

Short description: Legacy archive-based UCFF tests retained for traceability only; not used for Locked status.

Status: Deprecated

Evidence: archive/tests/test\_ucff\_core\_symbolic.py; archive/tests/test\_ucff\_core\_roundtrip.py

Scope / limits: Legacy only; not canonical evidence for OP-01 status.

Dependencies: None

Notes: Superseded by formal/python/tests/\* UCFF tests.

External anchor: None

External evidence: None





ID: CT-01-EVIDENCE-PHB

Name: Dispersion preservation under probe-level coefficient identity (DR-01)

Category: Evidence block

Short description: Behavioral probe-level regression suite for CT-01 (plane-wave coefficient identity).

Status: Behavioral (Python)

Evidence: formal/python/tests/test\_phaseB\_dispersion\_preservation\_expanded.py

Scope / limits: Probe-level only (plane-wave coefficient identity); linearization about ψ=0; does not validate solver dynamics or physical interpretation.

Dependencies: CT-01, DR-01, EQ-02

Notes: Previously grouped under “PHASE-B EVIDENCE (PYTHON)” and “CT-01 — DR-01 probe-level dispersion preservation (expanded evidence suite)”. Includes pass/fail families (linear vs nonlinear, derivative surrogates with k-edge cases) and constant source term check; last recorded run: 62 passed (expanded) and 69 passed (full suite).

External anchor: None

External evidence: None





ID: CT-01-EVIDENCE-SOLVER-OMEGA

Name: Solver-level ω(k) consequence under CT-01 failure

Category: Evidence block

Short description: Time-evolution frequency-shift checks predicted by probe-level dispersion incompatibility.

Status: Behavioral (Python)

Evidence: formal/python/tests/test\_phaseB\_solver\_omega\_shift.py

Scope / limits: Narrow periodic-box spectral split-step setup; ω̂(k) extraction via mode projection; constant-source detected via k=0/mean growth; diagnostic behavioral consequence only.

Dependencies: CT-01, DR-01, EQ-02

Notes: Tests ω̂(k) shift for linear potential and derivative surrogates, near-unshifted small-amplitude cubic; last recorded run: 7 passed (suite) and 72 passed (full suite).

External anchor: None

External evidence: None



ID: OV-01

Name: FN-dependent observable probe (OV-01)

Category: Observable / Diagnostic

Short description: Defines a minimal, deterministic observable computed from a promoted FN artifact parameterization and the BR-01/MT-01 metric derived from a data-backed DR fit. This is probe-relative and intended as the smallest “FN touches an observable” step.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_observable.py

Scope / limits: Option A (consistency residual) only; observable is a deliberately minimal FN×metric scalar with target 0 and residual |obs|; not a physical claim.

Dependencies: FN-01k, BR-01c, MT-01a, DR-01

Notes: OV-01 exists to force FN parameters into an externally anchored (data-backed) pipeline surface; higher-value observables may replace the algebraic form while preserving the report/fingerprint structure.

External anchor: None

External evidence: None



ID: OV-01a

Name: OV-01 scan and sensitivity locks (DR-02a vs DR-03a)

Category: Evidence block

Short description: Evidence-only scan of the OV-01 observable for multiple FN parameter settings (g values) under two different data-backed DR fit choices (DR-02a vs DR-03a), plus lock tests asserting fingerprint propagation and FN/metric sensitivity.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/observables/OV-01_DR02_DR03_scan.md; formal/python/tests/test_ov01_observable_residual.py

Scope / limits: Uses the current BR-01 unit-density gauge and u = 0 fits; observable is probe-relative and minimal.

Dependencies: OV-01, DR-02a, DR-03a

Notes: This is the first FN-dependent observable residual in the data-backed loop; it is intended as an upgrade point for future anchored targets (Option B) and/or additional DR windows.

External anchor: None

External evidence: None

ID: OV-01b

Name: OV-01 cross-fit stability gate (DR-02a vs DR-03a)

Category: Evidence block

Short description: Defines and locks a cross-fit stability residual comparing the same FN artifact’s OV-01 observable under two different data-backed DR fit choices (DR-02a vs DR-03a). Adds a provisional robustness gate (retain iff residual ≤ tau) and records a small g-grid table to make the decision surface explicit.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_cross_fit_stability.py; formal/python/tests/test_ov01_cross_fit_stability.py; formal/markdown/locks/observables/OV-01_cross_fit_stability_DR02_DR03.md

Scope / limits: Provisional robustness gate only (tau is not claimed “true”); observable is probe-relative and currently uses the BR-01 unit-density gauge and u = 0 fits.

Dependencies: OV-01a

Notes: This converts OV-01 into an explicit discriminator step (“stable under fit-window perturbation?”). Future upgrades may (i) tighten tau based on external anchors, (ii) introduce ranking over candidate families, or (iii) add a third window (DR-04) for a 3-point stability curve.

External anchor: None

External evidence: None





4.8 BUNDLE





ID: PK-01

Name: StructuralPreservationPaper (Lean bundle)

Category: Packaging / Traceability module

Short description: Packaging bundle aggregating Lean modules supporting structural preservation paper traceability.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/Paper/StructuralPreservationPaper.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorDefs.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorAxioms.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperators.lean; formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationAt0.lean

Scope / limits: Packaging only.

Dependencies: DR-01, OP-PW-02, CT-01a

Notes: None

External anchor: None

External evidence: None



ID: AD-01

Name: Canonical operator admissibility predicate (AdmissibleOp)

Category: Constraint / Criterion

Short description: Defines AdmissibleOp as conjunction of dispersion-compatibility, SYM-01 compliance, and CAUS-01 admissibility for Op2D operator candidates.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/AD01\_CausalityCoreConsumer.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_AdmissibleOp.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_Breakage.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_Canonicals.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_Instances.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_TimeOrderTests.lean; formal/toe\_formal/ToeFormal/OperatorCore/Op2DMeta.lean; AD-01-EVIDENCE-PY

Scope / limits: Structural-only; probe-relative where DispersionCompatible is probe-relative; canonicals define a single phase-action and a single CAUS gate suite; CAUS time-order is enforced via explicit declared tag (non-analytic).

Dependencies: OP-SIG-01, OP-PW-04, SYM-01, CAUS-01, DR-01

Notes: AD-01 is the canonical wiring layer for operator candidate admissibility. Breakage theorem links OP-PW-04 to admissibility via dispersion-compatibility closure. Canonical CAUS suite currently fixes EvolForm := firstOrderTime (NLSE-style) for non-circular time-order enforcement. Behavioral (Python) consequence checks are tracked in AD-01-EVIDENCE-PY. No physical claims.

External anchor: None

External evidence: None



ID: AD-01-EVIDENCE-PY

Name: AD-01 Python consequence tests (bookkeeping)

Category: Evidence block

Short description: Behavioral consequence checks confirming AD-01 wiring includes time-order sanity and rejects second-order-time metadata under a first-order canonical suite.

Status: Behavioral (Python)

Evidence: formal/python/tests/test\_ad01\_caus\_time\_order\_gate.py

Scope / limits: Consequence tests only; does not discover constraints; does not assert external epistemic status.

Dependencies: None

Notes: None

External anchor: None

External evidence: None





INTERPRETABILITY (NON-BINDING)

ID: MAP-01

Name: Symbolic→Empirical Dictionary (non-binding)

Category: Interpretive mapping

Short description: Registry of tentative symbol-to-empirical mappings used for human interpretation only.

Status: Spec-backed

Evidence: Viability Roadmap.txt

Scope / limits: Interpretive aid only; must not be used in admissibility gates, FN pruning, or any enforcement artifact. Mappings may be wrong even if upstream structural/behavioral artifacts are stable.

Dependencies: None

Notes: This entry exists to keep interpretation explicitly labeled and quarantined from enforcement logic.

External anchor: None

External evidence: None



EMPIRICAL INTERFACE (PROXY; UNVALIDATED)

ID: EMP-01

Name: Proxy claim (simulation-only) — dark soliton decay-time boundedness

Category: Empirical interface (proxy)

Short description: Proxy falsifier probe (simulation-only) driven by the DR-01→BR-01 artifact chain; emits one scalar residual and a boolean pass/fail under a single threshold.

Status: Hypothesis

Evidence: formal/python/toe/empirical_probes/emp01_proxy_falsifiability.py; formal/python/tests/test_emp01_proxy_falsifiability.py

Scope / limits: Proxy falsifiability pressure only. Synthetic simulation evidence is permitted as Behavioral bookkeeping but does not constitute empirical validation. No empirical validation performed.

Inputs (pinned; read-only):

- DR-01 fit payload embedded in test (zero runtime I/O), provenance reference:
	formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json
	(used as an embedded constant; path is informational only)
	Embedded payload digest (canonical json, sha256): 799b4fcc1d71a3e0a757044468f62d43c2148c619f568ac4cdca68d24914cd3e
	If digest changes, treat as a new EMP-01 instance requiring review.
- Fixed k-grid: (-3.0, -1.0, -0.25, 0.0, 0.25, 1.0, 3.0)
- Threshold: tol = 1.0e-12

Outputs (single falsifier):

- Scalar: max_abs_omega_residual = max_k | ω_DR01(k) - ω_BR01(metric_from_DR01)(k) |
- Boolean: passed := (max_abs_omega_residual <= tol)

Determinism invariant (meta-only):

- The probe is run twice on identical inputs and must return identical scalar + boolean.

Dependencies: DR-01, BR-01

Notes:

- Interpretation rule: fail = falsifier event under this proxy only; pass ≠ support/confirmation.
- Usage rule: EMP-01 results must not be used for status upgrades.
- Governance isolation: must not be imported by regen_canonical_locks.py, any pruning tables, admissibility gates, or selection/audit records that affect candidate survival.

External anchor: None

External evidence: None



DEPRECATED OR FROZEN ITEMS



ID:

Name:

Reason deprecated:

Replacement:

Notes:



(Leave empty unless applicable.)





OPEN GAPS (BOOKKEEPING ONLY)



Record missing layers or validations.

These are not failures.



Example entries:



Item ID: FN-01

Missing layer: Lean

Comment: No variational derivation



Item ID: BR-01

Missing layer: Python

Comment: No numerical stress test





CHANGE LOG



Date: 2026-01-10

Change: Added CT-01-EVIDENCE-SOLVER-OMEGA (solver-level ω(k) consequence tests) and linked it under CT-01 Evidence. Updated constant source discriminator to use Option A (k=0 / mean(ψ) growth detection) instead of ω-shift.

Reason: Establish behavioral time-evolution consequence: ω̂(k) shifts when CT-01 fails, while remaining near ω0 for small-amplitude purely nonlinear perturbations. Constant source C is detected via mean growth (k=0 mode injection) since it doesn't directly shift ω̂ for k≠0 modes.



Date: 2026-01-10

Change: Updated CAUS-01 inventory entry to match current Lean interface (TimeOrderSane(form, P) parameterized by EvolForm; instantiated via TimeOrderSaneAt) and linked evidence module name ToeFormal.Constraints.CAUS01\_CausalityGate.

Reason: Align State\_of\_the\_Theory.md with the current CAUS-01 markdown semantics notes and the compiled Lean interface.



Date: 2026-01-10

Change: Clarified evidence scoping ambiguities by (1) separating EQ-02 Lean definition into a dedicated module path, (2) removing archive/\* paths from Locked evidence, and (3) setting DR-02 evidence-block status to Behavioral (Python) while retaining DR-02 as Empirically Anchored.

Reason: Remove ambiguity about what constitutes “current” Locked evidence, and ensure “Empirically Anchored” is applied to claims (inventory items) rather than internal reconstruction artifacts.



Date: 2026-01-10

Change: Added OP-01-EVIDENCE-ARCHIVE-LEGACY (Deprecated) to preserve legacy UCFF archive test paths while keeping OP-01 Locked evidence restricted to formal/python/tests/\*.

Reason: Remove ambiguity about canonical vs legacy evidence provenance for OP-01.





HARD RULES (NON-NEGOTIABLE)



If it is not listed here, it does not exist.

If status is Spec-backed, it must be labeled everywhere.

Aristotle may not modify this document.

Status downgrades are allowed without justification. Upgrades are not.





NEXT REQUIRED ACTION

State-of-the-Theory dependency DAG enforcement (unknown IDs + cycles), then resume ToE development.





Template status: We will keep editing.
