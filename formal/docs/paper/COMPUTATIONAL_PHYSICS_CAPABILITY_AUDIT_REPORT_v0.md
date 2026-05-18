# Computational Physics Capability Audit Report v0

Spec ID:
- `COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_REPORT_v0`

Status:
- `ACTIVE_NONLIVE_NONCLAIM`

Classification outcome:
- `COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_CLASSIFIES_EXISTING_NONCLAIM_ANALYSIS_SURFACES_WITHOUT_PROMOTION`

Authority binding:
- `AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`
- Roadmap: `formal/docs/paper/COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md`
- JSON audit: `formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json`
- Gate: `formal/python/tests/test_computational_physics_capability_audit_gate.py`

Non-claim boundary:
- Capability classification only; no theorem discharge, blocker movement, lane reopen, Phase 2 authorization, empirical validation claim, seam closure, master-action promotion, or external-truth claim.

Scope:
- Included rows: `8`
- Excluded: every Python test, every Lean file, full paper inventory, archive paths, quarantine paths.

## Audit Rows

| Artifact | Roles | Claim boundary | Verification | Validation | UQ | Robustness | Known limit | Falsifier | Promotion |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `C6_CP_NLSE_2D_LANE` | simulation, verification, robustness, regime_recovery, falsifier | `internal_consequence` | `gated` | `internal_only` | `none` | `partial` | `partial` | `defined` | `false` |
| `C7_MT01A_ACOUSTIC_METRIC_LANE` | simulation, verification, validation_relevant, robustness, falsifier | `validation_candidate` | `gated` | `internal_only` | `none` | `perturbation_scanned` | `candidate` | `defined` | `false` |
| `UCFF_SPECTRAL_AUDIT_LINEAGE` | verification, uq_relevant, model_comparison, regime_recovery | `internal_consequence` | `gated` | `internal_only` | `qualitative` | `partial` | `candidate` | `defined` | `false` |
| `BRAGG_DISPERSION_ELIMINATIVE_LANE` | validation_relevant, falsifier, model_comparison, uq_relevant | `validation_candidate` | `gated` | `empirical_candidate` | `partial` | `partial` | `candidate` | `defined` | `false` |
| `RL01_RELATIVISTIC_DISPERSION_LIMIT` | verification, validation_relevant, regime_recovery, falsifier, model_comparison | `known_limit_relevant` | `gated` | `known_limit_candidate` | `none` | `partial` | `partial` | `defined` | `false` |
| `RL02_NONRELATIVISTIC_NLSE_LIMIT` | verification, validation_relevant, regime_recovery, falsifier, model_comparison | `known_limit_relevant` | `gated` | `known_limit_candidate` | `none` | `partial` | `partial` | `defined` | `false` |
| `GR01_DERIVATION_COMPLETENESS_GATE` | verification, regime_recovery, governance_only | `blocked` | `gated` | `none` | `none` | `partial` | `blocked` | `blocked` | `false` |
| `BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS` | verification, robustness, falsifier, model_comparison | `internal_consequence` | `gated` | `internal_only` | `qualitative` | `perturbation_scanned` | `none` | `defined` | `false` |

## Summary

- Promotion allowed count: `0`
- Missing evidence count: `0`
- Next recommended packet: `VVUQ_CREDIBILITY_LEDGER_v0_AFTER_RESULT_REVIEW`

Interpretive note:
- This audit says that the selected artifacts perform recognizable computational-physics functions.
- It does not say that those artifacts validate the ToE.
