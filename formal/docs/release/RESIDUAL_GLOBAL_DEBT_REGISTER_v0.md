# Residual Global Debt Register v0

Document ID: RESIDUAL_GLOBAL_DEBT_REGISTER_v0
Owner: Governance
Status: Active
Last-Updated: 2026-03-07

Purpose:
- Canonically encode residual non-pillar debt that blocks final full-completion attestation.
- Tie blocker rows to explicit discharge artifacts and gates.

Global posture token:
- `RESIDUAL_GLOBAL_DEBT_STATUS_v0: ACTIVE`

Residual blockers:
1. `BLK-01`
- Description: theorem-complete RAC promotion remains blocked pending explicit promotion artifacts.
- Current row label: `B-BLOCKED`
- Required replacement artifacts:
  - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md`
- Discharge token:
  - `BLK01_RAC_PROMOTION_ADJUDICATION_v0: NOT_YET_DISCHARGED`

2. `BLK-02`
- Description: full analytic retirement of default-path action/RAC obligations is not yet discharged.
- Current row label: `B-BLOCKED`
- Required replacement artifacts:
  - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md`
  - `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md`
- Discharge token:
  - `BLK02_ACTION_RAC_RETIREMENT_ADJUDICATION_v0: NOT_YET_DISCHARGED`

Discharge rules:
- `BLK-01` and `BLK-02` may be relabeled from `B-BLOCKED` only when both discharge tokens are set to `DISCHARGED_v0` and replacement artifacts are present across roadmap/state/results references.
- Discharge must not silently remove non-claim boundaries.

Enforcement gate:
- `formal/python/tests/test_phase4_global_unification_and_residual_debt_gate.py`
