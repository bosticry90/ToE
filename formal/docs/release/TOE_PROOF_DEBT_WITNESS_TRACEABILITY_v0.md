# TOE Proof Debt Witness Traceability v0

Document ID:
- `TOE_PROOF_DEBT_WITNESS_TRACEABILITY_v0`

Purpose:
- bind active proof-debt rows to explicit witness/clearance surfaces.
- preserve bounded non-claim posture while improving debt traceability.

Canonical pointers:
- proof-debt packet: `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md`
- Lean registry surface: `formal/toe_formal/ToeFormal/ProofDebtRegistry.lean`
- parity gate: `formal/python/tests/test_proof_debt_witness_traceability_gate.py`

Traceability tokens:
- `TOE_PROOF_DEBT_TRACEABILITY_STATUS_v0: ACTIVE_BOUNDED_NONCLAIM`
- `TOE_PROOF_DEBT_TRACEABILITY_GAPID_CLASS_v0: OPEN_PROOF_DEBT`
- `TOE_PROOF_DEBT_TRACEABILITY_REGISTRY_SURFACE_v0: formal/toe_formal/ToeFormal/ProofDebtRegistry.lean`

Non-claim boundary:
- this surface tracks debt-to-witness mapping only.
- this surface does not assert debt discharge.
