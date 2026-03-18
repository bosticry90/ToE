# WS_06_DRYRUN_TOKEN_FLIP_FAMILY_MAPPING_v0

## Purpose
Provide the canonical cycle metadata mapping for the selected WS-06 family:
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_*_cycle*_gate.py`

This mapping is the T02 contract input for T03 helper extraction and parametrized coverage.

## Contract Columns
- `cycle`: canonical dryrun cycle id.
- `slug`: filename and artifact slug.
- `test_gate_rel`: canonical test path.
- `artifact_rel`: canonical artifact path.
- `progress_token`: required cycle progress token line.
- `gate_token`: required cycle gate token line.
- `scope_token`: required cycle scope token line.

## Mapping Table
| cycle | slug | test_gate_rel | artifact_rel | progress_token | gate_token | scope_token |
| --- | --- | --- | --- | --- | --- | --- |
| 37 | simulator | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_simulator_cycle37_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE37_v0: TOKEN_FLIP_DRYRUN_SIMULATOR_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_GATE_v0: SIMULATION_ONLY_NO_TOKEN_WRITE` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_SCOPE_v0: READINESS_CHECK_AGAINST_CYCLE27_36_BUNDLES_ONLY` |
| 38 | attestation | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_attestation_cycle38_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE38_v0: TOKEN_FLIP_DRYRUN_ATTESTATION_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_GATE_v0: REQUIRE_SIMULATOR_OUTPUT_AND_NONWRITE_CONFIRMATION` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_SCOPE_v0: CYCLE37_SIMULATOR_AND_CYCLE27_36_INPUTS_REPLAYED` |
| 39 | reconciliation | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE39_v0: TOKEN_FLIP_DRYRUN_RECONCILIATION_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_GATE_v0: REQUIRE_ATTESTATION_MATCH_AND_NO_TOKEN_MUTATION` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_SCOPE_v0: CYCLE38_ATTESTATION_AND_CYCLE37_SIMULATOR_ALIGNMENT` |
| 40 | closure | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_closure_cycle40_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_closure_cycle40_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE40_v0: TOKEN_FLIP_DRYRUN_CLOSURE_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_GATE_v0: REQUIRE_RECONCILIATION_COMPLETE_AND_NONWRITE_FINALIZED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_SCOPE_v0: CYCLE39_RECONCILIATION_PLUS_CYCLE37_38_TRACEABILITY` |
| 41 | archival | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_archival_cycle41_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_archival_cycle41_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE41_v0: TOKEN_FLIP_DRYRUN_ARCHIVAL_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_GATE_v0: REQUIRE_CYCLE40_CLOSURE_AND_IMMUTABLE_ARCHIVE_PIN` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_SCOPE_v0: CYCLE37_40_TRACE_CHAIN_ARCHIVED_NO_TOKEN_WRITE` |
| 42 | handoff | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_handoff_cycle42_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE42_v0: TOKEN_FLIP_DRYRUN_HANDOFF_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_GATE_v0: REQUIRE_ARCHIVAL_IMMUTABILITY_AND_HANDOFF_READINESS` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_SCOPE_v0: CYCLE41_ARCHIVE_CHAIN_AND_CYCLE37_40_TRACE_TRANSFER` |
| 43 | custody | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_custody_cycle43_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_custody_cycle43_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE43_v0: TOKEN_FLIP_DRYRUN_CUSTODY_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_GATE_v0: REQUIRE_HANDOFF_COMPLETENESS_AND_CUSTODY_CHAIN_SEAL` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_SCOPE_v0: CYCLE42_HANDOFF_WITH_CYCLE37_41_AUDIT_LINKAGE` |
| 44 | notarization | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_notarization_cycle44_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_notarization_cycle44_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE44_v0: TOKEN_FLIP_DRYRUN_NOTARIZATION_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_NOTARIZATION_GATE_v0: REQUIRE_CUSTODY_SEAL_AND_NOTARIZED_NONWRITE_ATTESTATION` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_NOTARIZATION_SCOPE_v0: CYCLE43_CUSTODY_WITH_CYCLE37_42_CHAIN_VERIFICATION` |
| 45 | witness | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_witness_cycle45_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_witness_cycle45_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE45_v0: TOKEN_FLIP_DRYRUN_WITNESS_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_WITNESS_GATE_v0: REQUIRE_NOTARIZATION_COMPLETION_AND_WITNESS_NONWRITE_CONFIRMATION` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_WITNESS_SCOPE_v0: CYCLE44_NOTARIZATION_WITH_CYCLE37_43_CHAIN_AUDIT` |
| 46 | ratification | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_ratification_cycle46_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_ratification_cycle46_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE46_v0: TOKEN_FLIP_DRYRUN_RATIFICATION_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RATIFICATION_GATE_v0: REQUIRE_WITNESS_CONFIRMATION_AND_RATIFIED_NONWRITE_STATUS` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RATIFICATION_SCOPE_v0: CYCLE45_WITNESS_WITH_CYCLE37_44_CHAIN_REVIEW` |
| 47 | concurrence | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_concurrence_cycle47_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_concurrence_cycle47_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE47_v0: TOKEN_FLIP_DRYRUN_CONCURRENCE_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONCURRENCE_GATE_v0: REQUIRE_RATIFICATION_COMPLETION_AND_MULTI_WITNESS_CONCURRENCE` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONCURRENCE_SCOPE_v0: CYCLE46_RATIFICATION_WITH_CYCLE37_45_CHAIN_AUDIT` |
| 48 | consensus | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_consensus_cycle48_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_consensus_cycle48_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE48_v0: TOKEN_FLIP_DRYRUN_CONSENSUS_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONSENSUS_GATE_v0: REQUIRE_CONCURRENCE_COMPLETION_AND_MULTI_PARTY_CONSENSUS_NONWRITE` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONSENSUS_SCOPE_v0: CYCLE47_CONCURRENCE_WITH_CYCLE37_46_CHAIN_REVIEW` |
| 49 | unanimity | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_unanimity_cycle49_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE49_v0: TOKEN_FLIP_DRYRUN_UNANIMITY_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_GATE_v0: REQUIRE_CONSENSUS_COMPLETION_AND_UNANIMOUS_NONWRITE_CONFIRMATION` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_SCOPE_v0: CYCLE48_CONSENSUS_WITH_CYCLE37_47_CHAIN_REVIEW` |
| 50 | closure_consensus | `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_gate.py` | `formal/output/qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_v0.json` | `QFT_FULL_DERIVATION_PROGRESS_CYCLE50_v0: TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_LOCK_PINNED` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_GATE_v0: REQUIRE_UNANIMITY_COMPLETION_AND_FINAL_NONWRITE_CLOSURE_CONSENSUS` | `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_SCOPE_v0: CYCLE49_UNANIMITY_WITH_CYCLE37_48_CHAIN_REVIEW` |

## Draft Helper Interface (T02 Contract)
- Helper module path (planned): `formal/python/tests/qft_full_derivation_token_flip_dryrun_helpers.py`
- Planned API:
  - `def load_surface_texts() -> tuple[str, str, str]`
  - `def assert_discharge_tokens(discharge_text: str, progress_token: str, gate_token: str, scope_token: str, artifact_rel: str) -> None`
  - `def assert_state_inventory_roadmap_tokens(state_text: str, inventory_text: str, roadmap_text: str, required_tokens: list[str]) -> None`
  - `def assert_artifact_contract(artifact_rel: str, expected_id: str, cycle: int, expected_status_key: str, expected_status_value: str, source_cycles: list[int] | None = None) -> None`

## Parametrization Contract (T02)
- Parameter source: this mapping table (or JSON equivalent extracted from it).
- One parametrized case per cycle row with keys:
  - `cycle`, `slug`, `test_gate_rel`, `artifact_rel`, `progress_token`, `gate_token`, `scope_token`.
- T03 representative gate target: cycle 37 + one late-chain case (cycle 50).
