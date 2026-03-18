from __future__ import annotations

from pathlib import Path

import pytest

from formal.python.tests.qft_full_derivation_token_flip_dryrun_helpers import (
    assert_artifact_contract,
    assert_discharge_tokens,
    assert_state_inventory_roadmap_tokens,
    load_surface_texts,
)


CASES = [
    {
        "cycle": 38,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_attestation_cycle38_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE38_v0: TOKEN_FLIP_DRYRUN_ATTESTATION_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_GATE_v0: REQUIRE_SIMULATOR_OUTPUT_AND_NONWRITE_CONFIRMATION",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_SCOPE_v0: CYCLE37_SIMULATOR_AND_CYCLE27_36_INPUTS_REPLAYED",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0",
        "status_key": "status",
        "status_value": "attested",
        "source_cycles": None,
        "extra_expected_lines": (
            '"source_cycle": 37',
            '"readiness_scope": "cycle37_simulator_and_cycle27_36_inputs_replayed"',
        ),
    },
    {
        "cycle": 39,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE39_v0: TOKEN_FLIP_DRYRUN_RECONCILIATION_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_GATE_v0: REQUIRE_ATTESTATION_MATCH_AND_NO_TOKEN_MUTATION",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_SCOPE_v0: CYCLE38_ATTESTATION_AND_CYCLE37_SIMULATOR_ALIGNMENT",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0",
        "status_key": "status",
        "status_value": "reconciled",
        "source_cycles": [37, 38],
        "extra_expected_lines": (),
    },
    {
        "cycle": 40,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_closure_cycle40_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_closure_cycle40_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE40_v0: TOKEN_FLIP_DRYRUN_CLOSURE_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_GATE_v0: REQUIRE_RECONCILIATION_COMPLETE_AND_NONWRITE_FINALIZED",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_SCOPE_v0: CYCLE39_RECONCILIATION_PLUS_CYCLE37_38_TRACEABILITY",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_closure_cycle40_v0",
        "status_key": "status",
        "status_value": "closure_locked",
        "source_cycles": [37, 38, 39],
        "extra_expected_lines": (),
    },
    {
        "cycle": 41,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_archival_cycle41_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_archival_cycle41_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE41_v0: TOKEN_FLIP_DRYRUN_ARCHIVAL_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_GATE_v0: REQUIRE_CYCLE40_CLOSURE_AND_IMMUTABLE_ARCHIVE_PIN",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_SCOPE_v0: CYCLE37_40_TRACE_CHAIN_ARCHIVED_NO_TOKEN_WRITE",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_archival_cycle41_v0",
        "status_key": "status",
        "status_value": "archived",
        "source_cycles": [37, 38, 39, 40],
        "extra_expected_lines": (),
    },
    {
        "cycle": 42,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_handoff_cycle42_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE42_v0: TOKEN_FLIP_DRYRUN_HANDOFF_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_GATE_v0: REQUIRE_ARCHIVAL_IMMUTABILITY_AND_HANDOFF_READINESS",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_SCOPE_v0: CYCLE41_ARCHIVE_CHAIN_AND_CYCLE37_40_TRACE_TRANSFER",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0",
        "status_key": "status",
        "status_value": "handoff_ready",
        "source_cycles": [37, 38, 39, 40, 41],
        "extra_expected_lines": (),
    },
    {
        "cycle": 43,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_custody_cycle43_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_custody_cycle43_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE43_v0: TOKEN_FLIP_DRYRUN_CUSTODY_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_GATE_v0: REQUIRE_HANDOFF_COMPLETENESS_AND_CUSTODY_CHAIN_SEAL",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_SCOPE_v0: CYCLE42_HANDOFF_WITH_CYCLE37_41_AUDIT_LINKAGE",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_custody_cycle43_v0",
        "status_key": "status",
        "status_value": "custody_sealed",
        "source_cycles": [37, 38, 39, 40, 41, 42],
        "extra_expected_lines": (),
    },
    {
        "cycle": 44,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_notarization_cycle44_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_notarization_cycle44_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE44_v0: TOKEN_FLIP_DRYRUN_NOTARIZATION_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_NOTARIZATION_GATE_v0: REQUIRE_CUSTODY_SEAL_AND_NOTARIZED_NONWRITE_ATTESTATION",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_NOTARIZATION_SCOPE_v0: CYCLE43_CUSTODY_WITH_CYCLE37_42_CHAIN_VERIFICATION",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_notarization_cycle44_v0",
        "status_key": "status",
        "status_value": "notarized",
        "source_cycles": [37, 38, 39, 40, 41, 42, 43],
        "extra_expected_lines": (),
    },
    {
        "cycle": 45,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_witness_cycle45_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_witness_cycle45_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE45_v0: TOKEN_FLIP_DRYRUN_WITNESS_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_WITNESS_GATE_v0: REQUIRE_NOTARIZATION_COMPLETION_AND_WITNESS_NONWRITE_CONFIRMATION",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_WITNESS_SCOPE_v0: CYCLE44_NOTARIZATION_WITH_CYCLE37_43_CHAIN_AUDIT",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_witness_cycle45_v0",
        "status_key": "status",
        "status_value": "witnessed",
        "source_cycles": [37, 38, 39, 40, 41, 42, 43, 44],
        "extra_expected_lines": (),
    },
    {
        "cycle": 46,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_ratification_cycle46_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_ratification_cycle46_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE46_v0: TOKEN_FLIP_DRYRUN_RATIFICATION_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RATIFICATION_GATE_v0: REQUIRE_WITNESS_CONFIRMATION_AND_RATIFIED_NONWRITE_STATUS",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RATIFICATION_SCOPE_v0: CYCLE45_WITNESS_WITH_CYCLE37_44_CHAIN_REVIEW",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_ratification_cycle46_v0",
        "status_key": "status",
        "status_value": "ratified",
        "source_cycles": [37, 38, 39, 40, 41, 42, 43, 44, 45],
        "extra_expected_lines": (),
    },
    {
        "cycle": 47,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_concurrence_cycle47_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_concurrence_cycle47_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE47_v0: TOKEN_FLIP_DRYRUN_CONCURRENCE_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONCURRENCE_GATE_v0: REQUIRE_RATIFICATION_COMPLETION_AND_MULTI_WITNESS_CONCURRENCE",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONCURRENCE_SCOPE_v0: CYCLE46_RATIFICATION_WITH_CYCLE37_45_CHAIN_AUDIT",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_concurrence_cycle47_v0",
        "status_key": "status",
        "status_value": "concurred",
        "source_cycles": [37, 38, 39, 40, 41, 42, 43, 44, 45, 46],
        "extra_expected_lines": (),
    },
    {
        "cycle": 48,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_consensus_cycle48_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_consensus_cycle48_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE48_v0: TOKEN_FLIP_DRYRUN_CONSENSUS_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONSENSUS_GATE_v0: REQUIRE_CONCURRENCE_COMPLETION_AND_MULTI_PARTY_CONSENSUS_NONWRITE",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONSENSUS_SCOPE_v0: CYCLE47_CONCURRENCE_WITH_CYCLE37_46_CHAIN_REVIEW",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_consensus_cycle48_v0",
        "status_key": "status",
        "status_value": "consensed",
        "source_cycles": [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47],
        "extra_expected_lines": (),
    },
    {
        "cycle": 49,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_unanimity_cycle49_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE49_v0: TOKEN_FLIP_DRYRUN_UNANIMITY_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_GATE_v0: REQUIRE_CONSENSUS_COMPLETION_AND_UNANIMOUS_NONWRITE_CONFIRMATION",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_SCOPE_v0: CYCLE48_CONSENSUS_WITH_CYCLE37_47_CHAIN_REVIEW",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0",
        "status_key": "status",
        "status_value": "unanimous",
        "source_cycles": [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48],
        "extra_expected_lines": (),
    },
]


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


@pytest.mark.parametrize(
    "case",
    CASES,
    ids=[
        "cycle38",
        "cycle39",
        "cycle40",
        "cycle41",
        "cycle42",
        "cycle43",
        "cycle44",
        "cycle45",
        "cycle46",
        "cycle47",
        "cycle48",
        "cycle49",
    ],
)
def test_remaining_dryrun_tokens_in_discharge_doc(case: dict[str, object]) -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert_discharge_tokens(
        discharge_text=doc,
        progress_token=case["progress_token"],
        gate_token=case["gate_token"],
        scope_token=case["scope_token"],
        artifact_rel=case["artifact_rel"],
    )


@pytest.mark.parametrize(
    "case",
    CASES,
    ids=[
        "cycle38",
        "cycle39",
        "cycle40",
        "cycle41",
        "cycle42",
        "cycle43",
        "cycle44",
        "cycle45",
        "cycle46",
        "cycle47",
        "cycle48",
        "cycle49",
    ],
)
def test_remaining_dryrun_tokens_in_state_and_roadmap(case: dict[str, object]) -> None:
    state, inventory, roadmap = load_surface_texts()
    required = [
        case["progress_token"],
        case["gate_token"],
        case["scope_token"],
        case["test_gate_rel"],
    ]
    assert_state_inventory_roadmap_tokens(
        state_text=state,
        inventory_text=inventory,
        roadmap_text=roadmap,
        required_tokens=required,
    )


@pytest.mark.parametrize(
    "case",
    CASES,
    ids=[
        "cycle38",
        "cycle39",
        "cycle40",
        "cycle41",
        "cycle42",
        "cycle43",
        "cycle44",
        "cycle45",
        "cycle46",
        "cycle47",
        "cycle48",
        "cycle49",
    ],
)
def test_remaining_dryrun_artifact_json_contract(case: dict[str, object]) -> None:
    assert_artifact_contract(
        artifact_rel=case["artifact_rel"],
        expected_id=case["artifact_id"],
        cycle=case["cycle"],
        expected_status_key=case["status_key"],
        expected_status_value=case["status_value"],
        source_cycles=case["source_cycles"],
        extra_expected_lines=case["extra_expected_lines"],
    )