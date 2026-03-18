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
        "cycle": 37,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_simulator_cycle37_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE37_v0: TOKEN_FLIP_DRYRUN_SIMULATOR_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_GATE_v0: SIMULATION_ONLY_NO_TOKEN_WRITE",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_SCOPE_v0: READINESS_CHECK_AGAINST_CYCLE27_36_BUNDLES_ONLY",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0",
        "status_key": "dryrun_mode",
        "status_value": "simulation_only",
        "source_cycles": None,
        "extra_expected_lines": (
            '"readiness_scope": "cycle27_36_bundles_only"',
        ),
    },
    {
        "cycle": 50,
        "test_gate_rel": "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_gate.py",
        "artifact_rel": "formal/output/qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_v0.json",
        "progress_token": "QFT_FULL_DERIVATION_PROGRESS_CYCLE50_v0: TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_LOCK_PINNED",
        "gate_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_GATE_v0: REQUIRE_UNANIMITY_COMPLETION_AND_FINAL_NONWRITE_CLOSURE_CONSENSUS",
        "scope_token": "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_SCOPE_v0: CYCLE49_UNANIMITY_WITH_CYCLE37_48_CHAIN_REVIEW",
        "artifact_id": "qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_v0",
        "status_key": "status",
        "status_value": "closure_consensed",
        "source_cycles": [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49],
        "extra_expected_lines": (
            '"closure_consensus_result": "unanimity_chain_closure_consensed_nonwrite"',
        ),
    },
]


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


@pytest.mark.parametrize("case", CASES, ids=["cycle37", "cycle50"])
def test_representative_dryrun_tokens_in_discharge_doc(case: dict[str, object]) -> None:
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


@pytest.mark.parametrize("case", CASES, ids=["cycle37", "cycle50"])
def test_representative_dryrun_tokens_in_state_and_roadmap(case: dict[str, object]) -> None:
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


@pytest.mark.parametrize("case", CASES, ids=["cycle37", "cycle50"])
def test_representative_dryrun_artifact_json_contract(case: dict[str, object]) -> None:
    assert_artifact_contract(
        artifact_rel=case["artifact_rel"],
        expected_id=case["artifact_id"],
        cycle=case["cycle"],
        expected_status_key=case["status_key"],
        expected_status_value=case["status_value"],
        source_cycles=case["source_cycles"],
        extra_expected_lines=case["extra_expected_lines"],
    )