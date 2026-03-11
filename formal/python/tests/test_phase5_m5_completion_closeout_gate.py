from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


CLOSEOUT_GATE_PATH = "formal/python/tests/test_phase5_m5_completion_closeout_gate.py"
CLOSEOUT_ARTIFACT_PATH = "formal/output/phase5_m5_completion_closeout_checkpoint_v0.json"
CLOSEOUT_ARTIFACT_ID = "phase5_m5_completion_closeout_checkpoint_v0"
TERMINAL_TARGET = "TARGET-PHASE5-SR-M5-CONTROLLED-v0"


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_PROGRAM_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CLOSEOUT_ARTIFACT_ABS = REPO_ROOT / CLOSEOUT_ARTIFACT_PATH


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-./]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_int_token(text: str, token_name: str) -> int:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*(\d+)", text)
    assert m is not None, f"Missing integer token `{token_name}`."
    return int(m.group(1))


def _extract_cycle(gate_path: str) -> int:
    m = re.search(r"cycle(\d+)", gate_path)
    assert m is not None, f"Unable to parse cycle number from `{gate_path}`."
    return int(m.group(1))


def test_phase5_m5_completion_closeout_gate() -> None:
    program_text = _read(PROGRAM_PATH)
    registry = _read_json(REGISTRY_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    min_cycles = _extract_int_token(program_text, "PHASE5_M5_COMPLETION_MIN_ACTIVE_CYCLES_v0")
    intro_cycle = _extract_int_token(program_text, "PHASE5_M5_COMPLETION_INTRO_CYCLE_v0")
    counting_rule = _extract_token(program_text, "PHASE5_M5_COMPLETION_COUNTING_RULE_v0")
    stability_window_token = _extract_token(program_text, "PHASE5_M5_COMPLETION_STABILITY_WINDOW_v0")
    required_gates_token = _extract_token(program_text, "PHASE5_M5_COMPLETION_REQUIRED_GATES_v0")

    m = re.match(r"(\d+)_CONSECUTIVE_GREEN_v0", stability_window_token)
    assert m is not None, "Invalid PHASE5_M5_COMPLETION_STABILITY_WINDOW_v0 token format."
    stability_window = int(m.group(1))

    assert counting_rule == "ACTIVE_SR_M5_CYCLE_NUMBER_MINUS_INTRO_CYCLE_PLUS_ONE"
    assert required_gates_token == "SR_M5_THEORY_PARITY_AND_PHASE5_CONTRACT_AND_ARCHIVE_DISCIPLINE"

    active_gate_path = registry.get("sr_m5_theory_parity_gate_path")
    assert isinstance(active_gate_path, str) and active_gate_path
    active_cycle = _extract_cycle(active_gate_path)

    observed_cycles = active_cycle - intro_cycle + 1
    assert observed_cycles >= min_cycles, "Phase-5 minimum active cycle threshold not satisfied."

    expected_window_cycles = list(range(active_cycle - stability_window + 1, active_cycle + 1))
    assert expected_window_cycles[0] >= intro_cycle

    required_gate_paths = [
        active_gate_path,
        registry.get("sr_m5_phase5_advancement_contract_gate_path"),
        registry.get("sr_m5_archive_discipline_gate_path"),
    ]
    assert all(isinstance(p, str) and p for p in required_gate_paths)
    for rel in required_gate_paths:
        assert (REPO_ROOT / rel).exists(), f"Missing required gate file {rel}."

    for cycle in expected_window_cycles:
        assert (REPO_ROOT / f"formal/output/sr_m5_theory_parity_link_cycle{cycle}_v0.json").exists(), (
            f"Missing SR M5 artifact for cycle{cycle}."
        )
        assert (REPO_ROOT / f"formal/python/tests/test_sr_m5_theory_parity_link_cycle{cycle}_gate.py").exists(), (
            f"Missing SR M5 gate for cycle{cycle}."
        )

    assert CLOSEOUT_ARTIFACT_ABS.exists(), "Missing phase-5 closeout checkpoint artifact."
    closeout_json = _read_json(CLOSEOUT_ARTIFACT_ABS)
    closeout_sha = hashlib.sha256(CLOSEOUT_ARTIFACT_ABS.read_bytes()).hexdigest()
    payload = closeout_json.get("payload", {})

    assert closeout_json.get("artifact_id") == CLOSEOUT_ARTIFACT_ID
    assert payload.get("status") == "COMPLETE_BOUNDED_v0"
    assert payload.get("signature_attestation") == "NONCRYPTO_CHECKPOINT_SIGNATURE_v0"
    assert payload.get("current_active_cycle") == active_cycle
    assert payload.get("intro_cycle") == intro_cycle
    assert payload.get("counting_rule") == counting_rule
    assert payload.get("active_cycles_observed") == observed_cycles
    assert payload.get("minimum_active_cycles_required") == min_cycles
    assert payload.get("stability_window_required") == stability_window
    assert payload.get("window_cycles_verified") == expected_window_cycles
    assert payload.get("required_gates") == required_gate_paths
    assert payload.get("all_required_gates_satisfied") is True
    assert payload.get("all_window_cycles_governance_green") is True
    assert payload.get("terminal_next_target") == TERMINAL_TARGET

    sr_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-SR"), None)
    assert sr_row is not None, "Missing PILLAR-SR row in deep maturity registry."
    assert sr_row.get("next_target") == TERMINAL_TARGET

    status = registry.get("program_status", {})
    assert status.get("PILLAR_DEEP_MATURITY_PROGRAM_STATUS_v0") == "COMPLETE_BOUNDED_v0"
    assert status.get("PILLAR_DEEP_MATURITY_CURRENT_PHASE_v0") == "PHASE_5_M5_COMPLETION_CLOSED_v0"
    assert status.get("PILLAR_DEEP_MATURITY_ACTIVE_TARGET_v0") == TERMINAL_TARGET
    assert status.get("PILLAR_DEEP_MATURITY_NEXT_TARGET_v0") == TERMINAL_TARGET

    assert registry.get("phase5_m5_closeout_gate_path") == CLOSEOUT_GATE_PATH
    assert registry.get("phase5_m5_closeout_artifact_path") == CLOSEOUT_ARTIFACT_PATH

    for text in (program_text, state_text, roadmap_text):
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_PROGRAM_STATUS_v0") == "COMPLETE_BOUNDED_v0"
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_CURRENT_PHASE_v0") == "PHASE_5_M5_COMPLETION_CLOSED_v0"
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_ACTIVE_TARGET_v0") == TERMINAL_TARGET
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_NEXT_TARGET_v0") == TERMINAL_TARGET
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_PHASE5_CLOSEOUT_STATUS_v0") == "COMPLETE_BOUNDED_v0"
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_PHASE5_CLOSEOUT_ARTIFACT_v0") == CLOSEOUT_ARTIFACT_ID
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_PHASE5_CLOSEOUT_SHA256_v0") == closeout_sha
        assert _extract_token(text, "PILLAR_DEEP_MATURITY_PHASE5_CLOSEOUT_GATE_v0") == CLOSEOUT_GATE_PATH
