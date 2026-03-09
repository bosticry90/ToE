from __future__ import annotations

import json
import re
from pathlib import Path


PHASE5_CONTRACT_GATE_PATH = "formal/python/tests/test_sr_m5_phase5_cycle_advancement_contract_gate.py"
CONTRACT_TOKEN_NAME = "SR_M5_PHASE5_ADVANCEMENT_DELTA_TOKEN_v0"
CONTRACT_GATE_TOKEN_NAME = "SR_M5_PHASE5_ADVANCEMENT_CONTRACT_GATE_v0"
INTRO_CYCLE = 40


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_PROGRAM_v0.md"
TARGET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md"
SR_AUTHORITY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-./]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _cycle_number_from_artifact_id(artifact_id: str) -> int:
    m = re.search(r"cycle(\d+)_v0$", artifact_id)
    assert m is not None, f"Artifact id must encode cycle number: {artifact_id}"
    return int(m.group(1))


def test_sr_m5_phase5_cycle_advancement_contract_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    program_text = _read(PROGRAM_PATH)
    target_text = _read(TARGET_DOC_PATH)
    sr_text = _read(SR_AUTHORITY_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    assert registry.get("sr_m5_phase5_advancement_contract_gate_path") == PHASE5_CONTRACT_GATE_PATH
    assert PHASE5_CONTRACT_GATE_PATH in program_text

    sr_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-SR"), None)
    assert sr_row is not None, "Missing PILLAR-SR row in deep maturity registry."

    m5_parity = sr_row.get("m5_theory_parity", {})
    artifact_path = m5_parity.get("artifact_path")
    assert isinstance(artifact_path, str) and artifact_path, "Missing active SR M5 artifact path."

    artifact_abs = REPO_ROOT / artifact_path
    artifact_json = _read_json(artifact_abs)
    payload = artifact_json.get("payload", {})
    artifact_id = artifact_json.get("artifact_id", "")
    cycle_num = _cycle_number_from_artifact_id(artifact_id)

    assert cycle_num >= INTRO_CYCLE, "Phase-5 advancement contract gate is expected from cycle40 onward."

    delta_token = payload.get("phase5_advancement_delta_token")
    assert isinstance(delta_token, str) and delta_token, "Missing payload.phase5_advancement_delta_token"
    assert delta_token.startswith(f"CYCLE{cycle_num}_"), "Advancement token must be cycle-coupled to active artifact."
    assert delta_token.endswith("_v0"), "Advancement token must be versioned."

    if cycle_num == INTRO_CYCLE:
        assert delta_token == "CYCLE40_ADVANCEMENT_CONTRACT_GATE_INTRODUCED_v0"

    for text in (target_text, sr_text, state_text, roadmap_text):
        assert _extract_token(text, CONTRACT_TOKEN_NAME) == delta_token
        assert _extract_token(text, CONTRACT_GATE_TOKEN_NAME) == PHASE5_CONTRACT_GATE_PATH
