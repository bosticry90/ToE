from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
QFT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qft_m2_analytic_completeness_scaffold_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "qft_m2_analytic_completeness_scaffold_cycle01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_compact_state_or_inventory(state_text: str, inventory_text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", state_text)
    if m is not None:
        return m.group(1)
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", inventory_text)
    assert m is not None, f"Missing token `{token_name}` in compact state or central inventory."
    return m.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_qft_m2_analytic_completeness_scaffold_cycle01_gate() -> None:
    qft_text = _read(QFT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert ARTIFACT_PATH.exists(), "QFT M2 analytic completeness scaffold artifact is missing."
    artifact_json = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert isinstance(artifact_json.get("payload"), dict)
    expected_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == expected_sha

    assert _extract_token(qft_text, "QFT_M2_ANALYTIC_COMPLETENESS_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(state_text, "QFT_M2_ANALYTIC_COMPLETENESS_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(roadmap_text, "QFT_M2_ANALYTIC_COMPLETENESS_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"

    assert _extract_token(qft_text, "QFT_M2_ANALYTIC_COMPLETENESS_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(state_text, "QFT_M2_ANALYTIC_COMPLETENESS_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(roadmap_text, "QFT_M2_ANALYTIC_COMPLETENESS_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID

    assert _extract_token(qft_text, "QFT_M2_ANALYTIC_COMPLETENESS_SHA256_v0") == expected_sha
    assert _extract_token(state_text, "QFT_M2_ANALYTIC_COMPLETENESS_SHA256_v0") == expected_sha
    assert _extract_token(roadmap_text, "QFT_M2_ANALYTIC_COMPLETENESS_SHA256_v0") == expected_sha

    assert _extract_token(qft_text, "QFT_M2_ANALYTIC_COMPLETENESS_GATE_v0") == EXPECTED_GATE
    assert _extract_token(state_text, "QFT_M2_ANALYTIC_COMPLETENESS_GATE_v0") == EXPECTED_GATE
    assert _extract_token(roadmap_text, "QFT_M2_ANALYTIC_COMPLETENESS_GATE_v0") == EXPECTED_GATE

    assert _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "QFT_M2_ANALYTIC_COMPLETENESS_STATUS_v0"
    ) == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "QFT_M2_ANALYTIC_COMPLETENESS_ARTIFACT_v0"
    ) == EXPECTED_ARTIFACT_ID
    assert _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "QFT_M2_ANALYTIC_COMPLETENESS_SHA256_v0"
    ) == expected_sha
    assert _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "QFT_M2_ANALYTIC_COMPLETENESS_GATE_v0"
    ) == EXPECTED_GATE

    artifact_rel = "formal/output/qft_m2_analytic_completeness_scaffold_cycle01_v0.json"
    assert artifact_rel in qft_text
    assert artifact_rel in state_text or artifact_rel in inventory_text
    assert artifact_rel in roadmap_text

