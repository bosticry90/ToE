from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class QftEvidenceDiversificationCycleSpec:
    cycle: int


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
QFT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_compact_state_or_inventory(state_text: str, inventory_text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", state_text)
    if match is not None:
        return match.group(1)
    inventory_match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", inventory_text)
    assert inventory_match is not None, f"Missing token `{token_name}` in compact state and central inventory."
    return inventory_match.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _assign_test(module_globals: dict[str, object], test_name: str, test_callable: object) -> None:
    test_callable.__name__ = test_name
    module_globals[test_name] = test_callable


def register_qft_evidence_diversification_cycle_gate(
    module_globals: dict[str, object], spec: QftEvidenceDiversificationCycleSpec
) -> None:
    cycle_str = f"{spec.cycle:02d}"
    artifact_path = REPO_ROOT / "formal" / "output" / f"qft_evidence_diversification_checkpoint_cycle{cycle_str}_v0.json"
    expected_artifact_id = f"qft_evidence_diversification_checkpoint_cycle{cycle_str}_v0"
    artifact_token_name = f"QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE{cycle_str}_ARTIFACT_v0"
    sha_token_name = f"QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE{cycle_str}_SHA256_v0"
    gate_token_name = f"QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE{cycle_str}_GATE_v0"

    def _test_cycle_gate() -> None:
        qft_text = _read(QFT_DOC_PATH)
        state_text = _read(STATE_PATH)
        roadmap_text = _read(ROADMAP_PATH)
        inventory_text = _read(INVENTORY_PATH)

        assert artifact_path.exists(), f"QFT evidence-diversification cycle-{cycle_str} checkpoint artifact is missing."
        artifact_json = json.loads(artifact_path.read_text(encoding="utf-8"))

        assert "payload" in artifact_json and isinstance(artifact_json["payload"], dict)
        assert "payload_sha256" in artifact_json and isinstance(artifact_json["payload_sha256"], str)

        computed_payload_sha = _payload_hash(artifact_json["payload"])
        assert artifact_json["payload_sha256"] == computed_payload_sha, (
            f"QFT evidence-diversification cycle-{cycle_str} payload_sha256 does not match canonical payload hash."
        )

        qft_artifact_token = _extract_token(qft_text, artifact_token_name)
        state_artifact_token = _extract_token_from_compact_state_or_inventory(
            state_text, inventory_text, artifact_token_name
        )
        roadmap_artifact_token = _extract_token(roadmap_text, artifact_token_name)

        qft_sha_token = _extract_token(qft_text, sha_token_name)
        state_sha_token = _extract_token_from_compact_state_or_inventory(state_text, inventory_text, sha_token_name)
        roadmap_sha_token = _extract_token(roadmap_text, sha_token_name)

        qft_gate_token = _extract_token(qft_text, gate_token_name)
        state_gate_token = _extract_token_from_compact_state_or_inventory(state_text, inventory_text, gate_token_name)
        roadmap_gate_token = _extract_token(roadmap_text, gate_token_name)

        assert qft_artifact_token == roadmap_artifact_token == expected_artifact_id
        assert state_artifact_token == expected_artifact_id
        assert qft_sha_token == roadmap_sha_token == artifact_json["payload_sha256"]
        assert state_sha_token == artifact_json["payload_sha256"]
        assert qft_gate_token == roadmap_gate_token == EXPECTED_COUPLING_GATE
        assert state_gate_token == EXPECTED_COUPLING_GATE

        artifact_rel = f"formal/output/qft_evidence_diversification_checkpoint_cycle{cycle_str}_v0.json"
        assert artifact_rel in qft_text
        assert artifact_rel in state_text or artifact_rel in inventory_text
        assert artifact_rel in roadmap_text

        assert "Keep the lane bounded and non-claim while discharge obligations are assembled." in qft_text
        assert "- `QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0`" in qft_text

    _assign_test(
        module_globals,
        f"test_qft_evidence_diversification_checkpoint_coupling_cycle{cycle_str}_gate",
        _test_cycle_gate,
    )
