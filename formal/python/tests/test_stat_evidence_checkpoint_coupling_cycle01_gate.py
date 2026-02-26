from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STAT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_evidence_checkpoint_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "stat_evidence_checkpoint_cycle01_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_ARTIFACT_REL = "formal/output/stat_evidence_checkpoint_cycle01_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_evidence_checkpoint_coupling_cycle01_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_stat_evidence_checkpoint_coupling_cycle01_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)

    assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text, (
        "STAT cycle01 evidence checkpoint coupling gate applies only after `PILLAR-STAT` activation."
    )
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist for active-cycle checkpoint coupling gate."
    assert stat_matrix.get("matrix_status") == "ACTIVE", "PILLAR-STAT matrix row must be `ACTIVE`."

    assert ARTIFACT_PATH.exists(), "STAT evidence checkpoint cycle-01 artifact is missing."
    artifact_json = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert "payload" in artifact_json and isinstance(artifact_json["payload"], dict)
    assert "payload_sha256" in artifact_json and isinstance(artifact_json["payload_sha256"], str)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json["payload_sha256"] == computed_payload_sha, (
        "STAT cycle-01 payload_sha256 does not match canonical payload hash."
    )

    stat_artifact_token = _extract_token(stat_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_v0")
    state_artifact_token = _extract_token(state_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_v0")
    roadmap_artifact_token = _extract_token(roadmap_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_v0")

    stat_sha_token = _extract_token(stat_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_SHA256_v0")
    state_sha_token = _extract_token(state_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_SHA256_v0")
    roadmap_sha_token = _extract_token(roadmap_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_SHA256_v0")

    stat_gate_token = _extract_token(stat_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_GATE_v0")
    state_gate_token = _extract_token(state_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_GATE_v0")
    roadmap_gate_token = _extract_token(roadmap_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_GATE_v0")

    assert stat_artifact_token == state_artifact_token == roadmap_artifact_token == EXPECTED_ARTIFACT_ID
    assert stat_sha_token == state_sha_token == roadmap_sha_token == artifact_json["payload_sha256"]
    assert stat_gate_token == state_gate_token == roadmap_gate_token == EXPECTED_COUPLING_GATE

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert EXPECTED_ARTIFACT_REL in doc_text, f"{doc_label} must pin STAT cycle-01 artifact path."
        assert EXPECTED_GATE_REL in doc_text, f"{doc_label} must pin STAT cycle-01 coupling gate path."

    assert "non-claim boundary remains explicit and binding for this artifact." in stat_text
    assert "no entropy derivation discharge claim" in stat_text
    assert "no adequacy completion claim" in stat_text

    payload = artifact_json["payload"]
    assert payload.get("target_id") == "TARGET-TH-ENTROPY-PLAN"
    assert payload.get("status") == "structural_activation_checkpoint_placeholder"
    assert payload.get("required_results_rows_refs") == ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]
    assert payload.get("artifact_sha256") == "TOP_LEVEL_payload_sha256"
    assert EXPECTED_GATE_REL in payload.get("cross_surface_pointers", [])
