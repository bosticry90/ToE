from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
GR_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_COMPLETENESS_GATE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_m2_completion_promotion_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "gr_m2_completion_promotion_cycle01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
ROW_KEYS = (
    "analytic_completeness",
    "canonical_equivalence",
    "assumption_minimization",
    "literature_alignment",
)


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


def test_gr_m2_completion_promotion_cycle01_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    gr_text = _read(GR_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    gr_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-GR"), None)
    assert gr_row is not None, "Missing PILLAR-GR row in deep maturity registry."
    assert gr_row.get("m2_status") == "COMPLETE_BOUNDED_v0"

    m2_rows = gr_row.get("m2_exit_rows", {})
    for key in ROW_KEYS:
        row = m2_rows.get(key)
        assert isinstance(row, dict), f"Missing GR M2 row `{key}`."
        assert row.get("token_value") == "RUN_BOUNDED_v0_NONCLAIM", f"GR M2 row `{key}` must be active bounded-run."

    assert ARTIFACT_PATH.exists(), "GR M2 completion promotion artifact is missing."
    artifact_json = _read_json(ARTIFACT_PATH)
    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert isinstance(artifact_json.get("payload"), dict)
    expected_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == expected_sha

    assert _extract_token(gr_text, "GR_M2_STATUS_v0") == "COMPLETE_BOUNDED_v0"
    assert _extract_token(state_text, "GR_M2_STATUS_v0") == "COMPLETE_BOUNDED_v0"
    assert _extract_token(roadmap_text, "GR_M2_STATUS_v0") == "COMPLETE_BOUNDED_v0"

    assert _extract_token(gr_text, "GR_M2_COMPLETION_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(state_text, "GR_M2_COMPLETION_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(roadmap_text, "GR_M2_COMPLETION_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID

    assert _extract_token(gr_text, "GR_M2_COMPLETION_SHA256_v0") == expected_sha
    assert _extract_token(state_text, "GR_M2_COMPLETION_SHA256_v0") == expected_sha
    assert _extract_token(roadmap_text, "GR_M2_COMPLETION_SHA256_v0") == expected_sha

    assert _extract_token(gr_text, "GR_M2_COMPLETION_GATE_v0") == EXPECTED_GATE
    assert _extract_token(state_text, "GR_M2_COMPLETION_GATE_v0") == EXPECTED_GATE
    assert _extract_token(roadmap_text, "GR_M2_COMPLETION_GATE_v0") == EXPECTED_GATE

    artifact_rel = "formal/output/gr_m2_completion_promotion_cycle01_v0.json"
    assert artifact_rel in gr_text
    assert artifact_rel in state_text
    assert artifact_rel in roadmap_text

