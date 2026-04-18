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
COSMO_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Cosmology" / "BackgroundObjectScaffold.lean"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"

EXPECTED_GATE = "ARTIFACT_HASH_ROW_LABEL_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_GATE_REL = "formal/python/tests/test_cosmo_der02_closure_package_cycle01_gate.py"
EXPECTED_ROW_BINDINGS = {
    "COSMO_DER02_THEOREM_BODY_SCOPE_BOUNDARY": "TOE_COSMO_DER_02_T_PROVED_THEOREM_BODY_SCOPE_BOUNDARY_PINNED_NONCLAIM",
    "COSMO_DER02_THEOREM_BODY_SCAFFOLD": "TOE_COSMO_DER_02_T_PROVED_THEOREM_BODY_SCAFFOLD_PINNED_NONCLAIM",
    "COSMO_DER02_DISCHARGE_SCAFFOLD": "TOE_COSMO_DER_02_T_PROVED_DISCHARGE_SCAFFOLD_PINNED_NONCLAIM",
    "COSMO_DER02_OBJECT_SURFACE_SCAFFOLD": "TOE_COSMO_DER_02_T_PROVED_OBJECT_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
}
ARTIFACT_SPECS = [
    (
        "COSMO_DER02_THEOREM_BODY_SCOPE_BOUNDARY",
        "cosmo_der02_theorem_body_scope_boundary_cycle01_v0",
        "formal/output/cosmo_der02_theorem_body_scope_boundary_cycle01_v0.json",
    ),
    (
        "COSMO_DER02_THEOREM_BODY_SCAFFOLD",
        "cosmo_der02_theorem_body_scaffold_cycle01_v0",
        "formal/output/cosmo_der02_theorem_body_scaffold_cycle01_v0.json",
    ),
    (
        "COSMO_DER02_DISCHARGE_SCAFFOLD",
        "cosmo_der02_discharge_scaffold_cycle01_v0",
        "formal/output/cosmo_der02_discharge_scaffold_cycle01_v0.json",
    ),
    (
        "COSMO_DER02_OBJECT_SURFACE_SCAFFOLD",
        "cosmo_der02_object_surface_scaffold_cycle01_v0",
        "formal/output/cosmo_der02_object_surface_scaffold_cycle01_v0.json",
    ),
]


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


def test_cosmo_der02_closure_package_cycle01_gate() -> None:
    cosmo_text = _read(COSMO_DOC_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    results_text = _read(RESULTS_PATH)
    lean_text = _read(LEAN_PATH)
    suite_text = _read(SUITE_PATH)

    for token_prefix, artifact_id, artifact_rel in ARTIFACT_SPECS:
        artifact_path = REPO_ROOT / artifact_rel
        artifact_json = _read_json(artifact_path)
        payload_sha = _payload_hash(artifact_json["payload"])

        assert artifact_json.get("artifact_id") == artifact_id
        assert artifact_json.get("artifact_version") == "v0"
        assert artifact_json.get("placeholder_template") is False
        assert artifact_json.get("payload_sha256") == payload_sha

        assert _extract_token(cosmo_text, f"{token_prefix}_CYCLE01_ARTIFACT_v0") == artifact_id
        assert _extract_token(roadmap_text, f"{token_prefix}_CYCLE01_ARTIFACT_v0") == artifact_id
        assert _extract_token(state_text, f"{token_prefix}_CYCLE01_ARTIFACT_v0") == artifact_id

        assert _extract_token(cosmo_text, f"{token_prefix}_CYCLE01_SHA256_v0") == payload_sha
        assert _extract_token(roadmap_text, f"{token_prefix}_CYCLE01_SHA256_v0") == payload_sha
        assert _extract_token(state_text, f"{token_prefix}_CYCLE01_SHA256_v0") == payload_sha

        assert _extract_token(cosmo_text, f"{token_prefix}_CYCLE01_GATE_v0") == EXPECTED_GATE
        assert _extract_token(roadmap_text, f"{token_prefix}_CYCLE01_GATE_v0") == EXPECTED_GATE
        assert _extract_token(state_text, f"{token_prefix}_CYCLE01_GATE_v0") == EXPECTED_GATE

        assert _extract_token(cosmo_text, f"{token_prefix}_ROW_BINDING_v0") == EXPECTED_ROW_BINDINGS[token_prefix]
        assert _extract_token(roadmap_text, f"{token_prefix}_ROW_BINDING_v0") == EXPECTED_ROW_BINDINGS[token_prefix]
        assert _extract_token(state_text, f"{token_prefix}_ROW_BINDING_v0") == EXPECTED_ROW_BINDINGS[token_prefix]

        for doc_text in (cosmo_text, roadmap_text, state_text):
            assert artifact_rel in doc_text
            assert EXPECTED_GATE_REL in doc_text

    for theorem_token in [
        "cosmo_der02_theorem_body_scope_boundary_cycle01_v0",
        "cosmo_der02_theorem_body_scaffold_cycle01_v0",
        "cosmo_der02_discharge_scaffold_cycle01_v0",
        "cosmo_der02_object_surface_scaffold_cycle01_v0",
    ]:
        assert theorem_token in lean_text

    assert "| TOE-COSMO-DER-02 | `T-PROVED` |" in results_text
    assert EXPECTED_GATE_REL in results_text
    assert EXPECTED_GATE_REL in suite_text
