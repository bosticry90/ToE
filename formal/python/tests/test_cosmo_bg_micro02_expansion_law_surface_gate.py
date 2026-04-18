from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
)
COSMO_MICRO02_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0.md"
)
COSMO_MICRO02_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_bg_micro02_expansion_law_surface_cycle01_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_micro02_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
    assert COSMO_MICRO02_PATH.exists(), "Missing COSMO background Cycle-002 micro document."
    assert COSMO_MICRO02_ARTIFACT_PATH.exists(), "Missing COSMO background Cycle-002 artifact payload."


def test_cosmo_target_references_micro02_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "TARGET-COSMO-BG-MICRO-02-EXPANSION-LAW-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0.md",
        "formal/output/cosmo_bg_micro02_expansion_law_surface_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro02_expansion_law_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target is missing required micro-02 token(s): " + ", ".join(missing)


def test_cosmo_micro02_doc_contains_required_tokens() -> None:
    text = _read(COSMO_MICRO02_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0",
        "TARGET-COSMO-BG-MICRO-02-EXPANSION-LAW-SURFACE-v0",
        "COSMO_BG_MICRO02_EXPANSION_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO02_SCOPE_BOUNDARY_v0: EXPANSION_LAW_SURFACE_ONLY_NONCLAIM",
        "COSMO_BG_MICRO02_PROGRESS_v0: EXPANSION_LAW_SURFACE_TOKEN_PINNED",
        "COSMO_BG_MICRO02_EXPANSION_SURFACE_ARTIFACT_v0: cosmo_bg_micro02_expansion_law_surface_cycle01_v0",
        "COSMO_BG_MICRO02_EXPANSION_RELATION_SURFACE_v0: HUBBLE_SCALE_FACTOR_RELATION_PLACEHOLDER_PINNED",
        "COSMO_BG_MICRO02_CURVATURE_SURFACE_v0: SPATIAL_CURVATURE_TERM_PLACEHOLDER_PINNED",
        "COSMO_BG_MICRO02_SOURCE_COUPLING_SURFACE_v0: EFFECTIVE_DENSITY_PRESSURE_COUPLING_PLACEHOLDER_PINNED",
        "COSMO_BG_MICRO02_REGIME_SURFACE_v0: HOMOGENEITY_ISOTROPY_BOUNDARY_PLACEHOLDER_PINNED",
        "formal/output/cosmo_bg_micro02_expansion_law_surface_cycle01_v0.json",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO micro-02 document is missing required token(s): " + ", ".join(missing)


def test_cosmo_micro02_nonclaim_boundary_is_explicit() -> None:
    text = _read(COSMO_MICRO02_PATH)
    required_nonclaim_phrases = [
        "expansion-law scaffold scope only.",
        "no Einstein-equation closure claim.",
        "no Friedmann derivation closure claim.",
        "no perturbation-theory closure claim.",
        "no full cosmological model completion claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "COSMO micro-02 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_cosmo_micro02_artifact_schema_and_token_alignment() -> None:
    payload = _read_json(COSMO_MICRO02_ARTIFACT_PATH)

    assert payload.get("artifact_id") == "cosmo_bg_micro02_expansion_law_surface_cycle01_v0"
    assert payload.get("artifact_version") == "v0"
    assert payload.get("placeholder_template") is True

    body = payload.get("payload")
    assert isinstance(body, dict), "Artifact payload block must be an object."
    assert body.get("checkpoint") == "cosmo_bg_micro02_expansion_law_surface_cycle01"
    assert body.get("status") == "placeholder_non_promotional"
    assert body.get("scope") == "expansion_law_surface_only_nonclaim_v0"

    token_rows = body.get("expansion_surface_tokens")
    assert isinstance(token_rows, list) and len(token_rows) == 4, (
        "COSMO micro-02 artifact must include exactly four expansion_surface_tokens rows."
    )
    for token in [
        "COSMO_BG_MICRO02_EXPANSION_RELATION_SURFACE_v0: HUBBLE_SCALE_FACTOR_RELATION_PLACEHOLDER_PINNED",
        "COSMO_BG_MICRO02_CURVATURE_SURFACE_v0: SPATIAL_CURVATURE_TERM_PLACEHOLDER_PINNED",
        "COSMO_BG_MICRO02_SOURCE_COUPLING_SURFACE_v0: EFFECTIVE_DENSITY_PRESSURE_COUPLING_PLACEHOLDER_PINNED",
        "COSMO_BG_MICRO02_REGIME_SURFACE_v0: HOMOGENEITY_ISOTROPY_BOUNDARY_PLACEHOLDER_PINNED",
    ]:
        assert token in token_rows
