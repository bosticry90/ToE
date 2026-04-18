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
COSMO_MICRO05_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_05_PACKAGE_FREEZE_REOPEN_POLICY_v0.md"
)
COSMO_MICRO05_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_micro05_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
    assert COSMO_MICRO05_PATH.exists(), "Missing COSMO background Cycle-005 micro document."
    assert COSMO_MICRO05_ARTIFACT_PATH.exists(), "Missing COSMO background Cycle-005 artifact payload."


def test_cosmo_target_references_micro05_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "TARGET-COSMO-BG-MICRO-05-PACKAGE-FREEZE-REOPEN-POLICY-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_05_PACKAGE_FREEZE_REOPEN_POLICY_v0.md",
        "formal/output/cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro05_package_freeze_reopen_policy_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target is missing required micro-05 token(s): " + ", ".join(missing)


def test_cosmo_micro05_doc_contains_required_tokens() -> None:
    text = _read(COSMO_MICRO05_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_05_PACKAGE_FREEZE_REOPEN_POLICY_v0",
        "TARGET-COSMO-BG-MICRO-05-PACKAGE-FREEZE-REOPEN-POLICY-v0",
        "COSMO_BG_MICRO05_PACKAGE_FREEZE_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO05_SCOPE_BOUNDARY_v0: PACKAGE_FREEZE_REOPEN_POLICY_ONLY_NONCLAIM",
        "COSMO_BG_MICRO05_PROGRESS_v0: PACKAGE_FREEZE_REOPEN_POLICY_TOKEN_PINNED",
        "COSMO_BG_MICRO05_PACKAGE_FREEZE_ARTIFACT_v0: cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0",
        "COSMO_BG_MICRO05_PACKAGE_FREEZE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "COSMO_BG_MICRO05_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "COSMO_BG_MICRO05_REOPEN_TRIGGER_SURFACE_DRIFT_v0: ENABLED",
        "COSMO_BG_MICRO05_REOPEN_TRIGGER_SCOPE_REGRESSION_v0: ENABLED",
        "formal/output/cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0.json",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO micro-05 document is missing required token(s): " + ", ".join(missing)


def test_cosmo_micro05_required_package_contents_are_pinned() -> None:
    text = _read(COSMO_MICRO05_PATH)
    required_paths = [
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_01_OBJECT_SURFACE_v0.md",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0.md",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_03_SOURCE_COUPLING_SURFACE_v0.md",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_04_REGIME_FALSIFIABILITY_SURFACE_v0.md",
    ]
    missing = [path for path in required_paths if path not in text]
    assert not missing, "COSMO micro-05 required package content pointers missing: " + ", ".join(missing)


def test_cosmo_micro05_nonclaim_boundary_is_explicit() -> None:
    text = _read(COSMO_MICRO05_PATH)
    required_nonclaim_phrases = [
        "package-freeze/reopen-policy scaffold scope only.",
        "no Einstein-equation closure claim.",
        "no Friedmann derivation closure claim.",
        "no perturbation-theory closure claim.",
        "no full cosmological model completion claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "COSMO micro-05 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_cosmo_micro05_artifact_schema_and_token_alignment() -> None:
    payload = _read_json(COSMO_MICRO05_ARTIFACT_PATH)

    assert payload.get("artifact_id") == "cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0"
    assert payload.get("artifact_version") == "v0"
    assert payload.get("placeholder_template") is True

    body = payload.get("payload")
    assert isinstance(body, dict), "Artifact payload block must be an object."
    assert body.get("checkpoint") == "cosmo_bg_micro05_package_freeze_reopen_policy_cycle01"
    assert body.get("status") == "placeholder_non_promotional"
    assert body.get("scope") == "package_freeze_reopen_policy_only_nonclaim_v0"

    freeze_rows = body.get("package_freeze_tokens")
    assert isinstance(freeze_rows, list) and len(freeze_rows) == 4, (
        "COSMO micro-05 artifact must include exactly four package_freeze_tokens rows."
    )
    for token in [
        "COSMO_BG_MICRO05_PACKAGE_FREEZE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "COSMO_BG_MICRO05_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "COSMO_BG_MICRO05_REOPEN_TRIGGER_SURFACE_DRIFT_v0: ENABLED",
        "COSMO_BG_MICRO05_REOPEN_TRIGGER_SCOPE_REGRESSION_v0: ENABLED",
    ]:
        assert token in freeze_rows

    required_contents = body.get("required_package_contents")
    assert isinstance(required_contents, list) and len(required_contents) == 4, (
        "COSMO micro-05 artifact must include exactly four required_package_contents rows."
    )
