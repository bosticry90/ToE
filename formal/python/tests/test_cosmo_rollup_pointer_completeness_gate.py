from __future__ import annotations

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
TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
SUMMARY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md"
PACKAGE_PATH = REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _expected_micro_indices() -> list[str]:
    return [f"{i:02d}" for i in range(1, 30)]


def _extract_micro_doc_paths(target_text: str) -> dict[str, str]:
    pattern = re.compile(
        r"formal/docs/paper/(DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_(?P<idx>\d{2})_[A-Z0-9_]+_v0\.md)"
    )
    found: dict[str, str] = {}
    for match in pattern.finditer(target_text):
        found[match.group("idx")] = "formal/docs/paper/" + match.group(1)
    return found


def _extract_micro_output_paths(target_text: str) -> dict[str, str]:
    pattern = re.compile(
        r"formal/output/(cosmo_bg_micro(?P<idx>\d{2})_[a-z0-9_]+_cycle01_v0\.json)"
    )
    found: dict[str, str] = {}
    for match in pattern.finditer(target_text):
        found[match.group("idx")] = "formal/output/" + match.group(1)
    return found


def _extract_micro_gate_paths(target_text: str) -> dict[str, str]:
    pattern = re.compile(
        r"formal/python/tests/(test_cosmo_bg_micro(?P<idx>\d{2})_[a-z0-9_]+_gate\.py)"
    )
    found: dict[str, str] = {}
    for match in pattern.finditer(target_text):
        found[match.group("idx")] = "formal/python/tests/" + match.group(1)
    return found


def test_cosmo_target_has_complete_micro_pointer_set_01_to_27() -> None:
    target_text = _read(TARGET_PATH)
    expected = _expected_micro_indices()

    micro_docs = _extract_micro_doc_paths(target_text)
    micro_outputs = _extract_micro_output_paths(target_text)
    micro_gates = _extract_micro_gate_paths(target_text)

    assert sorted(micro_docs.keys()) == expected, "COSMO target micro doc pointer set must be complete for 01-27."
    assert sorted(micro_outputs.keys()) == expected, "COSMO target micro output pointer set must be complete for 01-27."
    assert sorted(micro_gates.keys()) == expected, "COSMO target micro gate pointer set must be complete for 01-27."


def test_cosmo_rollup_package_contains_all_micro_doc_and_output_pointers_from_target() -> None:
    target_text = _read(TARGET_PATH)
    package_text = _read(PACKAGE_PATH)

    micro_docs = _extract_micro_doc_paths(target_text)
    micro_outputs = _extract_micro_output_paths(target_text)

    missing_docs = [path for _, path in sorted(micro_docs.items()) if path not in package_text]
    missing_outputs = [path for _, path in sorted(micro_outputs.items()) if path not in package_text]

    assert not missing_docs, "COSMO package missing micro-doc pointer(s): " + ", ".join(missing_docs)
    assert not missing_outputs, "COSMO package missing micro-output pointer(s): " + ", ".join(missing_outputs)


def test_cosmo_rollup_summary_contains_progress_tokens_01_to_27_and_external_pilot() -> None:
    summary_text = _read(SUMMARY_PATH)
    missing_progress = [
        f"COSMO_BG_MICRO{idx}_PROGRESS_v0:" for idx in _expected_micro_indices() if f"COSMO_BG_MICRO{idx}_PROGRESS_v0:" not in summary_text
    ]
    assert not missing_progress, "COSMO summary missing micro progress token(s): " + ", ".join(missing_progress)

    required_external = [
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_PROGRESS_v0: REFERENCE_SURFACE_POLICY_GATE_PINNED",
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_TARGET_v0: TARGET-COSMO-BG-EXTERNAL-HI-REFERENCE-SURFACE-v0",
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_BOUNDARY_v0: REFERENCE_ONLY_NON_PROMOTIONAL",
    ]
    missing_external = [token for token in required_external if token not in summary_text]
    assert not missing_external, "COSMO summary missing external-pilot token(s): " + ", ".join(missing_external)


def test_cosmo_state_and_suite_anchor_pointer_completeness_gate() -> None:
    state_text = _read(STATE_PATH)
    suite_text = _read(SUITE_PATH)

    required_state_tokens = [
        "COSMO rollup checkpoint (2026-03-01):",
        "formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py",
        "formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py",
        "formal/python/tests/test_cosmo_rollup_pointer_completeness_gate.py",
    ]
    missing_state = [token for token in required_state_tokens if token not in state_text]
    assert not missing_state, "COSMO state checkpoint missing pointer-completeness anchors: " + ", ".join(missing_state)

    gate_path = "formal/python/tests/test_cosmo_rollup_pointer_completeness_gate.py"
    assert gate_path in suite_text, "governance_suite.ps1 must execute the COSMO rollup pointer completeness gate."
