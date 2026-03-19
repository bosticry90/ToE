from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
QFT_GAUGE_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
TRANCHE_GATE_PATH = "formal/python/tests/test_qft_gauge_micro_tranche_01_05_completeness_gate.py"

MICRO_TARGET_IDS = [
    "TARGET-QFT-GAUGE-MICRO-01-GROUP-ACTION-SURFACE-v0",
    "TARGET-QFT-GAUGE-MICRO-02-CONNECTION-SURFACE-v0",
    "TARGET-QFT-GAUGE-MICRO-03-CURVATURE-SURFACE-v0",
    "TARGET-QFT-GAUGE-MICRO-04-GAUGE-TRANSFORM-INVARIANCE-SURFACE-v0",
    "TARGET-QFT-GAUGE-MICRO-05-COUPLING-SOURCE-CURRENT-INTERFACE-v0",
]

MICRO_DOC_PATHS = [
    "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_01_GROUP_ACTION_SURFACE_v0.md",
    "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_02_CONNECTION_SURFACE_v0.md",
    "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_03_CURVATURE_SURFACE_v0.md",
    "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_04_GAUGE_TRANSFORM_INVARIANCE_SURFACE_v0.md",
    "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_05_COUPLING_SOURCE_CURRENT_INTERFACE_v0.md",
]

MICRO_GATE_PATHS = [
    "formal/python/tests/test_qft_gauge_micro01_group_action_surface_gate.py",
    "formal/python/tests/test_qft_gauge_micro02_connection_surface_gate.py",
    "formal/python/tests/test_qft_gauge_micro03_curvature_surface_gate.py",
    "formal/python/tests/test_qft_gauge_micro04_gauge_transform_invariance_surface_gate.py",
    "formal/python/tests/test_qft_gauge_micro05_coupling_source_current_interface_gate.py",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _assert_present_in_order(text: str, ordered_tokens: list[str], label: str) -> None:
    idx = -1
    for token in ordered_tokens:
        next_idx = text.find(token, idx + 1)
        assert next_idx >= 0, f"Missing {label} token `{token}` in QFT gauge umbrella target."
        assert next_idx > idx, f"Out-of-order {label} token `{token}` in QFT gauge umbrella target."
        idx = next_idx


def test_qft_gauge_micro_tranche_artifacts_exist() -> None:
    assert QFT_GAUGE_TARGET_PATH.exists(), "Missing QFT gauge umbrella target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."
    assert INVENTORY_PATH.exists(), "Missing TOE_MATH_PHYSICS_INVENTORY authority surface."


def test_qft_gauge_umbrella_contains_micro_tranche_01_05_targets_docs_and_gates() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)

    _assert_present_in_order(text, MICRO_TARGET_IDS, "micro target")
    _assert_present_in_order(text, MICRO_DOC_PATHS, "micro doc path")
    _assert_present_in_order(text, MICRO_GATE_PATHS, "micro gate path")


def test_qft_gauge_micro_tranche_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert TRANCHE_GATE_PATH in roadmap_text, (
        f"Roadmap authority surface must pin `{TRANCHE_GATE_PATH}`."
    )
    assert TRANCHE_GATE_PATH in state_text or TRANCHE_GATE_PATH in inventory_text, (
        f"State or inventory authority surface must pin `{TRANCHE_GATE_PATH}`."
    )
