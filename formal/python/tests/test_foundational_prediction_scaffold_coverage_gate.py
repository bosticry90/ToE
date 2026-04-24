from __future__ import annotations

import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_PREDICTION_SCAFFOLD_PLAN_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

M3_DOCS = {
    "QM_M3": REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_M3_COMPLETION_PROMOTION_v0.md",
    "GR_M3": REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md",
    "STAT_M3": REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_M3_COMPLETION_PROMOTION_v0.md",
    "COSMO_M3": REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMO_M3_COMPLETION_PROMOTION_v0.md",
    "EM_M3": REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_M3_COMPLETION_PROMOTION_v0.md",
    "QFT_M3": REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_M3_COMPLETION_PROMOTION_v0.md",
    "SR_M3": REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_M3_COMPLETION_PROMOTION_v0.md",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_foundational_prediction_plan_surface_is_pinned() -> None:
    plan_text = _read(PLAN_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for token in (
        "FOUNDATIONAL_PREDICTION_SCAFFOLD_PLAN_v0",
        "residual observable definition",
        "alternative comparator definition",
        "elimination criterion",
        "uncertainty and bounded validity window",
    ):
        assert token in plan_text, f"Prediction plan missing token `{token}`."

    rel = "formal/docs/release/FOUNDATIONAL_PREDICTION_SCAFFOLD_PLAN_v0.md"
    assert rel in roadmap_text, "Roadmap must pin foundational prediction scaffold plan."
    assert rel in state_text, "State must pin foundational prediction scaffold plan."


def test_all_m3_docs_pin_prediction_scaffold_status_token() -> None:
    for lane_prefix, path in M3_DOCS.items():
        text = _read(path)
        token = f"{lane_prefix}_PREDICTION_SCAFFOLD_STATUS_v0"
        assert _extract_token(text, token) == "SCAFFOLD_PINNED_NONCLAIM"
