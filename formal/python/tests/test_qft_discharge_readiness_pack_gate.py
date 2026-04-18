from __future__ import annotations

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
PACK_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "QFT_DISCHARGE_READINESS_PACK_v0.md"
DISCHARGE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

CRIT_HEADER = re.compile(r"(?m)^###\s+(QFT-CRIT-\d{2})\s+(.+)$")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_surfaces(token_name: str, *surfaces: str) -> str:
    for surface in surfaces:
        m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", surface)
        if m is not None:
            return m.group(1)
    assert False, f"Missing token `{token_name}` across authority surfaces."


def _extract_backticked_paths(line: str) -> list[str]:
    return re.findall(r"`([^`]+)`", line)


def _criterion_blocks(text: str) -> list[tuple[str, str]]:
    starts = list(CRIT_HEADER.finditer(text))
    assert starts, "Readiness pack must contain at least one `QFT-CRIT-XX` criterion header."

    blocks: list[tuple[str, str]] = []
    for idx, match in enumerate(starts):
        criterion_id = match.group(1)
        start = match.start()
        end = starts[idx + 1].start() if idx + 1 < len(starts) else len(text)
        blocks.append((criterion_id, text[start:end]))
    return blocks


def test_qft_discharge_readiness_pack_is_complete_and_cross_surface_pinned() -> None:
    pack_text = _read(PACK_PATH)
    discharge_text = _read(DISCHARGE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    matrix = _read_json(MATRIX_PATH)

    assert "Classification:" in pack_text and "`P-POLICY`" in pack_text
    assert "## DISCHARGE_CRITERIA_MAP" in pack_text

    blocks = _criterion_blocks(pack_text)
    assert len(blocks) >= 4, "Readiness pack must define at least 4 discharge criteria."

    for criterion_id, block in blocks:
        enforcing_line_match = re.search(r"(?m)^- Enforcing tests:\s*(.+)$", block)
        assert enforcing_line_match is not None, f"{criterion_id}: missing `Enforcing tests` line."
        enforcing_tests = _extract_backticked_paths(enforcing_line_match.group(1))
        assert enforcing_tests, f"{criterion_id}: must include at least one enforcing test path."

        artifact_line_match = re.search(r"(?m)^- Artifact pointers:\s*(.+)$", block)
        assert artifact_line_match is not None, f"{criterion_id}: missing `Artifact pointers` line."
        artifact_paths = _extract_backticked_paths(artifact_line_match.group(1))
        assert artifact_paths, f"{criterion_id}: must include at least one artifact path."

        for test_rel in enforcing_tests:
            test_path = REPO_ROOT / test_rel
            assert test_path.exists(), f"{criterion_id}: missing enforcing test file `{test_rel}`."
            assert test_rel in roadmap_text, f"{criterion_id}: enforcing test `{test_rel}` must be pinned in roadmap."
            assert test_rel in state_text or test_rel in inventory_text, (
                f"{criterion_id}: enforcing test `{test_rel}` must be pinned in state or inventory."
            )
            assert test_rel in pack_text, f"{criterion_id}: enforcing test `{test_rel}` must be pinned in readiness pack."

        for artifact_rel in artifact_paths:
            artifact_path = REPO_ROOT / artifact_rel if artifact_rel != "State_of_the_Theory.md" else STATE_PATH
            assert artifact_path.exists(), f"{criterion_id}: missing artifact pointer target `{artifact_rel}`."

    qft_matrix = matrix.get("pillars", {}).get("PILLAR-QFT", {})
    assert qft_matrix, "PILLAR_STATUS_MATRIX_v1.json must define a PILLAR-QFT row."

    canonical_adjudication = _extract_token(discharge_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    canonical_inevitability = _extract_token(discharge_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")
    state_or_inventory_adjudication = _extract_token_from_surfaces(
        "QFT_FULL_DERIVATION_ADJUDICATION", state_text, inventory_text, roadmap_text, pack_text
    )
    state_or_inventory_inevitability = _extract_token_from_surfaces(
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION",
        state_text,
        inventory_text,
        roadmap_text,
        pack_text,
    )
    roadmap_adjudication = _extract_token(roadmap_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    roadmap_inevitability = _extract_token(roadmap_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")
    pack_adjudication = _extract_token(pack_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    pack_inevitability = _extract_token(pack_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")

    assert (
        canonical_adjudication
        == state_or_inventory_adjudication
        == roadmap_adjudication
        == pack_adjudication
    )
    assert (
        canonical_inevitability
        == state_or_inventory_inevitability
        == roadmap_inevitability
        == pack_inevitability
    )

    assert qft_matrix.get("full_derivation") == canonical_adjudication
    assert qft_matrix.get("inevitability") == canonical_inevitability
    assert qft_matrix.get("matrix_status") == "CLOSED"
