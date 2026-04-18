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
PACKET02_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json"
CHAIN_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_packet02_non_inconclusive_decisions_reference_m4_seam_surfaces() -> None:
    packet02 = _read_json(PACKET02_MATRIX_PATH).get("rows", {})
    phase_rows = _read_json(CHAIN_MATRIX_PATH).get("phase_rows", {})

    for lane, row in packet02.items():
        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        payload = artifact.get("payload", {})
        if payload.get("decision") == "INCONCLUSIVE_v0":
            continue

        assert lane in phase_rows, f"{lane}: missing phase_rows mapping for seam coupling check."
        m4_doc = phase_rows[lane]["m4"]["source_doc"]
        seam_pointer = payload.get("m4_seam_closure_pointer")
        assert seam_pointer == m4_doc, (
            f"{lane}: non-inconclusive packet-02 decisions must point to m4 seam doc `{m4_doc}`."
        )
        assert (REPO_ROOT / seam_pointer).exists(), f"{lane}: missing seam pointer file `{seam_pointer}`."
