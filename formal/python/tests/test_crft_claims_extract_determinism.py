from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.crft_claims_extract import build_payload


def test_crft_claims_extract_is_deterministic(tmp_path: Path) -> None:
    repo_root = tmp_path
    src = repo_root / "archive" / "docs" / "extended.md"
    src.parent.mkdir(parents=True, exist_ok=True)
    src.write_text(
        """C5 — Example\n\nPurpose:\nVerify something.\n\nFields:\n\n• φ(x,t) — field\n\nEquation:\n    ρ_t = −∂x(ρ u)\n\nPass criteria (spec):\n• E ≪ 1\n""",
        encoding="utf-8",
    )

    p1 = build_payload(source_path=src, repo_root=repo_root)
    p2 = build_payload(source_path=src, repo_root=repo_root)

    assert json.dumps(p1, sort_keys=True) == json.dumps(p2, sort_keys=True)
    assert p1["claims"][0]["id"] == "CLM-0001"
    assert p1["source"]["path"] == "archive/docs/extended.md"
