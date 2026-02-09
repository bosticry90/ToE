from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.toy_topological_invariants_report_generate import (
    DEFAULT_OUT_PATH,
    build_toy_topological_invariants_report_payload,
    render_toy_topological_invariants_report_text,
)


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_toy_topological_invariants_report_artifact_matches_generator() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    report_path = repo_root / Path(DEFAULT_OUT_PATH)
    assert report_path.exists(), "Expected pinned topological-invariants report artifact to exist"

    actual_text = report_path.read_text(encoding="utf-8")
    expected_text = render_toy_topological_invariants_report_text(
        build_toy_topological_invariants_report_payload()
    )
    assert actual_text == expected_text

    payload = json.loads(actual_text)
    assert payload.get("schema") == "TOY/topological_invariants_report/v1"
    assert payload.get("candidate_id") == "G1_sign_change"
    assert isinstance(payload.get("fingerprint"), str) and len(payload["fingerprint"]) == 64
