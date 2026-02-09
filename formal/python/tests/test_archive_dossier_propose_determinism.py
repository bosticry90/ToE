from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.archive_dossier_propose import rank_candidates, write_outputs


def _write(p: Path, data: bytes) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data)


def test_dossier_proposal_is_deterministic(tmp_path: Path) -> None:
    repo_root = tmp_path
    archive_root = repo_root / "archive"

    # Create two files with different content signals.
    _write(archive_root / "docs" / "a.md", b"# UCFF note\n\n$$E=mc^2$$\n")
    _write(archive_root / "code" / "b.py", b"\"\"\"CRFT diagnostic\"\"\"\nimport sympy as sp\n")

    intake = {
        "schema_version": 1,
        "roots": ["archive"],
        "files": [
            {
                "path": "archive/docs/a.md",
                "sha256": "x" * 64,
                "bytes": 1,
                "kind": "markdown",
                "title": "UCFF note",
                "docstring": None,
            },
            {
                "path": "archive/code/b.py",
                "sha256": "y" * 64,
                "bytes": 1,
                "kind": "python",
                "title": None,
                "docstring": "CRFT diagnostic",
            },
        ],
    }

    ranked1 = rank_candidates(repo_root=repo_root, intake_payload=intake)
    ranked2 = rank_candidates(repo_root=repo_root, intake_payload=intake)

    assert [c.path for c in ranked1] == [c.path for c in ranked2]
    assert json.dumps([c.__dict__ for c in ranked1], sort_keys=True) == json.dumps(
        [c.__dict__ for c in ranked2], sort_keys=True
    )

    out1 = repo_root / "formal" / "output" / "archive_candidate_ranking.json"
    dossiers1 = repo_root / "formal" / "quarantine" / "dossiers"
    write_outputs(repo_root=repo_root, ranked=ranked1, top_n=2, ranking_out=out1, dossiers_dir=dossiers1)

    # Re-run to ensure byte-for-byte stable outputs.
    out2 = repo_root / "formal" / "output" / "archive_candidate_ranking2.json"
    dossiers2 = repo_root / "formal" / "quarantine" / "dossiers2"
    write_outputs(repo_root=repo_root, ranked=ranked2, top_n=2, ranking_out=out2, dossiers_dir=dossiers2)

    assert out1.read_bytes() == out2.read_bytes()
    assert sorted(p.name for p in dossiers1.glob("*.md")) == sorted(p.name for p in dossiers2.glob("*.md"))
    for p1 in dossiers1.glob("*.md"):
        p2 = dossiers2 / p1.name
        assert p1.read_bytes() == p2.read_bytes()
