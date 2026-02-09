from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_admissibility_manifest_generate import build_bridge_admissibility_manifest_payload


def test_bridge_admissibility_manifest_is_deterministic() -> None:
    repo_root = Path(__file__).resolve()
    while repo_root != repo_root.parent and not (repo_root / "formal").exists():
        repo_root = repo_root.parent
    assert (repo_root / "formal").exists()

    m1 = build_bridge_admissibility_manifest_payload(repo_root=repo_root)
    m2 = build_bridge_admissibility_manifest_payload(repo_root=repo_root)

    assert m1 == m2
    assert m1.get("schema_version") == 1
    assert isinstance(m1.get("artifact_sha256"), str) and len(m1["artifact_sha256"]) == 64
