from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tests.tools import update_admissibility_manifest as updater


def _write(p: Path, text: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


def test_explicit_enable_list_requires_allow_flag(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo_root = tmp_path / "repo"

    lean_src = (
        repo_root
        / "formal"
        / "toe_formal"
        / "ToeFormal"
        / "Constraints"
        / "AD00_AdmissibilityManifest.lean"
    )
    gates_root = repo_root / "formal" / "toe_formal" / "ToeFormal" / "Gates"
    constraints_root = repo_root / "formal" / "toe_formal" / "ToeFormal" / "Constraints"
    manifest_path = repo_root / "formal" / "markdown locks" / "gates" / "admissibility_manifest.json"

    # Lean defaults: all disabled.
    _write(
        lean_src,
        """namespace ToeFormal\nnamespace Constraints\n\n/- BEGIN_ADMISSIBILITY_MANIFEST_JSON\n{\n  \"version\": 1,\n  \"gates\": {\n    \"CT01\": {\"enabled\": false},\n    \"SYM01\": {\"enabled\": false},\n    \"CAUS01\": {\"enabled\": false}\n  }\n}\nEND_ADMISSIBILITY_MANIFEST_JSON -/\n\nend Constraints\nend ToeFormal\n\nnamespace ToeFormal\nnamespace Gates\n\ndef defaultEnabled : List String := []\n\nend Gates\nend ToeFormal\n""",
    )

    for gate_id in ["CT01", "SYM01", "CAUS01"]:
        _write(gates_root / f"{gate_id}.lean", "namespace ToeFormal.Gates\nopaque X : Prop\nend ToeFormal.Gates\n")

    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(
        json.dumps(
            {
                "version": 1,
                "root": "formal/toe_formal/ToeFormal/Constraints",
                "origin": {"type": "lean_literal", "path": str(lean_src).replace("\\", "/"), "sha256": "0"},
                "gates": {
                    "CT01": {"enabled": False, "tracked": {}},
                    "SYM01": {"enabled": False, "tracked": {}},
                    "CAUS01": {"enabled": False, "tracked": {}},
                },
                "tracked": {},
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    # Default disabled policy.
    monkeypatch.setattr(updater, "DEFAULT_ENABLED_GATES", [], raising=False)

    rc = updater.main(
        [
            "--repo-root",
            str(repo_root),
            "--manifest-path",
            str(manifest_path),
            "--lean-manifest-src",
            str(lean_src),
            "--constraints-root",
            str(constraints_root),
            "--gates-root",
            str(gates_root),
            "--enable-gates",
            "CT01,SYM01,CAUS01",
        ]
    )
    assert rc != 0

    obj = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert obj["gates"]["CT01"]["enabled"] is False

    rc2 = updater.main(
        [
            "--allow-enable",
            "--repo-root",
            str(repo_root),
            "--manifest-path",
            str(manifest_path),
            "--lean-manifest-src",
            str(lean_src),
            "--constraints-root",
            str(constraints_root),
            "--gates-root",
            str(gates_root),
            "--enable-gates",
            "CT01,SYM01,CAUS01",
        ]
    )
    assert rc2 == 0

    obj2 = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert obj2["gates"]["CT01"]["enabled"] is True
    assert obj2["gates"]["SYM01"]["enabled"] is True
    assert obj2["gates"]["CAUS01"]["enabled"] is True
