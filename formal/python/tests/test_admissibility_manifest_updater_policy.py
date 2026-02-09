from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tests.tools import update_admissibility_manifest as updater


def _write(p: Path, text: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


def test_updater_refuses_to_enable_without_allow_flag(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Enabling gates must be an explicit action (Lean intent + --allow-enable)."""

    repo_root = tmp_path / "repo"

    # Minimal layout.
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

    # Lean intent: tries to enable CT01.
    _write(
        lean_src,
        """namespace ToeFormal\nnamespace Constraints\n\n/- BEGIN_ADMISSIBILITY_MANIFEST_JSON\n{\n  \"version\": 1,\n  \"gates\": {\n    \"CT01\": {\"enabled\": true},\n    \"SYM01\": {\"enabled\": false},\n    \"CAUS01\": {\"enabled\": false}\n  }\n}\nEND_ADMISSIBILITY_MANIFEST_JSON -/\n\nend Constraints\nend ToeFormal\n\nnamespace ToeFormal\nnamespace Gates\n\ndef defaultEnabled : List String := [\"CT01\"]\n\nend Gates\nend ToeFormal\n""",
    )

    # Gate stub files exist.
    for gate_id in ["CT01", "SYM01", "CAUS01"]:
        _write(gates_root / f"{gate_id}.lean", f"namespace ToeFormal.Gates\nopaque {gate_id} : Prop\nend ToeFormal.Gates\n")

    # Existing manifest starts disabled.
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

    # Configure policy to match Lean intent for this test scenario.
    monkeypatch.setattr(updater, "DEFAULT_ENABLED_GATES", ["CT01"], raising=False)

    # Without --allow-enable, updater must refuse to flip CT01 false→true.
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
        ]
    )
    assert rc != 0

    # Manifest remains unchanged (still disabled).
    obj = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert obj["gates"]["CT01"]["enabled"] is False

    # With --allow-enable, updater may flip CT01 to true.
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
        ]
    )
    assert rc2 == 0

    obj2 = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert obj2["gates"]["CT01"]["enabled"] is True


def test_lean_defaults_match_pinned_python_policy() -> None:
    """Guardrail: pinned Python policy must match Lean defaultEnabled intent."""

    assert updater.DEFAULT_ENABLED_GATES == []

    repo_root = Path(updater.REPO_ROOT)
    lean_src = repo_root / "formal" / "toe_formal" / "ToeFormal" / "Constraints" / "AD00_AdmissibilityManifest.lean"
    text = lean_src.read_text(encoding="utf-8", errors="replace")

    # Minimal deterministic check (no full Lean parsing): the stub policy must remain empty.
    assert "def defaultEnabled" in text
    assert ":= []" in text or ":=[]" in text
