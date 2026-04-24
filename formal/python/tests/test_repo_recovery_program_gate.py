from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import authority_surface_parity_check as authority_parity
from formal.python.tools import repo_recovery_baseline_report as recovery_baseline


REPO_ROOT = find_repo_root(Path(__file__))
ACTIVE_PYTHON_DIRS = [
    REPO_ROOT / "formal" / "python" / "tests",
    REPO_ROOT / "formal" / "python" / "tools",
    REPO_ROOT / "formal" / "python" / "research",
    REPO_ROOT / "formal" / "python" / "orchestration",
    REPO_ROOT / "formal" / "python" / "toe",
]


def test_find_repo_root_prefers_workspace_root_when_nested_formal_markers_exist(tmp_path: Path) -> None:
    repo_root = tmp_path / "repo"
    (repo_root / "formal" / "python").mkdir(parents=True)
    (repo_root / "State_of_the_Theory.md").write_text("authority\n", encoding="utf-8")
    nested_file = repo_root / "formal" / "formal" / "output" / "reports" / "marker.py"
    nested_file.parent.mkdir(parents=True)
    nested_file.write_text("pass\n", encoding="utf-8")

    assert find_repo_root(nested_file) == repo_root


def test_active_python_surfaces_use_shared_repo_root_helper() -> None:
    offending: list[str] = []
    for directory in ACTIVE_PYTHON_DIRS:
        for path in directory.rglob("*.py"):
            if "tests_quarantine" in path.parts:
                continue
            text = path.read_text(encoding="utf-8")
            if re.search(r"^def find_repo_root\(start: Path\)", text, flags=re.MULTILINE):
                offending.append(str(path.relative_to(REPO_ROOT)).replace("\\", "/"))
    assert not offending, "Active Python files still define inline find_repo_root helpers:\n- " + "\n- ".join(offending[:50])


def test_no_active_nested_formal_formal_files_remain() -> None:
    nested_root = REPO_ROOT / "formal" / "formal"
    files = [path for path in nested_root.rglob("*") if path.is_file()] if nested_root.exists() else []
    assert not files, "Active tracked files must not remain under formal/formal."


def test_roadmap_remediation_block_is_derived_from_state_surface() -> None:
    state_text = authority_parity.STATE_PATH.read_text(encoding="utf-8")
    roadmap_text = authority_parity.ROADMAP_PATH.read_text(encoding="utf-8")
    expected = authority_parity.generate_synced_roadmap_content(state_text, roadmap_text)
    assert roadmap_text == expected, "PHYSICS_ROADMAP remediation block drifted from State_of_the_Theory source."


def test_repo_recovery_baseline_matches_generator_output() -> None:
    payload = json.loads(recovery_baseline.DEFAULT_OUT_PATH.read_text(encoding="utf-8"))
    expected = recovery_baseline.build_report(
        captured_at_utc=payload.get("captured_at_utc"),
        lastfailed_snapshot=payload.get("branch_health_baseline", {}).get("lastfailed_snapshot"),
    )
    assert payload == expected, "Repo recovery baseline drifted from generator output."
