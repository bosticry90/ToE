from __future__ import annotations

from pathlib import Path


def _repo_root_from_test_file(test_file: Path) -> Path:
    # test_file is .../ToE/formal/python/tests/test_*.py
    # parents: tests -> python -> formal -> ToE
    return test_file.resolve().parents[3]


def _should_skip_path(repo_root: Path, path: Path) -> bool:
    rel = path.relative_to(repo_root)
    parts = rel.parts

    if "__pycache__" in parts:
        return True

    # Quarantine/reference zones.
    if parts and parts[0] in {"archive", "scratch", "backup"}:
        return True

    return False


def test_single_canonical_python_acoustic_metric_surface() -> None:
    """Prevent accidental reintroduction of a second acoustic-metric surface.

    Canonical Python front door for MT-01a is:
      formal/python/crft/acoustic_metric.py

    Legacy reference implementation remains quarantined under archive/.
    """

    repo_root = _repo_root_from_test_file(Path(__file__))

    matches: list[Path] = []
    for path in repo_root.rglob("acoustic_metric.py"):
        if _should_skip_path(repo_root, path):
            continue
        matches.append(path)

    allowed = {repo_root / "formal" / "python" / "crft" / "acoustic_metric.py"}

    assert set(matches) == allowed, (
        "Unexpected acoustic_metric.py surface(s) outside quarantine. "
        "Keep a single canonical Python front door (MT-01a) at formal/python/crft/acoustic_metric.py.\n"
        + "Found:\n"
        + "\n".join(f"- {p.relative_to(repo_root)}" for p in sorted(matches))
    )
