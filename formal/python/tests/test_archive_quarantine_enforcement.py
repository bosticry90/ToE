from __future__ import annotations

import configparser
import sys
from pathlib import Path

import pytest


def _repo_root_from_test_file(test_file: Path) -> Path:
    # test_file is .../ToE/formal/python/tests/test_*.py
    # parents: tests -> python -> formal -> ToE
    return test_file.resolve().parents[3]


def test_archive_is_not_importable() -> None:
    # `archive.py` at repo root intentionally blocks this import.
    with pytest.raises(ModuleNotFoundError):
        __import__("archive")


def test_sys_path_does_not_include_archive_dir() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    def norm(p: str) -> str:
        if p == "":
            pp = Path.cwd()
        else:
            pp = Path(p)
        try:
            resolved = pp.resolve(strict=False)
        except Exception:
            resolved = pp
        return str(resolved).replace("/", "\\").rstrip("\\").lower()

    root_norm = norm(str(repo_root))
    archive_norm = norm(str(repo_root / "archive"))
    normalized = [norm(p) for p in sys.path]

    # Invariant 1: repo root is present.
    assert root_norm in normalized

    # Invariant 2: no repo-root archive path is present anywhere.
    assert not any(p == archive_norm or p.startswith(archive_norm + "\\") for p in normalized)

    # Invariant 3: no repo-root archive subpath may appear before repo root.
    root_idx = normalized.index(root_norm)
    for idx, entry in enumerate(normalized[:root_idx]):
        if not entry.startswith(root_norm + "\\"):
            continue
        if "\\archive\\" in entry or entry.endswith("\\archive"):
            raise AssertionError(
                "Ordering invariant violated: repo-root archive path appears before repo root in sys.path"
            )


def test_no_init_py_under_archive_tree() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    archive_root = repo_root / "archive"

    # Keep archive non-packaged.
    # Full recursive scans can be slow in this repo, so enforce the strongest signals
    # (package roots) with bounded-depth checks.
    offenders: list[Path] = []

    direct = archive_root / "__init__.py"
    if direct.exists():
        offenders.append(direct.relative_to(repo_root))

    # If someone adds archive/ to sys.path, any shallow package roots become importable.
    for depth_glob in ("*/__init__.py", "*/*/__init__.py", "*/*/*/__init__.py"):
        for p in archive_root.glob(depth_glob):
            offenders.append(p.relative_to(repo_root))

    offenders = sorted(set(offenders))
    assert not offenders, "__init__.py found under archive quarantine:\n" + "\n".join(
        f"- {p.as_posix()}" for p in offenders
    )


def test_pytest_config_norecursedirs_includes_archive() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    cfg_path = repo_root / "pytest.ini"
    assert cfg_path.exists(), "Expected repo-root pytest.ini"

    cfg = configparser.ConfigParser()
    cfg.read(cfg_path, encoding="utf-8")
    assert cfg.has_section("pytest")

    # `norecursedirs` is multi-line; ConfigParser returns it as a single string.
    norecursedirs_raw = cfg.get("pytest", "norecursedirs", fallback="")
    toks = [t.strip() for t in norecursedirs_raw.splitlines() if t.strip()]
    assert "archive" in toks, "pytest.ini must include 'archive' in norecursedirs"


def test_tools_only_reference_archive_in_allowlisted_quarantine_tools() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    tools_root = repo_root / "formal" / "python" / "tools"

    allowlist = {
        tools_root / "legacy_archive_triage_report.py",
        tools_root / "archive_intake_index.py",
        tools_root / "archive_dossier_propose.py",
        tools_root / "crft_claims_extract.py",
        tools_root / "repo_hygiene_snapshot.py",
    }

    offenders: list[Path] = []

    for path in tools_root.rglob("*.py"):
        if path in allowlist:
            continue

        text = path.read_text(encoding="utf-8", errors="ignore")

        # Disallow hard-coded archive path references in non-quarantine tools.
        if "archive/" in text or "\\archive\\" in text:
            offenders.append(path.relative_to(repo_root))

    assert not offenders, "Non-quarantine tool references archive paths:\n" + "\n".join(
        f"- {p.as_posix()}" for p in offenders
    )
