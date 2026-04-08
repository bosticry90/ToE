from __future__ import annotations

from pathlib import Path
import unicodedata


def find_repo_root(start: Path, *, marker_dir: str = "formal") -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / marker_dir).exists():
            return p
        p = p.parent
    raise RuntimeError(f"Could not locate repo root (expected a '{marker_dir}' directory).")


def normalize_sys_path_entry(entry: str) -> str:
    if entry == "":
        p = Path.cwd()
    else:
        p = Path(entry)

    try:
        resolved = p.resolve(strict=False)
    except Exception:
        resolved = p

    normalized = unicodedata.normalize("NFKC", str(resolved)).replace("/", "\\").rstrip("\\")
    if normalized.startswith("\\\\"):
        raise ValueError(f"UNC paths are not permitted in sys.path quarantine checks: {entry}")
    return normalized.lower()