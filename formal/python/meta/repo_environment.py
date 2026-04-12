from __future__ import annotations

from pathlib import Path
import unicodedata


def find_repo_root(start: Path, *, marker_dir: str = "formal") -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent

    candidates: list[Path] = []
    while p != p.parent:
        if (p / marker_dir).exists():
            candidates.append(p)
        p = p.parent

    # Prefer canonical workspace root when nested marker directories exist.
    for candidate in candidates:
        if (candidate / "formal" / "python").exists() and (candidate / "State_of_the_Theory.md").exists():
            return candidate

    if candidates:
        return candidates[-1]

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