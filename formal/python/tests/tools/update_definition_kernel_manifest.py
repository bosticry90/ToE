# C:\Users\psboy\Documents\ToE\formal\python\tests\tools\update_definition_kernel_manifest.py
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Dict, List


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))

TOEFORMAL_ROOT = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal"
MANIFEST_PATH = REPO_ROOT / "formal" / "markdown locks" / "dcr" / "definition_kernel_manifest.json"

KERNEL_PATTERNS = [
    re.compile(r".*/Definitions.*\.lean$", re.IGNORECASE),
    re.compile(r".*/LinearizedEquation\.lean$", re.IGNORECASE),
    re.compile(r".*/EQ[-_].*\.lean$", re.IGNORECASE),
]


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def list_kernel_files() -> List[Path]:
    if not TOEFORMAL_ROOT.exists():
        raise FileNotFoundError(f"ToeFormal root not found: {TOEFORMAL_ROOT}")
    files: List[Path] = []
    for p in TOEFORMAL_ROOT.rglob("*.lean"):
        rel = str(p.relative_to(REPO_ROOT)).replace("\\", "/")
        if any(pat.match(rel) for pat in KERNEL_PATTERNS):
            files.append(p)
    return files


def build_tracked() -> Dict[str, str]:
    tracked: Dict[str, str] = {}
    for p in list_kernel_files():
        rel = str(p.relative_to(REPO_ROOT)).replace("\\", "/")
        tracked[rel] = sha256_file(p)
    return dict(sorted(tracked.items()))


def main() -> None:
    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)

    tracked = build_tracked()
    manifest = {
        "version": 1,
        "root": "formal/toe_formal/ToeFormal",
        "tracked": tracked,
    }

    MANIFEST_PATH.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Updated manifest: {MANIFEST_PATH}")
    print(f"Tracked files: {len(tracked)}")


if __name__ == "__main__":
    main()
