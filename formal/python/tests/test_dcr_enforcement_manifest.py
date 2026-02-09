# C:\Users\psboy\Documents\ToE\formal\python\tests\test_dcr_enforcement_manifest.py
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Dict, List, Tuple


# ----------------------------
# Repo rooting (NO git needed)
# ----------------------------
def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))

TOEFORMAL_ROOT = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal"
DCR_DIR = REPO_ROOT / "formal" / "markdown locks" / "dcr"
MANIFEST_PATH = DCR_DIR / "definition_kernel_manifest.json"

# Adjust these patterns to match exactly what you define as "definition kernel"
KERNEL_PATTERNS = [
    re.compile(r".*/Definitions.*\.lean$", re.IGNORECASE),
    re.compile(r".*/LinearizedEquation\.lean$", re.IGNORECASE),
    re.compile(r".*/EQ[-_].*\.lean$", re.IGNORECASE),
]

DCR_FILE_RE = re.compile(r"^DCR_\d{8}_.+\.md$", re.IGNORECASE)


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def stable_manifest_hash(tracked: Dict[str, str]) -> str:
    # Stable hash over sorted entries
    items = sorted(tracked.items(), key=lambda kv: kv[0])
    h = hashlib.sha256()
    for k, v in items:
        h.update(k.encode("utf-8"))
        h.update(b"\0")
        h.update(v.encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()


def list_kernel_files() -> List[Path]:
    if not TOEFORMAL_ROOT.exists():
        return []
    files: List[Path] = []
    for p in TOEFORMAL_ROOT.rglob("*.lean"):
        rel = str(p.relative_to(REPO_ROOT)).replace("\\", "/")
        if any(pat.match(rel) for pat in KERNEL_PATTERNS):
            files.append(p)
    return files


def load_manifest() -> Dict:
    if not MANIFEST_PATH.exists():
        raise FileNotFoundError(f"Missing manifest: {MANIFEST_PATH}")
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def compute_current_hashes() -> Dict[str, str]:
    current: Dict[str, str] = {}
    for p in list_kernel_files():
        rel = str(p.relative_to(REPO_ROOT)).replace("\\", "/")
        current[rel] = sha256_file(p)
    return current


def newest_dcr_text() -> Tuple[Path | None, str]:
    if not DCR_DIR.exists():
        return None, ""
    dcrs = [p for p in DCR_DIR.iterdir() if p.is_file() and DCR_FILE_RE.match(p.name)]
    if not dcrs:
        return None, ""
    newest = max(dcrs, key=lambda p: p.stat().st_mtime)
    return newest, newest.read_text(encoding="utf-8", errors="replace")


def test_definition_kernel_manifest_exists_and_matches_current():
    assert DCR_DIR.exists(), f"Missing DCR directory: {DCR_DIR}"
    assert MANIFEST_PATH.exists(), f"Missing manifest: {MANIFEST_PATH}"

    manifest = load_manifest()
    tracked: Dict[str, str] = manifest.get("tracked", {})

    current = compute_current_hashes()

    missing_in_manifest = sorted([k for k in current.keys() if k not in tracked])
    extra_in_manifest = sorted([k for k in tracked.keys() if k not in current])
    differing = sorted([k for k in current.keys() if k in tracked and current[k] != tracked[k]])

    assert tracked == current, (
        "Definition-kernel drift detected.\n\n"
        "Your current ToeFormal kernel files do NOT match the manifest.\n"
        "To resolve (intentionally, with audit):\n"
        "  1) Run: python formal\\python\\tests\\tools\\update_definition_kernel_manifest.py\n"
        "  2) Create a new DCR file in: formal\\markdown locks\\dcr\\\n"
        "     Name format: DCR_YYYYMMDD_<slug>.md\n"
        "     Include line: Manifest-Hash: <hash>\n\n"
        "Mismatch details:\n"
        f"  Missing in manifest: {missing_in_manifest}\n"
        f"  Extra in manifest:   {extra_in_manifest}\n"
        f"  Differing hashes:    {differing}\n"
    )


def test_newest_dcr_references_current_manifest_hash():
    manifest = load_manifest()
    tracked: Dict[str, str] = manifest.get("tracked", {})
    current_hash = stable_manifest_hash(tracked)

    dcr_path, dcr_text = newest_dcr_text()
    assert dcr_path is not None, (
        "No DCR file found.\n"
        "Create one in formal\\markdown locks\\dcr\\ named:\n"
        "  DCR_YYYYMMDD_<slug>.md\n"
        f"And include:\n  Manifest-Hash: {current_hash}\n"
    )

    assert f"Manifest-Hash: {current_hash}" in dcr_text, (
        "Newest DCR does not reference the current manifest hash.\n"
        f"Newest DCR: {dcr_path}\n"
        f"Add this line:\n  Manifest-Hash: {current_hash}\n"
    )
