from __future__ import annotations

"""CRFT surface feasibility scan (quarantine-safe).

Goal
- Before generating validation tickets for a CRFT claim family (e.g., C8 turbulence diagnostics),
  determine whether a canonical, non-archive Python front door exists.

Policy alignment
- Read-only: scans the repo working tree.
- Does not import from the archive directory.
- Output is bookkeeping only (no status upgrades).

Output schema (v1)
{
  "schema_version": 1,
  "surface": {"token": "C8", "label": "CRFT turbulence diagnostics"},
  "found": false,
  "canonical_front_doors": [
    {"path": "formal/python/crft/<...>.py", "reason": "keyword_match"}
  ],
  "related_non_crft_surfaces": [
    {"path": "formal/python/toe/observables/<...>.py", "reason": "keyword_match"}
  ],
  "prerequisite": "..."
}
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _iter_py_files(root: Path) -> Iterable[Path]:
    # Deterministic traversal order.
    for path in sorted(root.rglob("*.py"), key=lambda x: x.as_posix()):
        yield path


def _read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8", errors="ignore")


@dataclass(frozen=True)
class Hit:
    path: str
    reason: str


def scan_crft_surface_feasibility(repo_root: Path, token: str) -> dict:
    token = str(token).strip().upper()

    # Current scope: the only surface we actively gate here is C8.
    label = {
        "C8": "CRFT turbulence diagnostics",
    }.get(token, f"CRFT surface token {token}")

    crft_root = repo_root / "formal" / "python" / "crft"
    toe_obs_root = repo_root / "formal" / "python" / "toe" / "observables"

    # Keyword set based on the C8 spec excerpt.
    # To avoid false positives from generic spectral/FFT usage in unrelated CRFT modules,
    # we treat turbulence/taxonomy terms as required signals for C8 front-door discovery.
    required_re = re.compile(r"\b(turbulence|taxonomy)\b", flags=re.IGNORECASE)
    optional_re = re.compile(r"\b(Ephi|Eρ|Erho|Eu|spectrum)\b", flags=re.IGNORECASE)

    canonical_hits: List[Hit] = []
    related_hits: List[Hit] = []

    if token == "C8":
        if crft_root.exists():
            for p in _iter_py_files(crft_root):
                text = _read_text(p)
                if required_re.search(text) is not None and (optional_re.search(text) is not None):
                    canonical_hits.append(Hit(path=p.as_posix(), reason="keyword_match"))

        # Related (non-CRFT) surfaces can be useful, but do not count as a CRFT front door.
        if toe_obs_root.exists():
            for p in _iter_py_files(toe_obs_root):
                text = _read_text(p)
                if required_re.search(text) is not None:
                    related_hits.append(Hit(path=p.as_posix(), reason="keyword_match"))

    def rel(p: Path) -> str:
        try:
            return p.resolve().relative_to(repo_root.resolve()).as_posix()
        except Exception:
            return p.as_posix()

    canonical_front_doors = [
        {"path": rel(Path(h.path)), "sha256": _sha256_path(repo_root / rel(Path(h.path))), "reason": h.reason}
        for h in canonical_hits
        if (repo_root / rel(Path(h.path))).exists()
    ]
    related_non_crft = [
        {"path": rel(Path(h.path)), "sha256": _sha256_path(repo_root / rel(Path(h.path))), "reason": h.reason}
        for h in related_hits
        if (repo_root / rel(Path(h.path))).exists()
    ]

    found = len(canonical_front_doors) > 0

    prerequisite = ""
    if token == "C8" and not found:
        prerequisite = (
            "No canonical non-archive CRFT turbulence diagnostic front door found. "
            "Prerequisite: intentionally introduce a CRFT turbulence diagnostics front door (non-archive) "
            "with typed inputs + deterministic outputs and then generate bounded tickets."
        )

    return {
        "schema_version": 1,
        "surface": {"token": token, "label": label},
        "found": found,
        "canonical_front_doors": canonical_front_doors,
        "related_non_crft_surfaces": related_non_crft,
        "prerequisite": prerequisite,
    }


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Deterministic feasibility scan for CRFT surface front doors.")
    parser.add_argument("--token", required=True, help="Surface token, e.g. C8")
    parser.add_argument("--out", required=True, help="Repo-relative output JSON path")

    args = parser.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = scan_crft_surface_feasibility(repo_root=repo_root, token=args.token)

    out_path = repo_root / args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(str(Path(args.out).as_posix()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
