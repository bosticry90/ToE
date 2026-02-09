"""Helper: pin external evidence metadata (sha256) deterministically.

Purpose
- Given one or more repo-relative file paths under formal/external_evidence/,
  compute sha256 and write a deterministic metadata JSON file.

Design constraints
- Deterministic output: no timestamps, no file mtimes, stable JSON key order.
- Minimal surface area: stdlib only.
"""

from __future__ import annotations

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
from pathlib import Path


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _assert_under_external_evidence(rel: str) -> None:
    norm = rel.replace("\\", "/")
    if not norm.startswith("formal/external_evidence/"):
        raise ValueError(
            "Refusing to hash files outside formal/external_evidence/. "
            f"Got: {rel}"
        )


def build_metadata(*, repo_root: Path, relpaths: list[str], schema: str) -> dict:
    items = []
    for rel in relpaths:
        _assert_under_external_evidence(rel)
        p = (repo_root / rel).resolve()
        if not p.exists():
            raise FileNotFoundError(f"Missing evidence file: {rel} (resolved: {p})")
        items.append(
            {
                "relpath": rel.replace("\\", "/"),
                "sha256": _sha256_file(p),
                "bytes": int(p.stat().st_size),
            }
        )

    items.sort(key=lambda d: str(d["relpath"]))

    return {
        "schema": str(schema),
        "items": items,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--out-relpath",
        required=True,
        help="Repo-relative path for metadata JSON output (must be under formal/external_evidence/)",
    )
    ap.add_argument(
        "--relpath",
        action="append",
        required=True,
        help="Repo-relative evidence file path to hash (repeatable). Must be under formal/external_evidence/.",
    )
    ap.add_argument(
        "--schema",
        default="external_evidence_metadata/v1",
        help="Schema string to embed in the metadata JSON.",
    )
    args = ap.parse_args()

    _assert_under_external_evidence(str(args.out_relpath))
    repo_root = _find_repo_root(Path(__file__))

    payload = build_metadata(repo_root=repo_root, relpaths=list(args.relpath), schema=str(args.schema))

    out = (repo_root / str(args.out_relpath)).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(out.as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
