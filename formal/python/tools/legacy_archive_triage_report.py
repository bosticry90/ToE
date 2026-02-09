from __future__ import annotations

"""Legacy archive triage report generator.

Goal
- Inventory and categorize legacy materials under selected `archive/` subtrees.
- Produce a deterministic, audit-friendly report without promoting epistemic status.

Outputs
- Writes a Markdown summary and a JSON payload under `formal/output/`.

Policy alignment
- This is bookkeeping only (no gate enablement changes, no locks created).
- Treats legacy content as conditionally admissible input pending revalidation.
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
import os
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Iterable


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


_TEXT_EXTS = {
    ".md",
    ".txt",
    ".py",
    ".lean",
    ".toml",
    ".yaml",
    ".yml",
    ".json",
    ".ini",
    ".cfg",
    ".csv",
    ".tex",
    ".rst",
}


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _rel(repo_root: Path, p: Path) -> str:
    try:
        return p.resolve().relative_to(repo_root.resolve()).as_posix()
    except Exception:
        return p.as_posix()


def _iter_files(root: Path) -> Iterable[Path]:
    # Deterministic traversal by path.
    if not root.exists():
        return
    paths: list[Path] = []
    for p in root.rglob("*"):
        parts_lower = {part.lower() for part in p.parts}
        if "__pycache__" in parts_lower or ".pytest_cache" in parts_lower:
            continue
        if p.is_file():
            if p.suffix.lower() in {".pyc", ".pyo"}:
                continue
            paths.append(p)
    for p in sorted(paths, key=lambda x: x.as_posix().lower()):
        yield p


def _guess_kind(relpath: str, suffix: str) -> str:
    rp = relpath.lower()
    s = suffix.lower()

    if "/tests/" in rp or rp.endswith("pytest_legacy.ini") or rp.endswith("pytest.ini"):
        return "tests"
    if s in {".py"}:
        return "python"
    if s in {".lean"}:
        return "lean"
    if s in {".toml", ".ini", ".cfg", ".yaml", ".yml", ".json"}:
        return "config"
    if s in {".md", ".txt", ".tex", ".rst"}:
        return "docs"
    if s in {".png", ".jpg", ".jpeg", ".gif", ".svg", ".pdf"}:
        return "evidence_media"
    if s in {".csv"}:
        return "data"
    return "other"


def _read_head_text(path: Path, *, max_bytes: int) -> str | None:
    try:
        raw = path.read_bytes()
    except Exception:
        return None
    if len(raw) > max_bytes:
        raw = raw[:max_bytes]
    try:
        return raw.decode("utf-8", errors="replace")
    except Exception:
        return None


def _signals_from_text(text: str) -> dict[str, bool]:
    t = text
    return {
        "has_inventory_id_field": "\nID:" in t or t.startswith("ID:"),
        "has_status_field": "\nStatus:" in t or t.startswith("Status:"),
        "mentions_external_evidence": "external_evidence" in t or "External evidence" in t,
        "mentions_lock": "formal/markdown/locks" in t or "locks/" in t,
        "mentions_gate": "CT-01" in t or "SYM-01" in t or "CAUS-01" in t,
        "mentions_empirical_anchor": "Empirically Anchored" in t,
    }


def _suggest_bucket(kind: str, signals: dict[str, bool], relpath: str) -> str:
    # Conservative default: keep as reference until explicitly revalidated.
    if kind in {"evidence_media", "data"}:
        return "candidate_reanchor" if signals.get("mentions_external_evidence") else "reference_only"

    if kind == "tests":
        return "candidate_revalidate"

    if kind in {"python", "lean"}:
        # Legacy code rarely drops in cleanly; prefer staged revalidation.
        return "candidate_revalidate"

    if kind == "config":
        # Old configs should not be applied; treat as reference unless explicitly ported.
        return "reference_only"

    if kind == "docs":
        # If the doc looks structured (inventory-like), stage for migration.
        if signals.get("has_inventory_id_field") or signals.get("has_status_field"):
            return "candidate_revalidate"
        if "state_of_the_theory" in relpath.lower():
            return "reference_only"
        return "reference_only"

    return "reference_only"


@dataclass(frozen=True)
class FileEntry:
    relpath: str
    size_bytes: int
    kind: str
    bucket: str
    sha256: str | None
    signals: dict[str, bool]


def build_triage(*, repo_root: Path, roots: list[Path], max_text_bytes: int, max_hash_bytes: int) -> dict[str, Any]:
    entries: list[FileEntry] = []

    for r in roots:
        for p in _iter_files(r):
            relpath = _rel(repo_root, p)
            suffix = p.suffix
            kind = _guess_kind(relpath, suffix)
            size = int(p.stat().st_size)

            text = None
            signals: dict[str, bool] = {
                "has_inventory_id_field": False,
                "has_status_field": False,
                "mentions_external_evidence": False,
                "mentions_lock": False,
                "mentions_gate": False,
                "mentions_empirical_anchor": False,
            }
            if suffix.lower() in _TEXT_EXTS and size > 0:
                text = _read_head_text(p, max_bytes=max_text_bytes)
                if isinstance(text, str):
                    signals = _signals_from_text(text)

            sha256: str | None = None
            # Hash only small-ish files by default to avoid long runtime on binaries.
            if size > 0 and size <= max_hash_bytes:
                try:
                    sha256 = _sha256_bytes(p.read_bytes())
                except Exception:
                    sha256 = None

            bucket = _suggest_bucket(kind, signals, relpath)
            entries.append(
                FileEntry(
                    relpath=relpath,
                    size_bytes=size,
                    kind=kind,
                    bucket=bucket,
                    sha256=sha256,
                    signals=signals,
                )
            )

    # Deterministic ordering.
    entries_sorted = sorted(entries, key=lambda e: e.relpath.lower())

    counts: dict[str, int] = {}
    for e in entries_sorted:
        counts[e.bucket] = counts.get(e.bucket, 0) + 1

    kinds: dict[str, int] = {}
    for e in entries_sorted:
        kinds[e.kind] = kinds.get(e.kind, 0) + 1

    total_bytes = sum(e.size_bytes for e in entries_sorted)

    payload = {
        "schema": "OV-LG-ARCHIVE-TRIAGE/v1",
        "generated_at": datetime.now().isoformat(timespec="seconds"),
        "repo_root": repo_root.as_posix(),
        "inputs": {
            "roots": [_rel(repo_root, r) for r in roots],
            "max_text_bytes": int(max_text_bytes),
            "max_hash_bytes": int(max_hash_bytes),
        },
        "summary": {
            "file_count": len(entries_sorted),
            "total_bytes": int(total_bytes),
            "bucket_counts": dict(sorted(counts.items())),
            "kind_counts": dict(sorted(kinds.items())),
        },
        "files": [
            {
                "relpath": e.relpath,
                "size_bytes": e.size_bytes,
                "kind": e.kind,
                "bucket": e.bucket,
                "sha256": e.sha256,
                "signals": dict(e.signals),
            }
            for e in entries_sorted
        ],
    }
    payload["fingerprint"] = _sha256_bytes(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    )

    return payload


def _fmt_bytes(n: int) -> str:
    x = float(n)
    for unit in ["B", "KB", "MB", "GB", "TB"]:
        if x < 1024.0 or unit == "TB":
            if unit == "B":
                return f"{int(x)}{unit}"
            return f"{x:.2f}{unit}"
        x /= 1024.0
    return f"{int(n)}B"


def render_markdown(payload: dict[str, Any]) -> str:
    s = payload["summary"]
    inputs = payload["inputs"]

    lines: list[str] = []
    lines.append("# Legacy archive triage (bookkeeping)")
    lines.append("")
    lines.append(f"Generated: {payload['generated_at']}")
    lines.append(f"Schema: {payload['schema']}")
    lines.append(f"Fingerprint: {payload['fingerprint']}")
    lines.append("")
    lines.append("Scope / limits")
    lines.append("- Bookkeeping-only inventory of archive materials; no epistemic promotion")
    lines.append("- Does not enable gates, does not create locks, does not assert external anchoring")
    lines.append("- Buckets are conservative suggestions for staged reincorporation")
    lines.append("")

    lines.append("Inputs")
    for r in inputs["roots"]:
        lines.append(f"- {r}")
    lines.append(f"- max_text_bytes: {inputs['max_text_bytes']}")
    lines.append(f"- max_hash_bytes: {inputs['max_hash_bytes']}")
    lines.append("")

    lines.append("Summary")
    lines.append(f"- file_count: {s['file_count']}")
    lines.append(f"- total_bytes: {s['total_bytes']} ({_fmt_bytes(int(s['total_bytes']))})")
    lines.append("")

    def _table(title: str, d: dict[str, int]) -> None:
        lines.append(title)
        lines.append("| Key | Count |")
        lines.append("| --- | ---: |")
        for k, v in sorted(d.items(), key=lambda kv: (-kv[1], kv[0])):
            lines.append(f"| {k} | {v} |")
        lines.append("")

    _table("Bucket counts", dict(s["bucket_counts"]))
    _table("Kind counts", dict(s["kind_counts"]))

    # Highlight a small, actionable shortlist.
    files = payload.get("files") or []
    if isinstance(files, list):
        candidates = [
            f
            for f in files
            if isinstance(f, dict)
            and f.get("bucket") in {"candidate_revalidate", "candidate_reanchor"}
            and isinstance(f.get("relpath"), str)
        ]
        candidates = sorted(candidates, key=lambda f: str(f.get("relpath")).lower())
        lines.append("Shortlist (candidate_revalidate / candidate_reanchor)")
        lines.append("| Path | Kind | Bucket | Size | Signals |")
        lines.append("| --- | --- | --- | ---: | --- |")
        for f in candidates[:40]:
            sig = f.get("signals") or {}
            sig_keys = []
            if isinstance(sig, dict):
                for k, v in sig.items():
                    if v is True:
                        sig_keys.append(str(k))
            sig_text = ",".join(sig_keys) if sig_keys else "-"
            lines.append(
                "| "
                + str(f.get("relpath"))
                + " | "
                + str(f.get("kind"))
                + " | "
                + str(f.get("bucket"))
                + " | "
                + str(f.get("size_bytes"))
                + " | "
                + sig_text
                + " |"
            )
        if len(candidates) > 40:
            lines.append("")
            lines.append(f"(Showing first 40 of {len(candidates)} candidates; see JSON for full list.)")
        lines.append("")

    lines.append("Next steps (recommended)")
    lines.append("- Pick 3–10 candidate_revalidate items and define explicit revalidation targets (tests, invariants, or migration plan)")
    lines.append("- For speculative/interpretive docs, keep reference_only unless you can attach an exit condition + a front-door audit")
    lines.append("- For legacy code, port by extraction into a new module with tests; do not import archive code directly into core")
    lines.append("")

    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="legacy_archive_triage_report")
    p.add_argument("--out-dir", default=None, help="Output directory (default: formal/output)")
    p.add_argument("--max-text-bytes", type=int, default=200_000)
    p.add_argument("--max-hash-bytes", type=int, default=2_000_000)
    p.add_argument(
        "--root",
        action="append",
        default=[],
        help="Archive subtree to include, repo-relative (repeatable). Default: common archive paths.",
    )

    args = p.parse_args(argv)

    repo_root = _find_repo_root(Path(__file__))

    default_roots = [
        "archive/docs",
        "archive/field_theory",
        "archive/fundamental_theory",
        "archive/lcrd_legacy_docs",
        "archive/legacy_configs",
        "archive/mei",
        "archive/tests",
    ]
    roots_rel = [str(x) for x in (args.root if args.root else default_roots)]
    roots = [repo_root / r for r in roots_rel]

    payload = build_triage(
        repo_root=repo_root,
        roots=roots,
        max_text_bytes=int(args.max_text_bytes),
        max_hash_bytes=int(args.max_hash_bytes),
    )

    out_dir = Path(args.out_dir).resolve() if args.out_dir else (repo_root / "formal" / "output")
    out_dir.mkdir(parents=True, exist_ok=True)

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    md_path = out_dir / f"legacy_archive_triage_{stamp}.md"
    json_path = out_dir / f"legacy_archive_triage_{stamp}.json"

    md_path.write_text(render_markdown(payload), encoding="utf-8", newline="\n")
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    print(str(md_path))
    print(str(json_path))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
