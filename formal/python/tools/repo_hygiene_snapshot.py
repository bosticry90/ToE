"""Manifest-based hygiene tooling (no git required).

Manual invocation (durability): run via the repo venv (recommended: `.\\py.ps1 -m formal.python.tools.repo_hygiene_snapshot ...`).
Avoid calling `python -m ...` directly, which can accidentally use system Python.

Subcommands:
- snapshot: write deterministic JSONL inventory of files (path + sha256 + bytes + mtime)
- diff: compare two snapshots (NEW / MODIFIED / MISSING)
- quarantine: move non-allowlisted files into scratch/quarantine/YYYYMMDD/<original_path>

Designed to be safe by default: quarantine uses --dry-run unless --apply is provided.
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
import os
import re
import shutil
from dataclasses import dataclass
from datetime import datetime, timezone
from fnmatch import fnmatch
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple


@dataclass(frozen=True)
class SnapshotRow:
    path: str
    sha256: str
    bytes: int
    mtime: str
    mtime_ns: int
    mode: str  # "full" | "fast"


DEFAULT_ALLOWLIST: Tuple[str, ...] = (
    # Canonical docs
    "State_of_the_Theory.md",
    "README*.md",
    "*.md",
    "*.txt",
    "*.toml",
    "*.ini",
    "requirements*.txt",
    # Canonical formal area
    "formal/**",
    # Optional scratch space (quarantine lives here)
    "scratch/**",
)

# Explicit bucket for fixtures loaded by tests via direct filesystem paths.
# Keeping this separate makes the policy intent clear ("kept because tests load it").
FIXTURE_ALLOWLIST: Tuple[str, ...] = (
    "archive/fundamental_theory/**",
)

DEFAULT_IGNORE: Tuple[str, ...] = (
    # Python caches
    "**/__pycache__/**",
    "**/.pytest_cache/**",
    ".pytest_cache/**",
    "**/*.pyc",
    "**/*.pyo",
    # Any embedded git repos (including historic archive bundles)
    "**/.git/**",
    "archive/.git/**",
    # Treat archive as non-canonical working set (fixtures are re-included explicitly)
    "archive/**",
    # Virtual envs
    ".venv/**",
    "venv/**",
    # Legacy embedded venvs in archived material
    "archive/.venv/**",
    "archive/venv/**",
    # Editor / temp
    "**/*~",
    "**/*.swp",
    "**/*.swo",
    "**/.DS_Store",
    "**/Thumbs.db",
    "**/*.tmp",
    # Don’t let tool outputs destabilize snapshots
    "backup/**",
    "formal/tooling_snapshots/**",
)


PROFILE_SANITY_DIFF_IGNORE: Tuple[str, ...] = (
    # Lean / lake build outputs (high churn)
    "**/.lake/**",
    # Common caches
    "**/__pycache__/**",
    "**/*.pyc",
    "**/.pytest_cache/**",
    # Editor / temp
    "**/*.log",
    "**/*.tmp",
    "**/*.out",
    "**/*.aux",
    "**/*.synctex.gz",
    # Scratch workspace (including quarantine)
    "scratch/**",
)


def _repo_root_from_this_file() -> Path:
    # .../formal/python/tools/repo_hygiene_snapshot.py -> repo root is parents[3]
    return Path(__file__).resolve().parents[3]


def _posix_relpath(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def _utc_iso_from_mtime(mtime_seconds: float) -> str:
    return datetime.fromtimestamp(mtime_seconds, tz=timezone.utc).isoformat().replace("+00:00", "Z")


def _atomic_replace(src: Path, dst: Path) -> None:
    # Atomic on Windows when src/dst are on same volume.
    os.replace(str(src), str(dst))


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _compile_globs(patterns: Sequence[str]) -> Tuple[str, ...]:
    # Normalize to POSIX-style globs and expand a few common "globstar" idioms.
    # NOTE: fnmatch() does not treat "**/" as "optional prefix", so we add both
    # variants to make patterns like "**/.pytest_cache/**" match top-level too.
    out: List[str] = []
    for raw in patterns:
        p = raw.replace("\\", "/")
        out.append(p)
        if p.startswith("**/"):
            out.append(p[len("**/") :])
    # Deduplicate while preserving order.
    seen: Set[str] = set()
    deduped: List[str] = []
    for p in out:
        if p in seen:
            continue
        seen.add(p)
        deduped.append(p)
    return tuple(deduped)


# Precompile default policy globs for hot paths.
_DEFAULT_IGNORE_COMPILED: Tuple[str, ...] = _compile_globs(DEFAULT_IGNORE)
_FIXTURE_ALLOWLIST_COMPILED: Tuple[str, ...] = _compile_globs(FIXTURE_ALLOWLIST)


def _matches_any(path_posix: str, patterns: Sequence[str]) -> bool:
    return any(fnmatch(path_posix, pat) for pat in patterns)


def _literal_prefix_before_wildcard(glob_pat: str) -> str:
    for i, ch in enumerate(glob_pat):
        if ch in "*?[":
            return glob_pat[:i]
    return glob_pat


def _has_included_descendant(dir_rel_posix: str, include_globs: Sequence[str]) -> bool:
    """Conservative hint: avoid pruning a dir if an include glob lives under it."""
    dir_rel_posix = dir_rel_posix.rstrip("/")
    if not dir_rel_posix:
        return True
    needle = dir_rel_posix.replace("\\", "/") + "/"
    for raw in include_globs:
        pat = raw.replace("\\", "/")
        prefix = _literal_prefix_before_wildcard(pat)
        if prefix.startswith(needle):
            return True
    return False


def _should_ignore(path_posix: str, *, ignore_globs: Sequence[str], include_globs: Sequence[str]) -> bool:
    path_posix = path_posix.replace("\\", "/")
    if _matches_any(path_posix, include_globs):
        return False
    return _matches_any(path_posix, ignore_globs)


def is_ignored_by_default(path_posix: str) -> bool:
    """Policy predicate used for tests and reasoning about DEFAULT_IGNORE + fixture override."""
    return _should_ignore(path_posix, ignore_globs=_DEFAULT_IGNORE_COMPILED, include_globs=_FIXTURE_ALLOWLIST_COMPILED)


def iter_repo_files(root: Path, ignore_globs: Sequence[str]) -> Iterator[Path]:
    ignore_globs = _compile_globs(ignore_globs)
    include_globs = _compile_globs(FIXTURE_ALLOWLIST)

    # Walk deterministically.
    for dirpath, dirnames, filenames in os.walk(root):
        dirpath_p = Path(dirpath)
        rel_dir = "" if dirpath_p == root else _posix_relpath(dirpath_p, root)

        # Prune ignored directories early.
        pruned: List[str] = []
        for d in list(dirnames):
            rel = f"{rel_dir}/{d}" if rel_dir else d
            if (
                _should_ignore(rel + "/", ignore_globs=ignore_globs, include_globs=include_globs)
                or _should_ignore(rel + "/**", ignore_globs=ignore_globs, include_globs=include_globs)
                or _should_ignore(rel, ignore_globs=ignore_globs, include_globs=include_globs)
            ) and not _has_included_descendant(rel, include_globs):
                pruned.append(d)
                dirnames.remove(d)
        # filenames filtered below.

        for name in sorted(filenames):
            p = dirpath_p / name
            try:
                rel = _posix_relpath(p, root)
            except ValueError:
                continue
            if _should_ignore(rel, ignore_globs=ignore_globs, include_globs=include_globs):
                continue
            yield p


def write_snapshot(
    *,
    root: Path,
    out_path: Path,
    ignore_globs: Sequence[str],
    include_hash: bool,
    mode: str,
    progress_every: int = 0,
) -> int:
    """Writes a snapshot JSONL to out_path. Caller decides atomicity."""
    out_path.parent.mkdir(parents=True, exist_ok=True)

    rows: List[SnapshotRow] = []
    scanned = 0
    for p in iter_repo_files(root, ignore_globs=ignore_globs):
        scanned += 1
        if progress_every and (scanned % int(progress_every) == 0):
            print(f"SNAPSHOT_PROGRESS {scanned}")
        st = p.stat()
        sha = _sha256_file(p) if include_hash else ""
        rows.append(
            SnapshotRow(
                path=_posix_relpath(p, root),
                sha256=sha,
                bytes=int(st.st_size),
                mtime=_utc_iso_from_mtime(st.st_mtime),
                mtime_ns=int(getattr(st, "st_mtime_ns", int(st.st_mtime * 1e9))),
                mode=mode,
            )
        )

    rows.sort(key=lambda r: r.path)

    with out_path.open("w", encoding="utf-8", newline="\n") as f:
        for r in rows:
            f.write(
                json.dumps(
                    {
                        "path": r.path,
                        "sha256": r.sha256,
                        "bytes": r.bytes,
                        "mtime": r.mtime,
                        "mtime_ns": r.mtime_ns,
                        "mode": r.mode,
                    },
                    sort_keys=True,
                    ensure_ascii=False,
                )
                + "\n"
            )

    return len(rows)


def write_snapshot_atomic(
    *,
    root: Path,
    out_path: Path,
    ignore_globs: Sequence[str],
    include_hash: bool,
    mode: str,
    progress_every: int = 0,
) -> int:
    """Atomic snapshot write: writes to <out>.tmp then renames on success.

    On interrupt/exception, attempts to delete the temp file.
    """
    tmp_path = out_path.with_suffix(out_path.suffix + ".tmp")
    try:
        count = write_snapshot(
            root=root,
            out_path=tmp_path,
            ignore_globs=ignore_globs,
            include_hash=include_hash,
            mode=mode,
            progress_every=progress_every,
        )
        _atomic_replace(tmp_path, out_path)
        return count
    except BaseException:
        try:
            if tmp_path.exists():
                tmp_path.unlink()
        except Exception:
            pass
        raise


def read_snapshot(path: Path) -> Dict[str, SnapshotRow]:
    out: Dict[str, SnapshotRow] = {}
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            mode = str(obj.get("mode") or ("full" if obj.get("sha256") else "fast"))
            raw_mtime_ns = obj.get("mtime_ns")
            mtime_ns = int(raw_mtime_ns) if raw_mtime_ns is not None else 0
            if not mtime_ns:
                parsed_ns = _mtime_iso_to_ns(str(obj.get("mtime") or ""))
                if parsed_ns is not None:
                    # Snap to millisecond boundary for stability across platforms.
                    mtime_ns = int((parsed_ns // 1_000_000) * 1_000_000)
            out[obj["path"]] = SnapshotRow(
                path=obj["path"],
                sha256=str(obj.get("sha256") or ""),
                bytes=int(obj["bytes"]),
                mtime=str(obj["mtime"]),
                mtime_ns=mtime_ns,
                mode=mode,
            )
    return out


def _mtime_iso_to_ns(mtime_iso: str) -> Optional[int]:
    try:
        s = mtime_iso.strip()
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        dt = datetime.fromisoformat(s)
        return int(dt.timestamp() * 1e9)
    except Exception:
        return None


def _row_mtime_ms(r: SnapshotRow) -> int:
    """Comparable mtime for diffing.

    On Windows, st_mtime_ns often has sub-microsecond granularity (e.g. 100ns).
    Older snapshots store ISO timestamps derived from float seconds, which are
    rounded and can differ by <1µs from the true ns value. Milliseconds avoids
    those false positives while remaining a good sanity signal.
    """
    if r.mtime_ns:
        return int(r.mtime_ns // 1_000_000)
    parsed = _mtime_iso_to_ns(r.mtime)
    return int((parsed or 0) // 1_000_000)


def _row_sig_fast(r: SnapshotRow) -> Tuple[int, int]:
    return (r.bytes, _row_mtime_ms(r))


def _rows_equivalent_fallback(b: SnapshotRow, c: SnapshotRow, *, mtime_ms_tolerance: int = 2) -> bool:
    # Treat small mtime jitter as equal (Windows rounding, FAT/exFAT, toolchains touching mtimes, etc).
    if b.bytes != c.bytes:
        return False
    return abs(_row_mtime_ms(b) - _row_mtime_ms(c)) <= int(mtime_ms_tolerance)


def diff_snapshots(baseline: Dict[str, SnapshotRow], current: Dict[str, SnapshotRow]) -> Tuple[List[str], List[str], List[str]]:
    b_paths = set(baseline.keys())
    c_paths = set(current.keys())

    new = sorted(c_paths - b_paths)
    missing = sorted(b_paths - c_paths)

    modified: List[str] = []
    for p in sorted(b_paths & c_paths):
        b = baseline[p]
        c = current[p]
        both_full = (b.mode == "full" and c.mode == "full" and b.sha256 and c.sha256)
        if both_full:
            if b.sha256 != c.sha256:
                modified.append(p)
        else:
            if not _rows_equivalent_fallback(b, c):
                modified.append(p)

    return new, modified, missing


def _filter_snapshot_rows(rows: Dict[str, SnapshotRow], ignore_globs: Sequence[str]) -> Dict[str, SnapshotRow]:
    ignore_globs = _compile_globs(ignore_globs)
    if not ignore_globs:
        return rows
    return {p: r for p, r in rows.items() if not _matches_any(p, ignore_globs)}


def _emit_list(label: str, paths: Sequence[str], *, max_list: int) -> None:
    if max_list <= 0:
        return
    for p in paths[: min(max_list, len(paths))]:
        print(f"{label} {p}")
    if len(paths) > max_list:
        print(f"{label} ... ({len(paths) - max_list} more)")


_LINK_RE = re.compile(r"\]\(([^)]+)\)")
_IMG_RE = re.compile(r"!\[[^\]]*\]\(([^)]+)\)")


def _unescape_markdown_path(s: str) -> str:
    # Handle the common escapes used in this repo's evidence paths (e.g. toe\_formal).
    return s.replace("\\_", "_")


def referenced_paths_from_state_theory(root: Path) -> Set[str]:
    state = root / "State_of_the_Theory.md"
    if not state.exists():
        return set()

    text = state.read_text(encoding="utf-8", errors="ignore")
    candidates: Set[str] = set()

    for rx in (_IMG_RE, _LINK_RE):
        for m in rx.finditer(text):
            raw = m.group(1).strip()
            if not raw or "://" in raw:
                continue
            raw = raw.split("#", 1)[0].split("?", 1)[0].strip()
            if not raw:
                continue
            # Normalize
            raw = _unescape_markdown_path(raw).replace("\\", "/")
            # Ignore mailto, anchors
            if raw.startswith("mailto:"):
                continue
            # Remove surrounding <...> if present
            raw = raw.strip("<>")
            candidates.add(raw)

    # Also capture plain-text evidence file paths, which are typically semicolon-separated.
    # Example: "Evidence: archive/tests/test_ucff_core_symbolic.py; formal/python/..."
    for line in text.splitlines():
        if not line.startswith("Evidence:"):
            continue
        rhs = line[len("Evidence:") :]
        for part in rhs.split(";"):
            token = _unescape_markdown_path(part.strip())
            if not token:
                continue
            token = token.replace("\\", "/")
            # Heuristic: treat as a file/dir path only if it looks like one.
            if "/" not in token and "\\" not in token:
                continue
            # Strip stray trailing punctuation.
            token = token.strip().strip(",")
            # Remove markdown emphasis/backticks if present.
            token = token.strip("`*")
            candidates.add(token)

    allowed: Set[str] = set()
    for rel in candidates:
        rel = rel.strip()
        if not rel:
            continue
        p = (root / rel).resolve()
        try:
            p.relative_to(root.resolve())
        except Exception:
            continue
        if p.is_file():
            allowed.add(_posix_relpath(p, root))
        elif p.is_dir():
            allowed.add(_posix_relpath(p, root) + "/**")

    return allowed


def _is_allowlisted(
    path_posix: str,
    *,
    allow_globs: Sequence[str],
    fixture_globs: Sequence[str],
    extra_allow: Sequence[str],
) -> bool:
    allow_globs = _compile_globs(tuple(allow_globs) + tuple(fixture_globs) + tuple(extra_allow))
    return _matches_any(path_posix, allow_globs)


def is_fixture_path(path_posix: str) -> bool:
    """Returns True if `path_posix` is covered by the fixture allowlist bucket."""
    return _matches_any(path_posix.replace("\\", "/"), _compile_globs(FIXTURE_ALLOWLIST))


def quarantine_candidates(
    root: Path,
    snapshot_current: Dict[str, SnapshotRow],
    *,
    allow_globs: Sequence[str],
    ignore_globs: Sequence[str],
    mode: str,
    snapshot_baseline: Optional[Dict[str, SnapshotRow]] = None,
) -> List[str]:
    ignore_globs = _compile_globs(ignore_globs)
    include_globs = _compile_globs(FIXTURE_ALLOWLIST)

    extra_allow = sorted(referenced_paths_from_state_theory(root))

    candidates: List[str]
    if mode == "all":
        candidates = sorted(snapshot_current.keys())
    elif mode == "changed":
        if snapshot_baseline is None:
            raise ValueError("changed mode requires a baseline snapshot")
        new, modified, _missing = diff_snapshots(snapshot_baseline, snapshot_current)
        candidates = sorted(set(new) | set(modified))
    else:
        raise ValueError(f"Unknown mode: {mode}")

    to_quarantine: List[str] = []
    for rel in candidates:
        # Don’t quarantine ignored stuff.
        if _should_ignore(rel, ignore_globs=ignore_globs, include_globs=include_globs):
            continue
        # Don’t quarantine allowlisted stuff.
        if _is_allowlisted(rel, allow_globs=allow_globs, fixture_globs=FIXTURE_ALLOWLIST, extra_allow=extra_allow):
            continue
        to_quarantine.append(rel)

    return to_quarantine


def perform_quarantine(
    root: Path,
    rel_paths: Sequence[str],
    *,
    quarantine_root: Path,
    dry_run: bool,
) -> None:
    for rel in rel_paths:
        src = root / Path(rel)
        dst = quarantine_root / Path(rel)
        if not src.exists():
            continue
        if dry_run:
            continue
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(src), str(dst))


def latest_snapshot_file(snapshots_dir: Path) -> Optional[Path]:
    if not snapshots_dir.exists():
        return None
    snaps = sorted(snapshots_dir.glob("repo_snapshot_*.jsonl"))
    return snaps[-1] if snaps else None


def cmd_snapshot(args: argparse.Namespace) -> int:
    root = Path(args.root).resolve()
    out = Path(args.out).resolve() if args.out else None

    if out is None:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        out = root / "formal" / "tooling_snapshots" / f"repo_snapshot_{ts}.jsonl"

    use_fast = bool(getattr(args, "fast", False) or getattr(args, "fast_metadata_only", False))
    include_hash = not use_fast
    mode = "fast" if not include_hash else "full"

    count = write_snapshot_atomic(
        root=root,
        out_path=out,
        ignore_globs=args.ignore,
        include_hash=include_hash,
        mode=mode,
        progress_every=int(getattr(args, "progress_every", 0) or 0),
    )
    print(str(out))
    print(f"SNAPSHOT_FILES {count}")
    return 0


def cmd_diff(args: argparse.Namespace) -> int:
    baseline_path = args.baseline if getattr(args, "baseline", None) else getattr(args, "baseline_pos", None)
    current_path = args.current if getattr(args, "current", None) else getattr(args, "current_pos", None)
    if not baseline_path or not current_path:
        raise SystemExit("diff requires --baseline/--current or two positional snapshot paths")

    baseline = read_snapshot(Path(baseline_path))
    current = read_snapshot(Path(current_path))

    # Optional ignore filter applied at diff-time (useful for ignoring quarantine noise).
    diff_ignore: List[str] = list(getattr(args, "diff_ignore", []) or [])
    profile = str(getattr(args, "profile", "") or "").strip().lower()
    if profile in ("sanity", "clean"):
        diff_ignore.extend(PROFILE_SANITY_DIFF_IGNORE)
    if getattr(args, "ignore_quarantine", False):
        diff_ignore.append("scratch/quarantine/**")

    baseline = _filter_snapshot_rows(baseline, diff_ignore)
    current = _filter_snapshot_rows(current, diff_ignore)

    new, modified, missing = diff_snapshots(baseline, current)

    max_list = int(getattr(args, "max_list", 50))

    print(f"COUNTS new={len(new)} modified={len(modified)} missing={len(missing)}")
    _emit_list("NEW", new, max_list=max_list)
    _emit_list("MODIFIED", modified, max_list=max_list)
    _emit_list("MISSING", missing, max_list=max_list)

    out_path = getattr(args, "out", None)
    if out_path:
        out_p = Path(out_path)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        with out_p.open("w", encoding="utf-8", newline="\n") as f:
            for p in new:
                f.write(f"NEW {p}\n")
            for p in modified:
                f.write(f"MODIFIED {p}\n")
            for p in missing:
                f.write(f"MISSING {p}\n")
            f.write(f"COUNTS new={len(new)} modified={len(modified)} missing={len(missing)}\n")
        print(str(out_p))
    return 0


def cmd_quarantine(args: argparse.Namespace) -> int:
    root = Path(args.root).resolve()
    today = datetime.now().strftime("%Y%m%d")
    quarantine_root = (root / "scratch" / "quarantine" / today).resolve()

    snapshots_dir = root / "formal" / "tooling_snapshots"
    snapshots_dir.mkdir(parents=True, exist_ok=True)

    current_path = Path(args.current).resolve() if args.current else None
    baseline_path = Path(args.baseline).resolve() if args.baseline else None

    if current_path is None:
        # Generate a current snapshot on the fly.
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        current_path = snapshots_dir / f"repo_snapshot_{ts}.jsonl"
        write_snapshot_atomic(
            root=root,
            out_path=current_path,
            ignore_globs=args.ignore,
            include_hash=True,
            mode="full",
        )

    current = read_snapshot(current_path)

    baseline: Optional[Dict[str, SnapshotRow]] = None
    if args.mode == "changed":
        if baseline_path is None:
            latest = latest_snapshot_file(snapshots_dir)
            if latest is None:
                raise SystemExit("No baseline snapshot found; provide --baseline or create one with snapshot")
            baseline_path = latest
        baseline = read_snapshot(baseline_path)

    to_q = quarantine_candidates(
        root,
        current,
        allow_globs=args.allow,
        ignore_globs=args.ignore,
        mode=args.mode,
        snapshot_baseline=baseline,
    )

    # Summary
    print(f"QUARANTINE_ROOT {quarantine_root.as_posix()}")
    print(f"CANDIDATES {len(to_q)}")
    for p in to_q[: min(50, len(to_q))]:
        print(f"MOVE {p}")
    if len(to_q) > 50:
        print(f"... ({len(to_q) - 50} more)")

    dry_run = not args.apply
    if dry_run:
        print("DRY_RUN (pass --apply to move files)")
        return 0

    quarantine_root.mkdir(parents=True, exist_ok=True)
    perform_quarantine(root, to_q, quarantine_root=quarantine_root, dry_run=False)
    print(f"MOVED {len(to_q)}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="repo_hygiene_snapshot")
    sub = p.add_subparsers(dest="cmd", required=True)

    ps = sub.add_parser("snapshot", help="Write a deterministic repo snapshot JSONL")
    ps.add_argument("--root", default=str(_repo_root_from_this_file()))
    ps.add_argument("--out", default=None)
    ps.add_argument(
        "--fast",
        action="store_true",
        help="Fast snapshot: record bytes+mtime only (no sha256 hashing)",
    )
    ps.add_argument(
        "--fast-metadata-only",
        action="store_true",
        help="Alias for --fast (non-authoritative): record bytes+mtime only (no sha256 hashing)",
    )
    ps.add_argument(
        "--progress-every",
        type=int,
        default=0,
        help="Emit SNAPSHOT_PROGRESS every N files scanned (0 disables)",
    )
    ps.add_argument("--ignore", action="append", default=list(DEFAULT_IGNORE))
    ps.set_defaults(func=cmd_snapshot)

    pd = sub.add_parser("diff", help="Diff two snapshot JSONLs")
    # Support both: (a) old positional form, (b) explicit flag form.
    pd.add_argument("--baseline", default=None)
    pd.add_argument("--current", default=None)
    pd.add_argument(
        "--profile",
        choices=("sanity", "clean"),
        default=None,
        help="Preset diff ignore rules (e.g. ignore .lake/** and other churn)",
    )
    pd.add_argument("--diff-ignore", action="append", default=[], help="Glob(s) to ignore during diff")
    pd.add_argument("--ignore-quarantine", action="store_true", help="Ignore scratch/quarantine/** during diff")
    pd.add_argument("--max-list", type=int, default=50, help="Max entries per category to print")
    pd.add_argument("--out", default=None, help="Write full diff output to this file")
    pd.add_argument("baseline_pos", nargs="?", default=None)
    pd.add_argument("current_pos", nargs="?", default=None)
    pd.set_defaults(func=cmd_diff)

    pq = sub.add_parser("quarantine", help="Move non-allowlisted files to scratch/quarantine/YYYYMMDD/")
    pq.add_argument("--root", default=str(_repo_root_from_this_file()))
    pq.add_argument("--mode", choices=("all", "changed"), default="all")
    pq.add_argument("--baseline", default=None)
    pq.add_argument("--current", default=None)
    pq.add_argument("--allow", action="append", default=list(DEFAULT_ALLOWLIST))
    pq.add_argument("--ignore", action="append", default=list(DEFAULT_IGNORE))
    pq.add_argument("--apply", action="store_true", help="Actually move files (default is dry-run)")
    pq.set_defaults(func=cmd_quarantine)

    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
