from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_GREEN_CACHE_STAMP_v0"

DEFAULT_KEY_FILES = [
    Path("formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"),
    Path("formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md"),
    Path("formal/docs/release/TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json"),
    Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"),
    Path("State_of_the_Theory.md"),
    Path("governance_suite.ps1"),
    Path("checkpoint_ladder.ps1"),
]


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _git_head_commit() -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return proc.stdout.strip()


def _compute_key_payload(extra_paths: list[str], status: str, captured_at_utc: str | None) -> dict[str, Any]:
    rel_paths = [str(path).replace("\\", "/") for path in DEFAULT_KEY_FILES]
    rel_paths.extend(str(Path(p)).replace("\\", "/") for p in extra_paths)

    # Stable order and dedup for deterministic keying.
    ordered_rel_paths = sorted(set(rel_paths))

    file_hashes: list[dict[str, str]] = []
    for rel_path in ordered_rel_paths:
        abs_path = REPO_ROOT / rel_path
        if not abs_path.exists():
            raise FileNotFoundError(f"Required key file not found: {rel_path}")
        digest = _sha256_bytes(abs_path.read_bytes())
        file_hashes.append({"path": rel_path, "sha256": digest})

    head_commit = _git_head_commit()
    key_material = {
        "head_commit": head_commit,
        "file_hashes": file_hashes,
    }
    cache_key = _sha256_bytes(json.dumps(key_material, sort_keys=True).encode("utf-8"))

    return {
        "schema_id": SCHEMA_ID,
        "status": status,
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "head_commit": head_commit,
        "cache_key": cache_key,
        "key_material": key_material,
        "non_claim_boundary": "This cache stamp is a repository-local execution optimization artifact and does not assert scientific adequacy.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Compute governance green-run cache key and optionally write stamp.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_green_cache_stamp_v0.json",
        help="Output path for cache stamp JSON (ignored with --print-key-only).",
    )
    parser.add_argument(
        "--status",
        default="GREEN",
        help="Status token to write into the stamp payload.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override.",
    )
    parser.add_argument(
        "--extra-path",
        action="append",
        default=[],
        help="Additional repository-relative path to include in key material (repeatable).",
    )
    parser.add_argument(
        "--print-key-only",
        action="store_true",
        help="Print only the cache key and do not write a stamp file.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    payload = _compute_key_payload(
        extra_paths=ns.extra_path,
        status=str(ns.status),
        captured_at_utc=ns.captured_at_utc,
    )

    if ns.print_key_only:
        print(payload["cache_key"])
        return 0

    out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "governance_cache_key: "
        f"status={payload['status']} "
        f"cache_key={payload['cache_key']} "
        f"out={out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
