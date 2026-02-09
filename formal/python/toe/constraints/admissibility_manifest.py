from __future__ import annotations

import json
import os
import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ENV_MANIFEST_PATH = "TOE_ADMISSIBILITY_MANIFEST"


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def default_manifest_path(repo_root: Path) -> Path:
    return repo_root / "formal" / "markdown locks" / "gates" / "admissibility_manifest.json"


@dataclass(frozen=True)
class GateCheckResult:
    blocked: bool
    reasons: list[str]
    manifest_path: str
    manifest_version: int | None
    manifest_sha256: str | None


def load_admissibility_manifest(*, repo_root: Path, manifest_path: Path | None = None) -> dict[str, Any]:
    if manifest_path is None:
        env_override = os.environ.get(ENV_MANIFEST_PATH)
        manifest_path = Path(env_override) if env_override else default_manifest_path(repo_root)

    if not manifest_path.exists():
        raise FileNotFoundError(f"Missing admissibility manifest: {manifest_path}")

    return json.loads(manifest_path.read_text(encoding="utf-8"))


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _to_stable_manifest_path(*, repo_root: Path, path: Path) -> str:
    """Return a stable repo-relative path when possible."""

    try:
        rel = path.resolve().relative_to(repo_root.resolve())
        return str(rel).replace("\\", "/")
    except Exception:
        return str(path)


def check_required_gates(
    *,
    repo_root: Path,
    required_gate_ids: Iterable[str],
    manifest: dict[str, Any] | None = None,
    manifest_path: Path | None = None,
) -> GateCheckResult:
    resolved_file: Path | None = None

    if manifest_path is not None:
        resolved_file = manifest_path
    else:
        env_override = os.environ.get(ENV_MANIFEST_PATH)
        resolved_file = Path(env_override) if env_override else default_manifest_path(repo_root)

    if manifest is None:
        manifest = load_admissibility_manifest(repo_root=repo_root, manifest_path=resolved_file)

    resolved_path = _to_stable_manifest_path(repo_root=repo_root, path=resolved_file)

    manifest_sha256: str | None = None
    try:
        if resolved_file is not None and resolved_file.exists():
            manifest_sha256 = _sha256_text(resolved_file.read_text(encoding="utf-8"))
    except Exception:
        manifest_sha256 = None

    reasons: list[str] = []
    gates = manifest.get("gates", {})
    for gate_id in required_gate_ids:
        g = gates.get(str(gate_id))
        if g is None:
            reasons.append(f"missing_gate:{gate_id}")
            continue
        enabled = bool(g.get("enabled", False))
        if not enabled:
            reasons.append(f"gate_disabled:{gate_id}")

    version = manifest.get("version")
    try:
        version_i = int(version) if version is not None else None
    except Exception:  # noqa: BLE001
        version_i = None

    return GateCheckResult(
        blocked=bool(reasons),
        reasons=reasons,
        manifest_path=resolved_path,
        manifest_version=version_i,
        manifest_sha256=manifest_sha256,
    )
