"""Custody manifests for the narrow canonical-text attribute repair."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
ATTRIBUTES_PATH = REPO_ROOT / ".gitattributes"
PRECHANGE_PATH = (
    REPO_ROOT
    / "formal"
    / "custody"
    / "canonical_text"
    / "CANONICAL_TEXT_ATTRIBUTE_REPAIR_PRECHANGE_CUSTODY_20260729_v0.json"
)
POSTCHANGE_PATH = (
    REPO_ROOT
    / "formal"
    / "custody"
    / "canonical_text"
    / "CANONICAL_TEXT_ATTRIBUTE_REPAIR_POSTCHANGE_VERIFICATION_20260729_v0.json"
)

REMOVED_BROAD_RULES = (
    "formal/docs/release/*.json text eol=lf",
    "formal/docs/release/*.md text eol=lf",
    "formal/markdown/locks/**/*.md text eol=lf",
    "formal/output/*.json text eol=lf",
    "formal/output/**/*.json text eol=lf",
    "formal/python/**/*.py text eol=lf",
    "formal/toe_formal/**/*.lean text eol=lf",
)


class CanonicalTextMaintenanceError(RuntimeError):
    pass


def _run(*args: str, input_text: str | None = None) -> str:
    return subprocess.run(
        [*args],
        cwd=REPO_ROOT,
        check=True,
        input=input_text,
        capture_output=True,
        text=True,
    ).stdout


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    ).encode("utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise CanonicalTextMaintenanceError(f"expected object: {path}")
    return value


def _tracked_paths() -> list[str]:
    return [
        row
        for row in _run("git", "ls-files").splitlines()
        if row and row != "reddit"
    ]


def _affected_by_removed_broad_rule(path: str) -> bool:
    candidate = Path(path)
    suffix = candidate.suffix.casefold()
    parts = candidate.parts
    if len(parts) >= 4 and parts[:3] == ("formal", "docs", "release"):
        return suffix in {".json", ".md"}
    if len(parts) >= 3 and parts[:2] == ("formal", "output"):
        return suffix == ".json"
    if len(parts) >= 3 and parts[:2] == ("formal", "python"):
        return suffix == ".py"
    if len(parts) >= 3 and parts[:2] == ("formal", "toe_formal"):
        return suffix == ".lean"
    if len(parts) >= 4 and parts[:3] == ("formal", "markdown", "locks"):
        return suffix == ".md"
    return False


def affected_paths() -> list[str]:
    return sorted(path for path in _tracked_paths() if _affected_by_removed_broad_rule(path))


def _index_rows() -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for line in _run("git", "ls-files", "-s").splitlines():
        metadata, path = line.split("\t", 1)
        mode, object_id, stage = metadata.split()
        rows[path] = {
            "index_mode": mode,
            "index_object_id": object_id,
            "index_stage": int(stage),
        }
    return rows


def _effective_attributes(paths: list[str]) -> dict[str, dict[str, str]]:
    if not paths:
        return {}
    output = _run(
        "git",
        "check-attr",
        "-z",
        "--stdin",
        "text",
        "eol",
        input_text="\0".join(paths) + "\0",
    )
    result: dict[str, dict[str, str]] = {path: {} for path in paths}
    fields = output.split("\0")
    if fields[-1] == "":
        fields.pop()
    if len(fields) % 3 != 0:
        raise CanonicalTextMaintenanceError(
            "git check-attr returned an incomplete NUL-delimited record"
        )
    for offset in range(0, len(fields), 3):
        path, attribute, value = fields[offset : offset + 3]
        result[path][attribute] = value
    return result


def _head() -> str:
    return _run("git", "rev-parse", "HEAD").strip()


def _branch() -> str:
    return _run("git", "branch", "--show-current").strip()


def _path_record(
    relative_path: str,
    *,
    index: dict[str, dict[str, Any]],
    attributes: dict[str, dict[str, str]],
) -> dict[str, Any]:
    path = REPO_ROOT / relative_path
    if relative_path not in index:
        raise CanonicalTextMaintenanceError(f"tracked path missing from index: {relative_path}")
    raw = path.read_bytes()
    return {
        "path": relative_path,
        "file_size": len(raw),
        "working_tree_sha256": _sha256_bytes(raw),
        **index[relative_path],
        "effective_attributes": attributes[relative_path],
        "classification": "TRACKED_PATH_AFFECTED_BY_REMOVED_BROAD_TEXT_RULE",
    }


def build_prechange() -> dict[str, Any]:
    paths = affected_paths()
    index = _index_rows()
    attributes = _effective_attributes(paths)
    records = [
        _path_record(path, index=index, attributes=attributes)
        for path in paths
    ]
    return {
        "schema_id": "toe.canonical_text_attribute_repair.prechange_custody.v0",
        "artifact_id": "CANONICAL_TEXT_ATTRIBUTE_REPAIR_PRECHANGE_CUSTODY_20260729_v0",
        "captured_at_utc": "2026-07-29T00:00:00Z",
        "repository": {
            "branch": _branch(),
            "commit": _head(),
            "gitattributes_sha256": _sha256(ATTRIBUTES_PATH),
        },
        "removed_broad_rules": list(REMOVED_BROAD_RULES),
        "path_count": len(records),
        "paths": records,
        "boundary": {
            "bytes_rewritten": False,
            "index_renormalization_run": False,
            "scientific_target_rotated": False,
            "historical_blob_acceptance_claimed": False,
        },
    }


def build_postchange() -> dict[str, Any]:
    prechange = _read_json(PRECHANGE_PATH)
    old_rows = prechange["paths"]
    paths = [row["path"] for row in old_rows]
    if paths != sorted(paths):
        raise CanonicalTextMaintenanceError("prechange paths are not sorted")
    if paths != affected_paths():
        raise CanonicalTextMaintenanceError("affected tracked-path inventory changed")

    index = _index_rows()
    attributes = _effective_attributes(paths)
    comparisons = []
    changed_objects = []
    changed_worktree_hashes = []
    for old in old_rows:
        path = old["path"]
        current = _path_record(path, index=index, attributes=attributes)
        object_unchanged = old["index_object_id"] == current["index_object_id"]
        worktree_unchanged = (
            old["working_tree_sha256"] == current["working_tree_sha256"]
        )
        if not object_unchanged:
            changed_objects.append(path)
        if not worktree_unchanged:
            changed_worktree_hashes.append(path)
        comparisons.append(
            {
                "path": path,
                "old_effective_attributes": old["effective_attributes"],
                "new_effective_attributes": current["effective_attributes"],
                "old_index_object_id": old["index_object_id"],
                "new_index_object_id": current["index_object_id"],
                "index_object_unchanged": object_unchanged,
                "old_working_tree_sha256": old["working_tree_sha256"],
                "new_working_tree_sha256": current["working_tree_sha256"],
                "working_tree_bytes_unchanged": worktree_unchanged,
            }
        )

    attributes_text = ATTRIBUTES_PATH.read_text(encoding="utf-8")
    remaining_rules = [
        rule for rule in REMOVED_BROAD_RULES if rule in attributes_text
    ]
    return {
        "schema_id": "toe.canonical_text_attribute_repair.postchange_verification.v0",
        "artifact_id": (
            "CANONICAL_TEXT_ATTRIBUTE_REPAIR_POSTCHANGE_VERIFICATION_20260729_v0"
        ),
        "captured_at_utc": "2026-07-29T00:00:00Z",
        "prechange_artifact": PRECHANGE_PATH.relative_to(REPO_ROOT).as_posix(),
        "prechange_artifact_sha256": _sha256(PRECHANGE_PATH),
        "repository": {
            "branch": _branch(),
            "commit": _head(),
            "gitattributes_sha256": _sha256(ATTRIBUTES_PATH),
        },
        "path_count": len(comparisons),
        "comparisons": comparisons,
        "verification": {
            "changed_index_object_count": len(changed_objects),
            "changed_index_object_paths": changed_objects,
            "changed_working_tree_byte_count": len(changed_worktree_hashes),
            "changed_working_tree_byte_paths": changed_worktree_hashes,
            "remaining_forbidden_broad_rule_count": len(remaining_rules),
            "remaining_forbidden_broad_rules": remaining_rules,
            "historical_index_objects_unchanged": not changed_objects,
            "historical_working_tree_bytes_unchanged": not changed_worktree_hashes,
            "repository_wide_renormalization_run": False,
        },
    }


def validate_postchange(report: dict[str, Any]) -> None:
    verification = report["verification"]
    if verification["changed_index_object_count"] != 0:
        raise CanonicalTextMaintenanceError("historical index objects changed")
    if verification["changed_working_tree_byte_count"] != 0:
        raise CanonicalTextMaintenanceError("historical working-tree bytes changed")
    if verification["remaining_forbidden_broad_rule_count"] != 0:
        raise CanonicalTextMaintenanceError("forbidden broad rules remain")


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_json_bytes(payload))


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("write-prechange", "write-postchange", "check"))
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.command == "write-prechange":
        _write(PRECHANGE_PATH, build_prechange())
    elif args.command == "write-postchange":
        report = build_postchange()
        validate_postchange(report)
        _write(POSTCHANGE_PATH, report)
    else:
        if PRECHANGE_PATH.read_bytes() != _json_bytes(_read_json(PRECHANGE_PATH)):
            raise CanonicalTextMaintenanceError("prechange custody bytes drift")
        report = _read_json(POSTCHANGE_PATH)
        validate_postchange(report)
        if POSTCHANGE_PATH.read_bytes() != _json_bytes(report):
            raise CanonicalTextMaintenanceError("postchange verification bytes drift")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
