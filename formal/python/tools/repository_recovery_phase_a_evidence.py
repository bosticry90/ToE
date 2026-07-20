from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


AUDITED_COMMIT = "75af1d110a57df26344ca151ccd26b9f5c1f7736"
REGISTRY_BASE_COMMIT = "0e194f72"
EXPECTED_DIRTY_COUNT = 629
EXPECTED_TRACKED_DIRTY_COUNT = 7
EXPECTED_UNTRACKED_COUNT = 622
REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
CURRENT_TARGET_REL = "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_REL = "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"


class EvidenceError(RuntimeError):
    pass


def _run(
    root: Path,
    args: list[str],
    *,
    check: bool = True,
    text: bool = False,
) -> subprocess.CompletedProcess[Any]:
    return subprocess.run(
        args,
        cwd=root,
        check=check,
        capture_output=True,
        text=text,
    )


def _canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def _sha_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _timestamp() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _status_rows(root: Path) -> list[dict[str, str]]:
    raw = _run(
        root,
        ["git", "status", "--porcelain=v1", "-z", "-uall"],
    ).stdout
    parts = [part for part in raw.split(b"\0") if part]
    rows: list[dict[str, str]] = []
    index = 0
    while index < len(parts):
        item = parts[index]
        status = item[:2].decode("ascii")
        path = item[3:].decode("utf-8", errors="strict").replace("\\", "/")
        row = {"status": status, "path": path}
        if status[0] in {"R", "C"}:
            index += 1
            row["source_path"] = parts[index].decode("utf-8", errors="strict").replace(
                "\\", "/"
            )
        rows.append(row)
        index += 1
    return sorted(rows, key=lambda row: row["path"].casefold())


def _git_config(root: Path) -> dict[str, str]:
    result = _run(root, ["git", "config", "--list", "--show-origin"], text=True)
    rows: dict[str, str] = {}
    for index, line in enumerate(result.stdout.splitlines()):
        rows[f"row_{index:04d}"] = line
    return rows


def _attributes(root: Path, relative: str) -> dict[str, str]:
    proc = _run(
        root,
        [
            "git",
            "check-attr",
            "text",
            "eol",
            "working-tree-encoding",
            "--",
            relative,
        ],
        text=True,
    )
    result: dict[str, str] = {}
    for line in proc.stdout.splitlines():
        parts = line.split(": ", 2)
        if len(parts) == 3:
            result[parts[1]] = parts[2]
    return result


def _tracked_mode(root: Path, relative: str) -> str | None:
    result = _run(
        root,
        ["git", "ls-files", "--stage", "--", relative],
        text=True,
    ).stdout.strip()
    return result.split(maxsplit=1)[0] if result else None


def _head_blob(root: Path, relative: str) -> bytes | None:
    proc = _run(
        root,
        ["git", "show", f"HEAD:{relative}"],
        check=False,
    )
    return proc.stdout if proc.returncode == 0 else None


def _ignored(root: Path, relative: str) -> bool:
    proc = _run(
        root,
        ["git", "check-ignore", "-q", "--", relative],
        check=False,
    )
    return proc.returncode == 0


def _references(root: Path, relative: str) -> list[str]:
    name = Path(relative).name
    if len(name) < 8:
        return []
    proc = _run(
        root,
        [
            "git",
            "grep",
            "-l",
            "-F",
            "-e",
            name,
            "--",
            ".",
            ":(exclude)archive/**",
            ":(exclude)backup/**",
        ],
        check=False,
        text=True,
    )
    if proc.returncode not in {0, 1}:
        return []
    return sorted(
        {
            line.replace("\\", "/")
            for line in proc.stdout.splitlines()
            if line and line.replace("\\", "/") != relative
        }
    )[:100]


def _classification(relative: str, status: str) -> tuple[str, str, str, str]:
    lowered = relative.casefold()
    if any(token in lowered for token in ("__pycache__", ".pytest_cache", ".pyc")):
        return (
            "CACHE_OR_TRANSIENT",
            "path_rule_cache_or_bytecode",
            "HIGH",
            "PRESERVE_THEN_ELIGIBLE_FOR_SEPARATE_CLEANUP",
        )
    if "scalar_only_yukawa" in lowered or "yukawa" in lowered:
        return (
            "SCIENTIFIC_ARTIFACT",
            "path_rule_scalar_yukawa_lane",
            "HIGH",
            "PRESERVE_NONCURRENT_NO_FURTHER_EXECUTION",
        )
    if lowered.startswith("formal/output/"):
        return (
            "EXECUTION_EVIDENCE",
            "path_rule_formal_output",
            "MEDIUM",
            "PRESERVE_PENDING_AUTHORITY_CLASSIFICATION",
        )
    if lowered.startswith("formal/python/tools/"):
        return (
            "EXPLORATORY_IMPLEMENTATION",
            "path_rule_python_tool",
            "MEDIUM",
            "PRESERVE_PENDING_MANUAL_REVIEW",
        )
    if lowered.startswith("formal/python/tests/") or lowered.startswith(
        "formal/docs/release/"
    ):
        return (
            "GOVERNANCE_ARTIFACT",
            "path_rule_governance_surface",
            "MEDIUM",
            "PRESERVE_PENDING_AUTHORITY_CLASSIFICATION",
        )
    if lowered.endswith(".lean"):
        return (
            "SCIENTIFIC_ARTIFACT",
            "path_rule_lean_surface",
            "MEDIUM",
            "PRESERVE_PENDING_AUTHORITY_CLASSIFICATION",
        )
    if status.strip() == "D":
        return (
            "GOVERNANCE_ARTIFACT",
            "tracked_deletion_requires_manual_review",
            "MEDIUM",
            "PRESERVE_DELETION_AND_HEAD_BLOB",
        )
    return (
        "UNKNOWN_MANUAL_REVIEW",
        "no_high_confidence_path_rule",
        "LOW",
        "PRESERVE_PENDING_MANUAL_REVIEW",
    )


def _copy_object(custody: Path, digest: str, source: Path) -> Path:
    destination = custody / "objects" / digest[:2] / digest
    destination.parent.mkdir(parents=True, exist_ok=True)
    if not destination.exists():
        shutil.copyfile(source, destination)
    if _sha_path(destination) != digest:
        raise EvidenceError(f"custody object verification failed: {source}")
    return destination


def _copy_bytes(custody: Path, digest: str, value: bytes) -> Path:
    destination = custody / "objects" / digest[:2] / digest
    destination.parent.mkdir(parents=True, exist_ok=True)
    if not destination.exists():
        destination.write_bytes(value)
    if _sha_path(destination) != digest:
        raise EvidenceError("custody byte-object verification failed")
    return destination


def capture_custody(source: Path, custody: Path) -> dict[str, Any]:
    if custody.exists() and any(custody.iterdir()):
        raise EvidenceError(f"custody directory must start empty: {custody}")
    custody.mkdir(parents=True, exist_ok=True)
    started = _timestamp()
    initial = _status_rows(source)
    tracked_dirty = [row for row in initial if row["status"] != "??"]
    untracked = [row for row in initial if row["status"] == "??"]
    if (
        len(initial) != EXPECTED_DIRTY_COUNT
        or len(tracked_dirty) != EXPECTED_TRACKED_DIRTY_COUNT
        or len(untracked) != EXPECTED_UNTRACKED_COUNT
    ):
        raise EvidenceError(
            "audited worktree count drift: "
            f"total={len(initial)} tracked={len(tracked_dirty)} untracked={len(untracked)}"
        )

    entries: list[dict[str, Any]] = []
    for status_row in initial:
        relative = status_row["path"]
        path = source / Path(relative)
        exists = path.exists() or path.is_symlink()
        tracked = status_row["status"] != "??"
        mode = _tracked_mode(source, relative)
        attributes = _attributes(source, relative)
        file_type = "missing"
        size: int | None = None
        digest: str | None = None
        symlink_target: str | None = None
        custody_object: str | None = None
        mtime_ns: int | None = None
        if exists:
            info = path.lstat()
            mtime_ns = info.st_mtime_ns
            if stat.S_ISLNK(info.st_mode):
                file_type = "symlink"
                symlink_target = os.readlink(path)
                value = symlink_target.encode("utf-8")
                size = len(value)
                digest = _sha_bytes(value)
                custody_object = str(_copy_bytes(custody, digest, value).relative_to(custody)).replace(
                    "\\", "/"
                )
            elif stat.S_ISREG(info.st_mode):
                file_type = "regular"
                size = info.st_size
                digest = _sha_path(path)
                custody_object = str(_copy_object(custody, digest, path).relative_to(custody)).replace(
                    "\\", "/"
                )
            else:
                file_type = "other"
        head_blob = _head_blob(source, relative) if tracked else None
        head_blob_sha256 = _sha_bytes(head_blob) if head_blob is not None else None
        head_blob_object = None
        if head_blob is not None and not exists:
            head_blob_object = str(
                _copy_bytes(custody, head_blob_sha256, head_blob).relative_to(custody)
            ).replace("\\", "/")
        classification, rule, confidence, disposition = _classification(
            relative, status_row["status"]
        )
        entries.append(
            {
                **status_row,
                "tracked": tracked,
                "ignored": _ignored(source, relative),
                "exists": exists,
                "file_type": file_type,
                "git_file_mode": mode,
                "filesystem_mode": oct(path.lstat().st_mode) if exists else None,
                "symlink_target": symlink_target,
                "size": size,
                "sha256": digest,
                "mtime_ns": mtime_ns,
                "git_attributes": attributes,
                "head_blob_sha256": head_blob_sha256,
                "custody_object": custody_object,
                "head_blob_custody_object": head_blob_object,
                "tracked_references": _references(source, relative),
                "producing_tool": None,
                "authority_or_packet_references": [],
                "classification": classification,
                "classification_rule": rule,
                "classification_confidence": confidence,
                "manual_review_status": "REQUIRED"
                if confidence != "HIGH"
                else "NOT_REQUIRED_BY_RULE",
                "recommended_disposition": disposition,
            }
        )

    final = _status_rows(source)
    if final != initial:
        raise EvidenceError("EVIDENCE_BLOCKED_CUSTODY_MUTATION: Git status changed")
    for entry in entries:
        relative = entry["path"]
        path = source / Path(relative)
        exists = path.exists() or path.is_symlink()
        if exists != entry["exists"]:
            raise EvidenceError(f"EVIDENCE_BLOCKED_CUSTODY_MUTATION: existence {relative}")
        if entry["file_type"] == "regular" and _sha_path(path) != entry["sha256"]:
            raise EvidenceError(f"EVIDENCE_BLOCKED_CUSTODY_MUTATION: content {relative}")
        if entry["file_type"] == "symlink" and os.readlink(path) != entry["symlink_target"]:
            raise EvidenceError(f"EVIDENCE_BLOCKED_CUSTODY_MUTATION: symlink {relative}")

    root_payload = {
        "schema_id": "DIRTY_WORKTREE_CUSTODY_MANIFEST_20260719_v0",
        "audited_commit": AUDITED_COMMIT,
        "source_root": str(source).replace("\\", "/"),
        "capture_started_utc": started,
        "capture_completed_utc": _timestamp(),
        "identity": {
            "branch": _run(source, ["git", "branch", "--show-current"], text=True).stdout.strip(),
            "head": _run(source, ["git", "rev-parse", "HEAD"], text=True).stdout.strip(),
            "upstream": _run(
                source,
                ["git", "rev-parse", "@{upstream}"],
                check=False,
                text=True,
            ).stdout.strip()
            or None,
            "remote_origin": _run(
                source, ["git", "config", "--get", "remote.origin.url"], text=True
            ).stdout.strip(),
            "core_ignorecase": _run(
                source, ["git", "config", "--bool", "core.ignorecase"], text=True
            ).stdout.strip(),
            "git_config": _git_config(source),
        },
        "counts": {
            "total": len(entries),
            "tracked_dirty": len(tracked_dirty),
            "untracked": len(untracked),
        },
        "original_worktree_unchanged": True,
        "entries": entries,
    }
    manifest_bytes = _canonical(root_payload)
    manifest_path = custody / "DIRTY_WORKTREE_CUSTODY_MANIFEST_v0.json"
    manifest_path.write_bytes(manifest_bytes)
    manifest_sha = _sha_bytes(manifest_bytes)
    (custody / "DIRTY_WORKTREE_CUSTODY_MANIFEST_v0.sha256").write_text(
        f"{manifest_sha}  {manifest_path.name}\n", encoding="ascii"
    )
    return root_payload


def _commit_rows(repo: Path) -> list[dict[str, Any]]:
    hashes = _run(
        repo,
        ["git", "rev-list", "--reverse", f"{REGISTRY_BASE_COMMIT}..{AUDITED_COMMIT}"],
        text=True,
    ).stdout.splitlines()
    rows: list[dict[str, Any]] = []
    for commit in hashes:
        meta = _run(
            repo,
            ["git", "show", "-s", "--format=%H%x00%P%x00%an%x00%aI%x00%s", commit],
        ).stdout.decode("utf-8").strip().split("\0")
        paths = _run(
            repo,
            ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit],
            text=True,
        ).stdout.splitlines()
        normalized = [path.replace("\\", "/") for path in paths if path]
        result_paths = [path for path in normalized if "result_review" in path.casefold()]
        packet_paths = [path for path in normalized if "packet" in path.casefold()]
        target_bearing = any(
            token in path.casefold()
            for path in normalized
            for token in (
                "currenttarget.lean",
                "currentauthority.lean",
                "loop_control_registry",
                "result_review",
                "selector",
                "selection",
            )
        )
        rows.append(
            {
                "commit": meta[0],
                "parents": meta[1].split(),
                "author": meta[2],
                "authored_at": meta[3],
                "declared_purpose": meta[4],
                "changed_paths": normalized,
                "target_bearing_change_present": target_bearing,
                "registry_change_present": REGISTRY_REL in normalized,
                "thin_mirror_change_present": any(
                    path in {CURRENT_TARGET_REL, CURRENT_AUTHORITY_REL} for path in normalized
                ),
                "packet_artifacts": packet_paths,
                "result_artifacts": result_paths,
            }
        )
    return rows


def _extract_transition_values(repo: Path, commit: str, relative: str) -> dict[str, Any]:
    proc = _run(repo, ["git", "show", f"{commit}:{relative}"], check=False)
    if proc.returncode != 0:
        return {"content_available": False}
    value = proc.stdout
    result: dict[str, Any] = {
        "content_available": True,
        "sha256": _sha_bytes(value),
    }
    text = value.decode("utf-8", errors="replace")
    if relative.endswith(".json"):
        try:
            payload = json.loads(text)
        except json.JSONDecodeError:
            payload = {}
        for key in (
            "target",
            "selected_next_target",
            "selected_next_target_kind",
            "verdict",
            "status",
            "accepted",
        ):
            if key in payload:
                result[key] = payload[key]
    else:
        for token in (
            "prepare_",
            "execute_",
            "review_",
            "select_",
        ):
            candidates = [
                segment.split('"', 1)[0]
                for segment in text.split(f'"{token}')[1:]
            ]
            if candidates:
                result.setdefault("target_tokens", []).extend(
                    [token + candidate for candidate in candidates[:10]]
                )
    return result


def build_provenance(repo: Path, custody_manifest: dict[str, Any]) -> dict[str, Any]:
    commit_rows = _commit_rows(repo)
    transitions: list[dict[str, Any]] = []
    for row in commit_rows:
        if not row["target_bearing_change_present"]:
            continue
        selected_paths = [
            path
            for path in row["changed_paths"]
            if any(
                token in path.casefold()
                for token in (
                    "currenttarget.lean",
                    "currentauthority.lean",
                    "loop_control_registry",
                    "selector",
                    "selection",
                    "packet",
                    "result_review",
                )
            )
        ]
        for relative in selected_paths:
            transitions.append(
                {
                    "commit": row["commit"],
                    "declared_purpose": row["declared_purpose"],
                    "path": relative,
                    "artifact": _extract_transition_values(repo, row["commit"], relative),
                    "registry_enrolled": row["registry_change_present"],
                    "thin_mirror_propagated": row["thin_mirror_change_present"],
                    "tracked_at_audited_commit": bool(
                        _run(
                            repo,
                            ["git", "ls-files", "--error-unmatch", "--", relative],
                            check=False,
                        ).returncode
                        == 0
                    ),
                    "authority_classification": (
                        "REGISTRY_ENROLLED_CURRENT"
                        if row["registry_change_present"]
                        else "TRACKED_BUT_NOT_REGISTRY_ENROLLED"
                    ),
                }
            )

    local_entries = custody_manifest["entries"]
    scalar_entries = [
        row
        for row in local_entries
        if "scalar_only_yukawa" in row["path"].casefold()
        or "yukawa" in row["path"].casefold()
    ]
    current_target_local = next(
        (row for row in local_entries if row["path"] == CURRENT_TARGET_REL), None
    )
    current_authority_local = next(
        (row for row in local_entries if row["path"] == CURRENT_AUTHORITY_REL), None
    )
    v2_packet = (
        "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
        "ROUTE_SELECTION_PACKET_20260713_v2.json"
    )
    v2_review = (
        "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
        "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260713_v2.json"
    )
    artifacts = {
        "tracked_v2": {
            "paths": [v2_packet, v2_review],
            "classification": "TRACKED_BUT_NOT_REGISTRY_ENROLLED",
            "review_token": "ACCEPT",
            "repository_level_acceptance": False,
            "successor_authority": False,
        },
        "post_registry_maxwell_dirac": {
            "commit_count": sum(
                1
                for row in commit_rows
                if "maxwell" in row["declared_purpose"].casefold()
                or "dirac" in row["declared_purpose"].casefold()
            ),
            "classification": "TRACKED_BUT_NOT_REGISTRY_ENROLLED",
            "automatic_ratification": False,
        },
        "local_scalar_yukawa": {
            "artifact_count": len(scalar_entries),
            "classification": "LOCAL_UNTRACKED_EXPLORATORY",
            "disposition": (
                "PRESERVED_HASHED_CLASSIFIED_NONCURRENT_NO_FURTHER_EXECUTION_"
                "ARCHIVE_AND_DEFER"
            ),
        },
        "current_mirrors": {
            "tracked_head_target": "DIRAC_MAXWELL_CHAIN",
            "dirty_worktree_target": "SCALAR_YUKAWA_CHAIN",
            "registry_target": (
                "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
                "route_selection_packet_v2"
            ),
            "current_target_entry": current_target_local,
            "current_authority_entry": current_authority_local,
            "classification": "PROVENANCE_INCOMPLETE",
        },
    }
    return {
        "commit_lineage": {
            "schema_id": "AUTHORITY_COMMIT_LINEAGE_20260719_v0",
            "base_commit": REGISTRY_BASE_COMMIT,
            "audited_commit": AUDITED_COMMIT,
            "commit_count": len(commit_rows),
            "rows": commit_rows,
        },
        "transition_ledger": {
            "schema_id": "AUTHORITY_TRANSITION_LEDGER_20260719_v0",
            "transition_count": len(transitions),
            "rows": transitions,
        },
        "artifact_classification": {
            "schema_id": "POST_REGISTRY_ARTIFACT_CLASSIFICATION_20260719_v0",
            "artifacts": artifacts,
            "scientific_posture": "B-BLOCKED",
            "scientific_status_changed": False,
        },
    }


def write_provenance(repo: Path, custody: Path) -> None:
    manifest = json.loads(
        (custody / "DIRTY_WORKTREE_CUSTODY_MANIFEST_v0.json").read_text(
            encoding="utf-8"
        )
    )
    result = build_provenance(repo, manifest)
    outputs = {
        "AUTHORITY_COMMIT_LINEAGE_v0.json": result["commit_lineage"],
        "AUTHORITY_TRANSITION_LEDGER_v0.json": result["transition_ledger"],
        "POST_REGISTRY_ARTIFACT_CLASSIFICATION_v0.json": result[
            "artifact_classification"
        ],
    }
    for name, value in outputs.items():
        (custody / name).write_bytes(_canonical(value))


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    custody_parser = sub.add_parser("custody")
    custody_parser.add_argument("--source", type=Path, required=True)
    custody_parser.add_argument("--custody", type=Path, required=True)
    provenance_parser = sub.add_parser("provenance")
    provenance_parser.add_argument("--repo", type=Path, required=True)
    provenance_parser.add_argument("--custody", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "custody":
        capture_custody(args.source.resolve(), args.custody.resolve())
    else:
        write_provenance(args.repo.resolve(), args.custody.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
