"""Verify and freeze the accepted repository-recovery lineage.

This tool deliberately reasons about Git objects and accepted evidence records.
It does not treat branch names, working-tree line endings, or a passing historical
snapshot as proof that an accepted repair remains present.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[3]
BASE_CONTRACT = (
    ROOT
    / "formal"
    / "docs"
    / "release"
    / "RECOVERY_ACCEPTED_LINEAGE_PROTECTED_INVARIANTS_20260725_v0.json"
)
DEFAULT_CONTRACT = (
    ROOT
    / "formal"
    / "docs"
    / "release"
    / "RECOVERY_ACCEPTED_LINEAGE_PROTECTED_INVARIANTS_20260725_v2.json"
)


class LineageError(RuntimeError):
    """Raised when the proposed recovery base is incomplete or ambiguous."""


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        .encode("utf-8")
        + b"\n"
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _git(*args: str, repo_root: Path = ROOT, check: bool = True) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if check and completed.returncode != 0:
        raise LineageError(
            f"git {' '.join(args)} failed ({completed.returncode}): "
            f"{completed.stderr.strip()}"
        )
    return completed.stdout.strip()


def load_contract(path: Path = DEFAULT_CONTRACT) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema_id") not in {
        "RECOVERY_ACCEPTED_LINEAGE_PROTECTED_INVARIANTS_20260725_v0",
        "RECOVERY_ACCEPTED_LINEAGE_PROTECTED_INVARIANTS_20260725_v1",
        "RECOVERY_ACCEPTED_LINEAGE_PROTECTED_INVARIANTS_20260725_v2",
    }:
        raise LineageError("unexpected protected-invariant contract schema")
    if not payload.get("accepted_repairs"):
        raise LineageError("protected-invariant contract has no accepted repairs")
    return payload


def _contract_chain(
    contract: dict[str, Any],
    *,
    contract_path: Path,
    repo_root: Path,
) -> list[dict[str, Any]]:
    """Return the oldest-to-newest frozen contract chain."""

    chain = [contract]
    active = contract
    active_path = contract_path
    seen = {active_path.resolve()}
    while "base_contract" in active:
        reference = active["base_contract"]
        base_path = (repo_root / reference["path"]).resolve()
        if base_path in seen:
            raise LineageError("protected-invariant contract chain contains a cycle")
        seen.add(base_path)
        if sha256_path(base_path) != reference["sha256"]:
            raise LineageError("accepted protected-invariant base contract drift")
        base = load_contract(base_path)
        if len(base["accepted_repairs"]) != reference["accepted_repair_count"]:
            raise LineageError("accepted base-contract repair-count binding drift")
        chain.append(base)
        active = base
        active_path = base_path
    return list(reversed(chain))


def _is_ancestor(ancestor: str, descendant: str, repo_root: Path) -> bool:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), "merge-base", "--is-ancestor", ancestor, descendant],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return completed.returncode == 0


def _object_exists(object_id: str, repo_root: Path) -> bool:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), "cat-file", "-e", f"{object_id}^{{object}}"],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return completed.returncode == 0


def _tree(commit: str, repo_root: Path) -> str:
    return _git("show", "-s", "--format=%T", commit, repo_root=repo_root)


def _blob_at(commit: str, path: str, repo_root: Path) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), "show", f"{commit}:{path}"],
        check=False,
        capture_output=True,
    )
    if completed.returncode != 0:
        raise LineageError(
            f"cannot read {path} at {commit}: "
            f"{completed.stderr.decode('utf-8', errors='replace').strip()}"
        )
    return completed.stdout


def _first_add_commit(path: str, head: str, repo_root: Path) -> str:
    commits = _git(
        "log",
        "--diff-filter=A",
        "--format=%H",
        "--reverse",
        head,
        "--",
        path,
        repo_root=repo_root,
    ).splitlines()
    if not commits:
        raise LineageError(f"no introducing commit found for {path}")
    return commits[0]


def _all_strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for child in value.values():
            yield from _all_strings(child)
    elif isinstance(value, list):
        for child in value:
            yield from _all_strings(child)


def _evidence_inventory(
    start: str, head: str, repo_root: Path
) -> dict[str, list[dict[str, str]]]:
    history = _git(
        "log",
        "--reverse",
        "--format=@@%H",
        "--name-status",
        f"{start}..{head}",
        "--",
        "formal/docs/release",
        repo_root=repo_root,
    )
    introduced_by: dict[str, str] = {}
    active_commit = ""
    for line in history.splitlines():
        if line.startswith("@@"):
            active_commit = line[2:]
            continue
        fields = line.split("\t")
        if len(fields) >= 2 and fields[0] == "A":
            introduced_by.setdefault(fields[-1], active_commit)

    added = _git(
        "diff",
        "--diff-filter=A",
        "--name-only",
        f"{start}..{head}",
        "--",
        "formal/docs/release",
        repo_root=repo_root,
    ).splitlines()
    buckets: dict[str, list[dict[str, str]]] = {
        "selectors": [],
        "packets": [],
        "results": [],
        "reviews": [],
    }
    for path in sorted(item for item in added if item.endswith(".json")):
        name = Path(path).name
        if "RESULT_REVIEW" in name or "PACKET_REVIEW" in name:
            bucket = "reviews"
        elif "_RESULT_" in name:
            bucket = "results"
        elif "PACKET" in name:
            bucket = "packets"
        elif "SELECTION" in name or "AUTHORITY" in name:
            bucket = "selectors"
        else:
            continue
        blob = _blob_at(head, path, repo_root)
        buckets[bucket].append(
            {
                "path": path,
                "sha256": sha256_bytes(blob),
                "introduced_by": introduced_by.get(path)
                or _first_add_commit(path, head, repo_root),
            }
        )
    return buckets


def _manifest_root(rows: list[dict[str, str]]) -> str:
    return sha256_bytes(canonical_json_bytes(rows))


def _commit_inventory(start: str, head: str, repo_root: Path) -> list[dict[str, Any]]:
    raw = _git(
        "log",
        "--reverse",
        "--format=%H%x1f%P%x1f%T%x1f%s",
        f"{start}..{head}",
        repo_root=repo_root,
    )
    rows: list[dict[str, Any]] = []
    previous = start
    for line in raw.splitlines():
        commit, parents_raw, tree, subject = line.split("\x1f", 3)
        parents = parents_raw.split()
        if parents != [previous]:
            raise LineageError(
                f"recovery lineage is not linear at {commit}: "
                f"expected parent {previous}, observed {parents}"
            )
        rows.append(
            {
                "commit": commit,
                "parent": parents[0],
                "tree": tree,
                "subject": subject,
            }
        )
        previous = commit
    if not rows or rows[-1]["commit"] != head:
        raise LineageError("proposed base is not the terminal commit of the lineage")
    return rows


def _verify_cycle(
    cycle: dict[str, Any], head: str, repo_root: Path
) -> dict[str, Any]:
    commits = [cycle["authorization_commit"]]
    commits.extend(item["commit"] for item in cycle["implementation_commits"])
    commits.append(cycle["accepted_commit"])
    for commit in commits:
        if not _object_exists(commit, repo_root):
            raise LineageError(f"{cycle['cycle_id']}: missing commit {commit}")
        if not _is_ancestor(commit, head, repo_root):
            raise LineageError(
                f"{cycle['cycle_id']}: accepted commit {commit} is not in proposed base"
            )
    for item in cycle["implementation_commits"]:
        observed_tree = _tree(item["commit"], repo_root)
        if observed_tree != item["tree"]:
            raise LineageError(
                f"{cycle['cycle_id']}: tree mismatch at {item['commit']}: "
                f"{observed_tree} != {item['tree']}"
            )

    result_path = cycle["result_path"]
    review_path = cycle["review_path"]
    result_commit = _first_add_commit(result_path, head, repo_root)
    review_commit = _first_add_commit(review_path, head, repo_root)
    result_blob = _blob_at(result_commit, result_path, repo_root)
    review_blob = _blob_at(review_commit, review_path, repo_root)
    result_sha = sha256_bytes(result_blob)
    review_sha = sha256_bytes(review_blob)
    if cycle.get("result_sha256", result_sha) != result_sha:
        raise LineageError(f"{cycle['cycle_id']}: frozen result SHA-256 drift")
    if cycle.get("review_sha256", review_sha) != review_sha:
        raise LineageError(f"{cycle['cycle_id']}: frozen review SHA-256 drift")
    result_payload = json.loads(result_blob.decode("utf-8"))
    review_payload = json.loads(review_blob.decode("utf-8"))
    result_strings = set(_all_strings(result_payload))
    binding_mode = cycle.get("result_binding_mode", "ORIGINAL_RESULT_EXPLICIT")
    if binding_mode == "ORIGINAL_RESULT_EXPLICIT":
        for item in cycle["implementation_commits"]:
            if item["commit"] not in result_strings:
                raise LineageError(
                    f"{cycle['cycle_id']}: result does not bind implementation "
                    f"{item['commit']}"
                )
    elif binding_mode != "SUPPLEMENTAL_MANIFEST_BINDS_IMPLEMENTATION":
        raise LineageError(
            f"{cycle['cycle_id']}: unsupported result binding mode {binding_mode}"
        )
    review_strings = set(_all_strings(review_payload))
    if result_sha not in review_strings:
        raise LineageError(
            f"{cycle['cycle_id']}: review does not bind result SHA-256 {result_sha}"
        )
    review_commit_binding = result_commit in review_strings

    guards: list[dict[str, Any]] = []
    for guard in cycle["current_enforcing_guards"]:
        path = guard["path"]
        blob = _blob_at(head, path, repo_root)
        guards.append(
            {
                "path": path,
                "selectors": guard.get("selectors", []),
                "git_blob": _git(
                    "rev-parse", f"{head}:{path}", repo_root=repo_root
                ),
                "sha256": sha256_bytes(blob),
                "class": "PROTECTED_INVARIANT_GUARD",
            }
        )
    for superseded in cycle["superseded_guards"]:
        evidence_path = superseded["accepted_supersession_evidence"]
        _blob_at(head, evidence_path, repo_root)

    return {
        "cycle_id": cycle["cycle_id"],
        "authorization_commit": cycle["authorization_commit"],
        "implementation_commits": cycle["implementation_commits"],
        "accepted_commit": cycle["accepted_commit"],
        "accepted_commit_tree": _tree(cycle["accepted_commit"], repo_root),
        "protected_invariant": cycle["protected_invariant"],
        "current_enforcing_guards": guards,
        "historical_snapshot_guards": [
            {
                "guard": guard,
                "class": "HISTORICAL_SNAPSHOT_GUARD",
            }
            for guard in cycle["historical_snapshot_guards"]
        ],
        "superseded_guards": [
            {
                **guard,
                "class": "SUPERSEDED_GUARD_WITH_ACCEPTED_REPLACEMENT",
            }
            for guard in cycle["superseded_guards"]
        ],
        "result": {
            "path": result_path,
            "commit": result_commit,
            "sha256": result_sha,
        },
        "review": {
            "path": review_path,
            "commit": review_commit,
            "sha256": sha256_bytes(review_blob),
            "binds_result_commit_explicitly": review_commit_binding,
            "binds_result_sha256": True,
        },
        "result_binding_mode": binding_mode,
    }


def build_manifest(
    *,
    repo_root: Path = ROOT,
    contract_path: Path = DEFAULT_CONTRACT,
) -> dict[str, Any]:
    contract = load_contract(contract_path)
    chain = _contract_chain(
        contract,
        contract_path=contract_path,
        repo_root=repo_root,
    )
    accepted_repairs = [
        repair
        for version in chain
        for repair in version["accepted_repairs"]
    ]
    start = contract["recovery_start_commit"]
    head = contract["proposed_base"]["commit"]
    if _tree(head, repo_root) != contract["proposed_base"]["tree"]:
        raise LineageError("proposed-base tree does not match the frozen contract")
    if not _is_ancestor(start, head, repo_root):
        raise LineageError("recovery start is not an ancestor of proposed base")

    commit_rows = _commit_inventory(start, head, repo_root)
    cycles = [
        _verify_cycle(cycle, head, repo_root)
        for cycle in accepted_repairs
    ]

    unexpected_accepts = _git(
        "log",
        "--all",
        "--not",
        head,
        "--format=%H%x1f%s",
        "--grep=^Accept",
        repo_root=repo_root,
    ).splitlines()
    if unexpected_accepts:
        raise LineageError(
            "accepted commits exist outside the proposed base: "
            + "; ".join(unexpected_accepts)
        )

    evidence = _evidence_inventory(start, head, repo_root)
    protected_rows = [
        {
            "cycle_id": cycle["cycle_id"],
            "protected_invariant": cycle["protected_invariant"],
            "current_enforcing_guards": cycle["current_enforcing_guards"],
            "historical_snapshot_guards": cycle["historical_snapshot_guards"],
            "superseded_guards": cycle["superseded_guards"],
        }
        for cycle in cycles
    ]
    result_rows = evidence["results"]
    review_rows = evidence["reviews"]
    return {
        "schema_id": contract["schema_id"].replace(
            "PROTECTED_INVARIANTS",
            "COMPLETENESS_MANIFEST",
        ),
        "status": "RECOVERY_BASE_ACCEPTED_LINEAGE_COMPLETE",
        "recovery_start_commit": start,
        "proposed_base_identity": {
            "commit": head,
            "tree": contract["proposed_base"]["tree"],
            "accepted_result_manifest_root": _manifest_root(result_rows),
            "accepted_review_manifest_root": _manifest_root(review_rows),
            "protected_invariant_manifest_root": sha256_bytes(
                canonical_json_bytes(protected_rows)
            ),
        },
        "lineage": {
            "commit_count": len(commit_rows),
            "linear": True,
            "commits": commit_rows,
        },
        "accepted_repairs": cycles,
        "evidence_inventory": {
            **evidence,
            "roots": {
                bucket: _manifest_root(rows)
                for bucket, rows in evidence.items()
            },
        },
        "external_or_sibling_accepted_commits": [],
        "guard_execution_required": [
            guard
            for cycle in cycles
            for guard in cycle["current_enforcing_guards"]
        ],
        "scientific_posture": "B-BLOCKED",
        "v2_enrollment": "NOT_AUTHORIZED",
        "scientific_resumption": "NOT_AUTHORIZED",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    manifest = build_manifest(
        repo_root=args.repo_root.resolve(),
        contract_path=args.contract.resolve(),
    )
    encoded = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8", newline="\n")
    else:
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
