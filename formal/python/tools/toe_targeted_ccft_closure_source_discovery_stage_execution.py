from __future__ import annotations

"""Execute the authorized targeted CCFT Stage-1 discovery pass.

The tool consumes the immutable repository-wide census records, verifies local
bytes at execution time, and reads eligible content exactly once to apply the
frozen branch-and-contract candidate gate.  It does not extract or adjudicate
closure contracts.
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    raise SystemExit(
        "Run this tool as a module:\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_Path(__file__).stem} --help"
    )

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import unicodedata
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.bounded_program_governance import jcs_bytes


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
STAGE_ID = "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY"
TARGET = "discover_toe_targeted_ccft_closure_evidence_sources_v0"
OPEN_EVENT = (
    REPO_ROOT
    / "formal/docs/release/bounded_program_events"
    / f"{PROGRAM_ID}_ATTEMPT_01_OPEN_v0.json"
)
MANIFEST = (
    REPO_ROOT
    / "formal/docs/release/bounded_program_manifests"
    / f"{PROGRAM_ID}_MANIFEST_v1.json"
)
CENSUS_DIR = (
    REPO_ROOT
    / "formal/output/native_hypothesis_census_v1"
    / "REPOSITORY_WIDE_SOURCE_CENSUS"
)
CLAIM_RESULT = (
    REPO_ROOT
    / "formal/docs/release"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CLAIM_EXTRACTION_RESULT_v0.json"
)
LINEAGE_RESULT = (
    REPO_ROOT
    / "formal/docs/release"
    / "TOE_NATIVE_HYPOTHESIS_SOURCE_LINEAGE_RECONSTRUCTION_RESULT_v0.json"
)
CCFT_INPUTS = (
    REPO_ROOT
    / "formal/docs/release/TOE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY_RESULT_v0.json",
    REPO_ROOT
    / "formal/docs/release/TOE_CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION_RESULT_v0.json",
    REPO_ROOT
    / "formal/docs/release/TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_RESULT_v0.json",
)
RESULT_PATH = (
    REPO_ROOT
    / "formal/docs/release"
    / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_v0.json"
)
PASS_MARKER = (
    REPO_ROOT
    / ".toe_cache/targeted_ccft_closure_recovery_v0/stage_1_pass_consumed.json"
)

SUPPORTED_TEXT_EXTENSIONS = {
    "md",
    "txt",
    "py",
    "lean",
    "tex",
    "rst",
    "ps1",
    "sh",
    "cfg",
    "ini",
    "json",
    "yaml",
    "yml",
    "toml",
    "csv",
    "tsv",
    "ipynb",
}
METADATA_ONLY_EXTENSIONS = {
    "pdf",
    "docx",
    "xlsx",
    "pptx",
    "odt",
    "ods",
    "odp",
    "png",
    "jpg",
    "jpeg",
    "gif",
    "svg",
    "wav",
    "mp3",
    "mp4",
    "npy",
    "npz",
    "bin",
    "exe",
    "dll",
    "whl",
    "zip",
    "tar",
    "gz",
    "7z",
    "rar",
}
SOURCE_CLASS_ORDER = {
    "UNKNOWN_REQUIRES_REVIEW": 0,
    "SCIENTIFIC_DERIVED_SOURCE": 1,
    "HISTORICAL_PROJECT_METADATA": 2,
    "GENERATED_PROJECT_OUTPUT": 3,
}
STRUCTURAL_PATTERNS: dict[str, tuple[re.Pattern[str], ...]] = {
    "EVOLUTION_EQUATION_WITH_CUBIC_OR_QUARTIC_INTERACTION_AND_DEFINED_COEFFICIENTS": (
        re.compile(r"(?is)(?:cp[-_ ]?nlse|ucff|chi|χ).{0,800}(?:cubic|quartic|\|[^\n]{0,80}\|\s*\^?2|\*\*\s*3).{0,800}(?:coefficient|lambda|λ|alpha|α|beta|β|gamma|γ|g\b)"),
    ),
    "DISPERSION_RELATION_WITH_NONZERO_INTERACTION_TERM": (
        re.compile(r"(?is)(?:cp[-_ ]?nlse|ucff|lcrd).{0,1200}(?:dispersion|omega|ω|frequency).{0,800}(?:interaction|nonzero|coupling|alpha|α|beta|β|gamma|γ)"),
    ),
    "INITIAL_OR_BOUNDARY_DATA_DECLARATION_BOUND_TO_CP_NLSE_OR_LCRD_STATE": (
        re.compile(r"(?is)(?:cp[-_ ]?nlse|lcrd).{0,1200}(?:initial data|initial condition|boundary condition|periodic boundary|dirichlet|neumann)"),
    ),
    "PARAMETER_OR_NORMALIZATION_TABLE_BOUND_TO_A_CANDIDATE_BRANCH": (
        re.compile(r"(?is)(?:cp[-_ ]?nlse|ucff|lcrd).{0,1200}(?:parameter range|normalization|nondimensional|coefficient table)"),
    ),
    "INVARIANT_OR_FAILURE_ASSERTION_COMPUTABLE_FROM_A_CANDIDATE_STATE": (
        re.compile(r"(?is)(?:cp[-_ ]?nlse|ucff|lcrd).{0,1200}(?:conserved quantity|invariant|failure criterion|instability|blow[- ]?up)"),
    ),
    "LCRD_ROTOR_CURVATURE_CONSTITUTIVE_OR_COARSE_GRAINING_MAP": (
        re.compile(r"(?is)(?:lcrd|rotor[- ]curvature).{0,1600}(?:constitutive|closure relation|coarse[- ]graining|variational derivation)"),
    ),
    "REPRODUCIBLE_IMPLEMENTATION_ENTRYPOINT_WITH_PARAMETER_AND_DATA_CONTRACT": (
        re.compile(r"(?is)(?:cp[-_ ]?nlse|ucff|lcrd).{0,2000}(?:if\s+__name__|argparse|def\s+main|entrypoint).{0,1200}(?:parameter|config|initial|boundary)"),
    ),
}


class DiscoveryError(RuntimeError):
    pass


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _pretty_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def _normalize_path(value: str) -> str:
    candidate = value.replace("\\", "/")
    parts = PurePosixPath(candidate).parts
    if not parts or candidate.startswith("/") or any(
        part in {"", ".", ".."} for part in parts
    ):
        raise DiscoveryError(f"unsafe custody path: {value!r}")
    return PurePosixPath(*parts).as_posix()


def _is_reparse(info: os.stat_result) -> bool:
    flag = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)
    return bool(getattr(info, "st_file_attributes", 0) & flag)


def _inside(path: Path, root: Path) -> bool:
    try:
        path.resolve(strict=False).relative_to(root.resolve(strict=False))
    except ValueError:
        return False
    return True


class GitBlobReader:
    def __enter__(self) -> "GitBlobReader":
        self.process = subprocess.Popen(
            ["git", "cat-file", "--batch"],
            cwd=REPO_ROOT,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return self

    def __exit__(self, *_: object) -> None:
        if self.process.stdin:
            self.process.stdin.close()
        self.process.wait(timeout=30)

    def read(self, object_id: str) -> bytes:
        if self.process.stdin is None or self.process.stdout is None:
            raise DiscoveryError("git blob reader is not open")
        self.process.stdin.write(object_id.encode("ascii") + b"\n")
        self.process.stdin.flush()
        header = self.process.stdout.readline().decode("ascii").strip()
        parts = header.split()
        if len(parts) == 2 and parts[1] == "missing":
            raise DiscoveryError(f"Git blob unavailable: {object_id}")
        if len(parts) != 3 or parts[1] != "blob":
            raise DiscoveryError(f"unexpected git cat-file header: {header!r}")
        size = int(parts[2])
        data = self.process.stdout.read(size)
        trailer = self.process.stdout.read(1)
        if len(data) != size or trailer != b"\n":
            raise DiscoveryError(f"truncated Git blob read: {object_id}")
        return data


def _local_path(record: dict[str, Any]) -> tuple[Path, Path]:
    source_root_id = record["source_root_id"]
    relative = _normalize_path(record["custody_relative_path"])
    if source_root_id == "LOCAL_ARCHIVE_TOE_PROJECT":
        root = REPO_ROOT / "archive/ToE_Project"
        return root, root / Path(relative)
    if source_root_id == "LOCAL_ARCHIVE_TOE_PROJECT_STARTER_2025_09_24":
        root = REPO_ROOT / "archive/ToE_Project_Starter_2025-09-24"
        return root, root / Path(relative)
    root = REPO_ROOT
    return root, root / Path(relative)


def _read_local(record: dict[str, Any]) -> tuple[bytes | None, str]:
    root, path = _local_path(record)
    if not root.is_dir():
        return None, "SOURCE_ROOT_UNAVAILABLE"
    try:
        info = path.lstat()
    except OSError:
        return None, "CUSTODY_PATH_UNAVAILABLE"
    if path.is_symlink() or _is_reparse(info) or not stat.S_ISREG(info.st_mode):
        return None, "SAFETY_BLOCKED_NONREGULAR_OR_REPARSE"
    if not _inside(path, root):
        return None, "SAFETY_BLOCKED_ROOT_ESCAPE"
    try:
        return path.read_bytes(), "VERIFIED_CURRENT_LOCAL_BYTES"
    except OSError:
        return None, "CUSTODY_PATH_UNREADABLE"


def _load_census_records() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    aggregate = _load(CENSUS_DIR / "aggregate_manifest.json")
    records: list[dict[str, Any]] = []
    batch_bindings: list[dict[str, Any]] = []
    for binding in aggregate["batch_manifests"]:
        path = CENSUS_DIR / f"{binding['batch_id']}_manifest.json"
        if _sha_path(path) != binding["batch_file_sha256"]:
            raise DiscoveryError(f"census batch hash mismatch: {path}")
        payload = _load(path)
        if payload["source_root_id"] != binding["source_root_id"]:
            raise DiscoveryError(f"census batch root mismatch: {path}")
        if len(payload["records"]) != binding["record_count"]:
            raise DiscoveryError(f"census batch count mismatch: {path}")
        records.extend(payload["records"])
        batch_bindings.append(
            {
                "batch_id": binding["batch_id"],
                "source_root_id": binding["source_root_id"],
                "record_count": binding["record_count"],
                "sha256": binding["batch_file_sha256"],
            }
        )
    if len(records) != aggregate["record_count"]:
        raise DiscoveryError("aggregate census record count mismatch")
    return records, batch_bindings


def _reviewed_record_ids() -> set[str]:
    result = _load(CLAIM_RESULT)
    return {row["record_id"] for row in result["source_review_records"]}


def _lineage_map() -> dict[str, str]:
    result = _load(LINEAGE_RESULT)
    output: dict[str, str] = {}
    for component in result["lineage_components"]:
        for record_id in component["record_ids"]:
            output[record_id] = component["lineage_component_id"]
    return output


def _internally_referenced_paths() -> set[str]:
    paths: set[str] = set()

    def visit(value: Any) -> None:
        if isinstance(value, dict):
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)
        elif isinstance(value, str) and "/" in value:
            candidate = value.replace("\\", "/")
            if not candidate.startswith("/") and ".." not in PurePosixPath(candidate).parts:
                paths.add(candidate)

    for path in CCFT_INPUTS:
        visit(_load(path))
    return paths


def _snapshot(
    records: list[dict[str, Any]], *, git_reader: GitBlobReader
) -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]]]:
    current: dict[str, dict[str, Any]] = {}
    by_root: dict[str, list[dict[str, Any]]] = defaultdict(list)
    root_unavailable: set[str] = set()
    for record in records:
        record_id = record["record_id"]
        if record.get("git_object_id"):
            digest = record.get("committed_blob_sha256")
            if not digest:
                data = git_reader.read(record["git_object_id"])
                digest = _sha(data)
            row = {
                "record_id": record_id,
                "normalized_relative_path": record["custody_relative_path"],
                "file_type": record["file_type"],
                "size": record["file_size"],
                "sha256": digest,
                "custody_classification": record["custody_class"],
                "availability_status": "IMMUTABLE_GIT_BLOB_AVAILABLE",
            }
        else:
            data, status = _read_local(record)
            if status == "SOURCE_ROOT_UNAVAILABLE":
                root_unavailable.add(record["source_root_id"])
            row = {
                "record_id": record_id,
                "normalized_relative_path": record["custody_relative_path"],
                "file_type": record["file_type"] if data is not None else "UNAVAILABLE",
                "size": len(data) if data is not None else 0,
                "sha256": _sha(data) if data is not None else None,
                "custody_classification": record["custody_class"],
                "availability_status": status,
            }
        current[record_id] = row
        by_root[record["source_root_id"]].append(row)

    root_rows: list[dict[str, Any]] = []
    for source_root_id in sorted(by_root):
        rows = sorted(
            by_root[source_root_id],
            key=lambda row: row["normalized_relative_path"].encode("utf-8"),
        )
        tuples = [
            {
                "normalized_relative_path": row["normalized_relative_path"],
                "file_type": row["file_type"],
                "size": row["size"],
                "sha256": row["sha256"],
                "custody_classification": row["custody_classification"],
            }
            for row in rows
        ]
        root_rows.append(
            {
                "source_root_id": source_root_id,
                "record_count": len(rows),
                "aggregate_byte_count": sum(row["size"] for row in rows),
                "snapshot_tuple_hash": _sha(jcs_bytes(tuples)),
                "unavailable_record_count": sum(
                    row["sha256"] is None for row in rows
                ),
                "root_availability_status": (
                    "SOURCE_ROOT_UNAVAILABLE"
                    if source_root_id in root_unavailable
                    else "SOURCE_ROOT_AVAILABLE"
                ),
            }
        )
    return root_rows, current


def _line_numbers(text: str, terms: Iterable[str]) -> dict[str, list[int]]:
    output: dict[str, list[int]] = {}
    lines = text.splitlines()
    for term in terms:
        folded = term.casefold()
        hits = [index for index, line in enumerate(lines, start=1) if folded in line.casefold()]
        if hits:
            output[term] = hits[:16]
    return output


def gate_text(
    text: str,
    *,
    branch_terms: dict[str, list[str]],
    contract_terms: list[str],
) -> dict[str, Any] | None:
    folded = text.casefold()
    branch_hits = {
        branch: [term for term in terms if term.casefold() in folded]
        for branch, terms in branch_terms.items()
    }
    branch_hits = {branch: hits for branch, hits in branch_hits.items() if hits}
    contract_hits = [term for term in contract_terms if term.casefold() in folded]
    signatures = [
        signature
        for signature, patterns in STRUCTURAL_PATTERNS.items()
        if any(pattern.search(text) for pattern in patterns)
    ]
    if not branch_hits:
        return None
    if not contract_hits and not signatures:
        return None
    term_lines = _line_numbers(
        text,
        [term for hits in branch_hits.values() for term in hits] + contract_hits,
    )
    return {
        "branch_term_hits": branch_hits,
        "contract_term_hits": contract_hits,
        "structural_signature_hits": signatures,
        "term_line_locations": term_lines,
        "match_basis": (
            "FROZEN_BRANCH_AND_CONTRACT_GATE"
            if contract_hits
            else "FROZEN_STRUCTURAL_SIGNATURE_GATE"
        ),
    }


def _priority(candidate: dict[str, Any]) -> tuple[Any, ...]:
    if candidate["structural_signature_hits"]:
        rank = 2
        label = "FROZEN_STRUCTURAL_SIGNATURE_MATCH"
    elif candidate["internally_referenced_by_retained_ccft_input"]:
        rank = 3
        label = "SOURCE_NAMED_BY_RETAINED_CCFT_INPUT"
    elif re.search(r"(?i)(conflict|correction|review|errat)", candidate["custody_relative_path"]):
        rank = 4
        label = "CONFLICT_OR_CORRECTION_SOURCE"
    elif candidate["source_classification"] in {
        "HISTORICAL_PROJECT_METADATA",
        "GENERATED_PROJECT_OUTPUT",
    }:
        rank = 5
        label = "DERIVED_OR_SUMMARY_CANDIDATE"
    else:
        rank = 6
        label = "DETERMINISTIC_STRATIFIED_REMAINDER"
    if candidate["previously_deep_reviewed"]:
        rank += 10
        label = "PREVIOUSLY_REVIEWED_FALLBACK_" + label
    candidate["selection_priority_class"] = label
    branch_key = candidate["branch_ids"][0]
    return (
        rank,
        branch_key,
        SOURCE_CLASS_ORDER.get(candidate["source_classification"], 9),
        candidate["lineage_id"],
        candidate["custody_relative_path"].encode("utf-8"),
        candidate["verified_sha256"],
    )


def _compare_snapshots(
    initial: list[dict[str, Any]], final: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    initial_map = {row["source_root_id"]: row for row in initial}
    final_map = {row["source_root_id"]: row for row in final}
    output: list[dict[str, Any]] = []
    for source_root_id in sorted(initial_map):
        before = initial_map[source_root_id]
        after = final_map[source_root_id]
        stable = before["snapshot_tuple_hash"] == after["snapshot_tuple_hash"]
        output.append(
            {
                "source_root_id": source_root_id,
                "initial_file_count": before["record_count"],
                "final_file_count": after["record_count"],
                "initial_aggregate_byte_count": before["aggregate_byte_count"],
                "final_aggregate_byte_count": after["aggregate_byte_count"],
                "initial_snapshot_tuple_hash": before["snapshot_tuple_hash"],
                "final_snapshot_tuple_hash": after["snapshot_tuple_hash"],
                "initial_unavailable_record_count": before["unavailable_record_count"],
                "final_unavailable_record_count": after["unavailable_record_count"],
                "files_added_during_execution": [],
                "files_removed_during_execution": [],
                "files_changed_during_execution": [],
                "stability_status": (
                    "SOURCE_ROOT_SNAPSHOT_STABLE"
                    if stable
                    else "SOURCE_ROOT_MUTATED_DURING_TARGETED_RECOVERY"
                ),
            }
        )
    return output


def execute(*, captured_at_utc: str, open_commit: str) -> dict[str, Any]:
    if RESULT_PATH.exists():
        raise DiscoveryError(f"result already exists: {RESULT_PATH}")
    if PASS_MARKER.exists():
        raise DiscoveryError("the single targeted content pass is already consumed")

    manifest = _load(MANIFEST)
    open_event = _load(OPEN_EVENT)
    if (
        manifest["program_id"] != PROGRAM_ID
        or open_event["program_id"] != PROGRAM_ID
        or open_event["semantic_stage_id"] != STAGE_ID
        or open_event["target"] != TARGET
    ):
        raise DiscoveryError("installed manifest or OPEN event does not authorize this pass")
    if open_event["scope_hash"] != manifest["stages"][0]["canonical_scope_hash"]:
        raise DiscoveryError("Stage-1 scope hash mismatch")
    head_ancestors = subprocess.run(
        ["git", "merge-base", "--is-ancestor", open_commit, "HEAD"],
        cwd=REPO_ROOT,
        check=False,
    )
    if head_ancestors.returncode != 0:
        raise DiscoveryError("the immutable OPEN commit is not an ancestor of HEAD")

    controls = manifest["workload_caps"]
    search = manifest["deterministic_search_contract"]
    records, batch_bindings = _load_census_records()
    reviewed = _reviewed_record_ids()
    lineage = _lineage_map()
    referenced_paths = _internally_referenced_paths()

    PASS_MARKER.parent.mkdir(parents=True, exist_ok=True)
    PASS_MARKER.write_bytes(
        _pretty_bytes(
            {
                "program_id": PROGRAM_ID,
                "semantic_stage_id": STAGE_ID,
                "content_pass_number": 1,
                "status": "CONSUMED_AT_PASS_START",
                "captured_at_utc": captured_at_utc,
                "open_commit": open_commit,
            }
        )
    )

    with GitBlobReader() as git_reader:
        initial_roots, initial_current = _snapshot(records, git_reader=git_reader)
        root_unavailable = any(
            row["root_availability_status"] == "SOURCE_ROOT_UNAVAILABLE"
            for row in initial_roots
        )

        identity_groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
        unavailable: list[dict[str, Any]] = []
        unsupported: list[dict[str, Any]] = []
        for record in records:
            current = initial_current[record["record_id"]]
            if current["sha256"] is None:
                unavailable.append(
                    {
                        "record_id": record["record_id"],
                        "source_root_id": record["source_root_id"],
                        "custody_relative_path": record["custody_relative_path"],
                        "status": current["availability_status"],
                    }
                )
                continue
            if not record.get("eligibility_for_deeper_review", False):
                continue
            extension = str(record["file_type"]).casefold()
            if extension not in SUPPORTED_TEXT_EXTENSIONS:
                unsupported.append(
                    {
                        "record_id": record["record_id"],
                        "source_root_id": record["source_root_id"],
                        "custody_relative_path": record["custody_relative_path"],
                        "file_type": record["file_type"],
                        "status": (
                            "METADATA_ONLY_NO_ACTIVE_CONTENT"
                            if extension in METADATA_ONLY_EXTENSIONS
                            else "UNSUPPORTED_FORMAT_PRESERVED"
                        ),
                    }
                )
                continue
            if current["size"] > manifest["passive_content_contract"]["maximum_file_size_bytes"]:
                unsupported.append(
                    {
                        "record_id": record["record_id"],
                        "source_root_id": record["source_root_id"],
                        "custody_relative_path": record["custody_relative_path"],
                        "file_type": record["file_type"],
                        "status": "FILE_SIZE_LIMIT_EXCEEDED",
                    }
                )
                continue
            identity_groups[current["sha256"]].append(record)

        candidates: list[dict[str, Any]] = []
        candidate_text: dict[str, str] = {}
        scanned_unique_bytes = 0
        scanned_unique_content = 0
        parser_failures: list[dict[str, Any]] = []
        duplicate_groups: list[dict[str, Any]] = []
        max_text_per_file = controls["maximum_extracted_text_bytes_per_file"]
        for digest in sorted(identity_groups):
            aliases = sorted(identity_groups[digest], key=lambda row: row["record_id"])
            representative = sorted(
                aliases,
                key=lambda row: (
                    0 if row.get("git_object_id") else 1,
                    row["record_id"],
                ),
            )[0]
            if representative.get("git_object_id"):
                data = git_reader.read(representative["git_object_id"])
            else:
                data, status = _read_local(representative)
                if data is None:
                    parser_failures.append(
                        {
                            "record_id": representative["record_id"],
                            "status": status,
                        }
                    )
                    continue
            if _sha(data) != digest:
                raise DiscoveryError(
                    f"content identity changed after initial snapshot: {representative['record_id']}"
                )
            scanned_unique_bytes += len(data)
            scanned_unique_content += 1
            text_bytes = data[:max_text_per_file]
            text = text_bytes.decode("utf-8", errors="replace")
            gate = gate_text(
                text,
                branch_terms=search["branch_terms"],
                contract_terms=search["contract_terms"],
            )
            if gate is None:
                continue
            candidate_text[digest] = text
            if len(aliases) > 1:
                duplicate_groups.append(
                    {
                        "verified_sha256": digest,
                        "primary_record_id": representative["record_id"],
                        "alias_record_ids": [row["record_id"] for row in aliases],
                        "path_count": len(aliases),
                        "independent_support_count": 1,
                    }
                )
            for record in aliases:
                current = initial_current[record["record_id"]]
                candidates.append(
                    {
                        "record_id": record["record_id"],
                        "source_root_id": record["source_root_id"],
                        "custody_relative_path": record["custody_relative_path"],
                        "custody_class": record["custody_class"],
                        "source_classification": record["source_classification"],
                        "source_lineage_status": record.get("source_lineage"),
                        "lineage_id": lineage.get(record["record_id"], f"SINGLETON:{record['record_id']}"),
                        "file_type": record["file_type"],
                        "file_size": current["size"],
                        "git_object_id": record.get("git_object_id"),
                        "verified_sha256": digest,
                        "previously_deep_reviewed": record["record_id"] in reviewed,
                        "internally_referenced_by_retained_ccft_input": record["custody_relative_path"] in referenced_paths,
                        "portable_in_normal_git_history": bool(record.get("git_object_id")),
                        "local_custody_limitation": not bool(record.get("git_object_id")),
                        "branch_ids": sorted(gate["branch_term_hits"]),
                        **gate,
                    }
                )

        candidates.sort(key=_priority)
        raw_candidate_count = len(candidates)
        metadata_candidates = candidates[: controls["maximum_metadata_candidates"]]
        metadata_overflow = candidates[controls["maximum_metadata_candidates"] :]

        selected: list[dict[str, Any]] = []
        selected_identities: set[str] = set()
        branch_counts: Counter[str] = Counter()
        lineage_counts: Counter[str] = Counter()
        selected_file_bytes = 0
        selected_text_bytes = 0
        selection_overflow: list[dict[str, Any]] = []
        for candidate in metadata_candidates:
            identity = candidate["verified_sha256"]
            if identity in selected_identities:
                continue
            allocation_branch = next(
                (
                    branch
                    for branch in candidate["branch_ids"]
                    if branch_counts[branch]
                    < controls["maximum_deep_review_files_per_branch"]
                ),
                None,
            )
            text = candidate_text[identity]
            capture_bytes = len(text.encode("utf-8"))
            reason = None
            if allocation_branch is None:
                reason = "BRANCH_FILE_CAP"
            elif lineage_counts[candidate["lineage_id"]] >= controls["maximum_deep_review_files_per_lineage"]:
                reason = "LINEAGE_FILE_CAP"
            elif len(selected) >= controls["maximum_deep_review_files"]:
                reason = "TOTAL_FILE_CAP"
            elif selected_file_bytes + candidate["file_size"] > controls["maximum_total_deep_review_bytes"]:
                reason = "TOTAL_FILE_BYTE_CAP"
            elif selected_text_bytes + capture_bytes > controls["maximum_total_extracted_text_bytes"]:
                reason = "TOTAL_EXTRACTED_TEXT_CAP"
            if reason:
                selection_overflow.append(
                    {
                        "record_id": candidate["record_id"],
                        "verified_sha256": identity,
                        "reason": reason,
                    }
                )
                continue
            selected_identities.add(identity)
            branch_counts[allocation_branch] += 1
            lineage_counts[candidate["lineage_id"]] += 1
            selected_file_bytes += candidate["file_size"]
            selected_text_bytes += capture_bytes
            selected.append(
                {
                    **candidate,
                    "allocation_branch": allocation_branch,
                    "passive_text_capture": text,
                    "passive_text_capture_sha256": _sha(text.encode("utf-8")),
                    "passive_text_capture_bytes": capture_bytes,
                    "capture_truncated_at_frozen_limit": candidate["file_size"] > max_text_per_file,
                    "scientific_contract_interpretation_performed": False,
                }
            )

        selected_record_ids = {row["record_id"] for row in selected}
        candidate_ledger = [
            {
                **candidate,
                "selected_for_stage_2": candidate["record_id"] in selected_record_ids,
            }
            for candidate in metadata_candidates
        ]

        final_roots, _ = _snapshot(records, git_reader=git_reader)

    comparisons = _compare_snapshots(initial_roots, final_roots)
    roots_stable = all(
        row["stability_status"] == "SOURCE_ROOT_SNAPSHOT_STABLE"
        for row in comparisons
    )
    if root_unavailable:
        terminal = "SOURCE_ROOT_OR_CUSTODY_UNAVAILABLE"
        lifecycle = "BLOCKED"
    elif not roots_stable:
        terminal = "SOURCE_ROOT_MUTATED_DURING_TARGETED_RECOVERY"
        lifecycle = "BLOCKED"
    elif selected:
        terminal = "TARGETED_CCFT_SOURCE_SET_BOUND"
        lifecycle = "PASSED"
    else:
        terminal = "NO_TARGETED_CCFT_SOURCE_CANDIDATES_FOUND"
        lifecycle = "PASSED"

    result = {
        "artifact_id": "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_v0",
        "schema_id": "toe.targeted_ccft_closure.source_discovery_and_custody.result.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "semantic_stage_id": STAGE_ID,
        "attempt_sequence_number": 1,
        "scientific_target": TARGET,
        "scope_hash": open_event["scope_hash"],
        "open_event": {
            "path": OPEN_EVENT.relative_to(REPO_ROOT).as_posix(),
            "sha256": _sha_path(OPEN_EVENT),
            "event_hash": open_event["event_hash"],
            "open_commit": open_commit,
        },
        "input_bindings": {
            "manifest": {
                "path": MANIFEST.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha_path(MANIFEST),
                "manifest_hash": manifest["manifest_hash"],
            },
            "census_aggregate": {
                "path": (CENSUS_DIR / "aggregate_manifest.json").relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha_path(CENSUS_DIR / "aggregate_manifest.json"),
            },
            "census_batches": batch_bindings,
        },
        "single_content_pass": {
            "authorized_pass_limit": manifest["targeted_content_search_pass_limit"],
            "passes_consumed": 1,
            "pass_scope": "ALL_ELIGIBLE_UNIQUE_CONTENT_IDENTITIES_IN_THE_IMMUTABLE_13563_RECORD_CENSUS_POPULATION",
            "metadata_hashing_does_not_consume_the_content_pass": True,
            "selected_content_captured_for_later_stage_reuse": True,
            "second_search_authorized": False,
            "unique_content_identities_scanned": scanned_unique_content,
            "unique_content_bytes_streamed": scanned_unique_bytes,
        },
        "source_root_snapshot_records": comparisons,
        "source_inventory_summary": {
            "census_record_count": len(records),
            "authorized_root_count": len(initial_roots),
            "all_roots_stable": roots_stable,
            "unavailable_custody_record_count": len(unavailable),
            "snapshot_scope": "IMMUTABLE_STAGE_1_CENSUS_RECORD_POPULATION_WITH_CURRENT_LOCAL_BYTE_REVERIFICATION",
            "absolute_paths_and_timestamps_excluded": True,
        },
        "deterministic_candidate_discovery": {
            "candidate_gate": search["candidate_gate"],
            "branch_terms": search["branch_terms"],
            "contract_terms": search["contract_terms"],
            "structural_signatures": search["structural_signatures"],
            "selection_priority": search["selection_priority"],
            "tie_breaking_rule": search["tie_breaking_rule"],
            "raw_candidate_path_count": raw_candidate_count,
            "metadata_candidate_count": len(metadata_candidates),
            "metadata_candidate_overflow_count": len(metadata_overflow),
            "selected_unique_content_count": len(selected),
            "selected_source_bytes": selected_file_bytes,
            "selected_extracted_text_bytes": selected_text_bytes,
            "selected_by_branch": dict(sorted(branch_counts.items())),
            "selection_overflow_count": len(selection_overflow),
            "manual_preference_affected_selection": False,
        },
        "workload_cap_accounting": {
            "maximum_metadata_candidates": controls["maximum_metadata_candidates"],
            "metadata_candidates_retained": len(metadata_candidates),
            "maximum_deep_review_files": controls["maximum_deep_review_files"],
            "deep_review_files_selected": len(selected),
            "maximum_deep_review_files_per_branch": controls["maximum_deep_review_files_per_branch"],
            "maximum_selected_in_any_branch": max(branch_counts.values(), default=0),
            "maximum_deep_review_files_per_lineage": controls["maximum_deep_review_files_per_lineage"],
            "maximum_selected_in_any_lineage": max(lineage_counts.values(), default=0),
            "maximum_total_deep_review_bytes": controls["maximum_total_deep_review_bytes"],
            "selected_source_bytes": selected_file_bytes,
            "maximum_total_extracted_text_bytes": controls["maximum_total_extracted_text_bytes"],
            "selected_extracted_text_bytes": selected_text_bytes,
            "maximum_parser_failures": controls["maximum_parser_failures"],
            "selected_parser_failure_count": len(parser_failures),
            "maximum_unsupported_format_files": controls["maximum_unsupported_format_files"],
            "selected_unsupported_format_file_count": 0,
            "inventory_visible_metadata_only_or_unsupported_count": len(unsupported),
            "inventory_visible_excluded_records_do_not_count_against_deep_review_budget": True,
            "all_scientific_selection_caps_respected": True,
        },
        "candidate_source_ledger": candidate_ledger,
        "selected_source_ledger": selected,
        "overflow_ledger": {
            "metadata_candidate_overflow": [
                {
                    "record_id": row["record_id"],
                    "verified_sha256": row["verified_sha256"],
                    "reason": "MAXIMUM_METADATA_CANDIDATES",
                }
                for row in metadata_overflow
            ],
            "deep_review_selection_overflow": selection_overflow,
        },
        "exact_duplicate_ledger": duplicate_groups,
        "unsupported_or_parser_status_ledger": {
            "unsupported_or_metadata_only_count": len(unsupported),
            "parser_failure_count": len(parser_failures),
            "unsupported_or_metadata_only_records": unsupported,
            "parser_failures": parser_failures,
            "unavailable_records": unavailable,
        },
        "stage_2_handoff": {
            "selected_target": (
                "extract_toe_targeted_ccft_closure_contracts_v0"
                if lifecycle == "PASSED" and selected
                else manifest["mandatory_exit"]["target"]
            ),
            "stage_2_authorized": False,
            "contract_extraction_performed": False,
            "captured_text_may_be_reused_only_after_separate_stage_2_open": True,
        },
        "nonclaim_boundary": {
            "closure_contract_recovered_or_rejected": False,
            "equation_repaired_or_reconciled": False,
            "parameter_boundary_condition_or_invariant_inferred": False,
            "cp_nlse_or_lcrd_selected_as_ccft_v0": False,
            "new_ccft_postulate_inserted": False,
            "ccft_v0_constructed": False,
            "evidence_promoted": False,
            "repository_claim_exhaustion_established": False,
        },
        "terminal_outcome": terminal,
        "lifecycle_result": lifecycle,
        "status": "STAGE_1_RESULT_READY_FOR_INDEPENDENT_REVIEW",
    }
    RESULT_PATH.write_bytes(_pretty_bytes(result))
    marker = _load(PASS_MARKER)
    marker["status"] = "CONSUMED_AND_RESULT_WRITTEN"
    marker["result_path"] = RESULT_PATH.relative_to(REPO_ROOT).as_posix()
    marker["result_sha256"] = _sha_path(RESULT_PATH)
    PASS_MARKER.write_bytes(_pretty_bytes(marker))
    return result


def normalize_existing_result_for_close() -> dict[str, Any]:
    """Apply reporting-only cap clarification after the pass, without rereading sources."""
    if not RESULT_PATH.is_file() or not PASS_MARKER.is_file():
        raise DiscoveryError("existing result and consumed-pass marker are required")
    result = _load(RESULT_PATH)
    controls = _load(MANIFEST)["workload_caps"]
    for ledger_name in ("candidate_source_ledger", "selected_source_ledger"):
        for row in result[ledger_name]:
            if row.get("selection_priority_class") == "SOURCE_WITH_UNIQUE_STRUCTURAL_SIGNATURE":
                row["selection_priority_class"] = "FROZEN_STRUCTURAL_SIGNATURE_MATCH"
    discovery = result["deterministic_candidate_discovery"]
    selected = result["selected_source_ledger"]
    branch_counts = Counter(row["allocation_branch"] for row in selected)
    lineage_counts = Counter(row["lineage_id"] for row in selected)
    statuses = result["unsupported_or_parser_status_ledger"]
    result["workload_cap_accounting"] = {
        "maximum_metadata_candidates": controls["maximum_metadata_candidates"],
        "metadata_candidates_retained": discovery["metadata_candidate_count"],
        "maximum_deep_review_files": controls["maximum_deep_review_files"],
        "deep_review_files_selected": len(selected),
        "maximum_deep_review_files_per_branch": controls["maximum_deep_review_files_per_branch"],
        "maximum_selected_in_any_branch": max(branch_counts.values(), default=0),
        "maximum_deep_review_files_per_lineage": controls["maximum_deep_review_files_per_lineage"],
        "maximum_selected_in_any_lineage": max(lineage_counts.values(), default=0),
        "maximum_total_deep_review_bytes": controls["maximum_total_deep_review_bytes"],
        "selected_source_bytes": discovery["selected_source_bytes"],
        "maximum_total_extracted_text_bytes": controls["maximum_total_extracted_text_bytes"],
        "selected_extracted_text_bytes": discovery["selected_extracted_text_bytes"],
        "maximum_parser_failures": controls["maximum_parser_failures"],
        "selected_parser_failure_count": statuses["parser_failure_count"],
        "maximum_unsupported_format_files": controls["maximum_unsupported_format_files"],
        "selected_unsupported_format_file_count": 0,
        "inventory_visible_metadata_only_or_unsupported_count": statuses["unsupported_or_metadata_only_count"],
        "inventory_visible_excluded_records_do_not_count_against_deep_review_budget": True,
        "all_scientific_selection_caps_respected": True,
    }
    result["reporting_clarification"] = {
        "source_content_reread": False,
        "candidate_or_selected_set_changed": False,
        "reason": "Distinguish frozen structural-signature matches from literal source uniqueness and distinguish inventory-visible excluded formats from selected deep-review files.",
    }
    RESULT_PATH.write_bytes(_pretty_bytes(result))
    marker = _load(PASS_MARKER)
    marker["result_sha256"] = _sha_path(RESULT_PATH)
    marker["reporting_normalization_applied"] = True
    PASS_MARKER.write_bytes(_pretty_bytes(marker))
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run the single authorized targeted CCFT Stage-1 content pass."
    )
    parser.add_argument("--captured-at-utc", required=True)
    parser.add_argument("--open-commit", required=True)
    parser.add_argument("--normalize-existing-result-for-close", action="store_true")
    args = parser.parse_args(argv)
    if args.normalize_existing_result_for_close:
        result = normalize_existing_result_for_close()
    else:
        result = execute(
            captured_at_utc=args.captured_at_utc,
            open_commit=args.open_commit,
        )
    print(
        json.dumps(
            {
                "result": result["terminal_outcome"],
                "candidates": result["deterministic_candidate_discovery"]["raw_candidate_path_count"],
                "selected": result["deterministic_candidate_discovery"]["selected_unique_content_count"],
                "result_path": RESULT_PATH.relative_to(REPO_ROOT).as_posix(),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
