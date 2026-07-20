from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


AUDITED_DIRTY_RESULT = {
    "source": "preserved_read_only_audit_summary",
    "rerun": False,
    "status": "NOT_RERUN_TO_PRESERVE_AUDITED_WORKTREE",
    "passed": 1756,
    "skipped": 22,
    "failed": 14,
    "errors": 6,
    "stopped_after_failures_or_errors": 20,
    "complete": False,
}

SUMMARY_PATTERNS = {
    "passed": re.compile(r"(?P<count>\d+) passed"),
    "skipped": re.compile(r"(?P<count>\d+) skipped"),
    "failed": re.compile(r"(?P<count>\d+) failed"),
    "errors": re.compile(r"(?P<count>\d+) errors?"),
    "xfailed": re.compile(r"(?P<count>\d+) xfailed"),
    "xpassed": re.compile(r"(?P<count>\d+) xpassed"),
    "warnings": re.compile(r"(?P<count>\d+) warnings?"),
}
NODE_PATTERN = re.compile(r"^(FAILED|ERROR)\s+([^\s]+)", re.MULTILINE)
EXCEPTION_LINE_PATTERN = re.compile(r"^E\s+(.+)$", re.MULTILINE)
REPORT_HEADER_PATTERN = re.compile(r"^_+\s+(.+?)\s+_+$")


class BaselineResultError(RuntimeError):
    pass


def _canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_status(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    result: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            result[key] = value
    return result


def _summary(text: str) -> dict[str, int]:
    result = {key: 0 for key in SUMMARY_PATTERNS}
    tail = "\n".join(text.splitlines()[-100:])
    for key, pattern in SUMMARY_PATTERNS.items():
        matches = list(pattern.finditer(tail))
        if matches:
            result[key] = int(matches[-1].group("count"))
    return result


def _root_cause(nodeid: str, text: str) -> tuple[str, list[str]]:
    lowered = nodeid.casefold()
    if "conftest_signature" in lowered:
        return "COMMITTED_SOURCE_DEFECT", [
            "formal/python/tests/conftest.py",
            "formal/docs/release/CONFTEST_STABILITY_PROTOCOL_v0.md",
        ]
    if "archive_quarantine" in lowered or "no_archive_imports" in lowered:
        return "COMMITTED_SOURCE_DEFECT", [
            "formal/python/tests/test_archive_quarantine_enforcement.py"
        ]
    if "canonical_environment" in lowered or "environment_identity" in lowered:
        return "ENVIRONMENT_OR_TOOLCHAIN_DRIFT", []
    if "canonical_parameter_freeze" in lowered or "canonical_simulation" in lowered:
        return "COMMITTED_SOURCE_DEFECT", []
    if "non_authoritative_pilot" in lowered and (
        "output" in lowered or "artifact" in lowered
    ):
        return "OBSOLETE_STATEFUL_TEST", []
    return "UNRESOLVED", []


def _exception_index(text: str) -> dict[str, str]:
    """Index pytest exception lines in one pass over a terminal report."""

    result: dict[str, str] = {}
    active_names: list[str] = []
    for line in text.splitlines():
        header = REPORT_HEADER_PATTERN.match(line)
        if header:
            label = header.group(1).strip()
            for prefix in ("ERROR at setup of ", "ERROR at teardown of "):
                if label.startswith(prefix):
                    label = label[len(prefix) :]
            exact = label.strip()
            base = exact.split("[", 1)[0]
            active_names = [exact, base]
            continue
        if active_names and line.startswith("E "):
            message = line[2:].strip()
            for name in active_names:
                result.setdefault(name, message)
            active_names = []
    return result


def _first_exception(
    nodeid: str, text: str, *, index: dict[str, str] | None = None
) -> str:
    """Return the first pytest exception line associated with a node when possible.

    Pytest's terminal report is not a machine-readable custody format, so this is a
    conservative extraction.  It never invents an exception: when the report cannot
    be associated unambiguously, the row records that manual log review is required.
    """

    exact_name = nodeid.rsplit("::", 1)[-1]
    test_name = exact_name.split("[", 1)[0]
    if index is not None:
        return index.get(exact_name, index.get(test_name, "NOT_EXTRACTED_REQUIRES_RAW_LOG_REVIEW"))
    escaped = re.escape(test_name)
    headers = (
        re.compile(rf"^_+\s+{escaped}\s+_+$", re.MULTILINE),
        re.compile(rf"^_+\s+ERROR at .*\b{escaped}\b.*_+$", re.MULTILINE),
    )
    starts = [match.end() for pattern in headers for match in pattern.finditer(text)]
    if starts:
        start = min(starts)
        following_header = re.search(r"^(?:_+|=+)\s+.*(?:_+|=+)\s*$", text[start:], re.MULTILINE)
        end = start + following_header.start() if following_header else len(text)
        match = EXCEPTION_LINE_PATTERN.search(text[start:end])
        if match:
            return match.group(1).strip()
    return "NOT_EXTRACTED_REQUIRES_RAW_LOG_REVIEW"


def build_result(baseline_dir: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    full_log = baseline_dir / "full_pytest.log"
    full_status = _read_status(baseline_dir / "full_pytest.status.txt")
    text = full_log.read_text(encoding="utf-8", errors="replace") if full_log.exists() else ""
    counts = _summary(text)
    exit_value = full_status.get("EXIT")
    timed_out = full_status.get("TIMEOUT", "FALSE").upper() == "TRUE" or exit_value == "124"
    completed = bool(
        exit_value is not None
        and not timed_out
        and "KeyboardInterrupt" not in text
    )
    nodes: list[dict[str, Any]] = []
    full_exception_index = _exception_index(text)
    seen: set[tuple[str, str]] = set()
    for kind, nodeid in NODE_PATTERN.findall(text):
        key = (kind, nodeid)
        if key in seen:
            continue
        seen.add(key)
        cause, source_paths = _root_cause(nodeid, text)
        test_path = nodeid.split("::", 1)[0]
        if test_path not in source_paths:
            source_paths = [test_path, *source_paths]
        nodes.append(
            {
                "test_id": nodeid,
                "outcome": kind,
                "exact_command": (
                    ".venv/Scripts/python.exe -B -m pytest -q -p no:cacheprovider "
                    "formal/python/tests"
                ),
                "first_exception": _first_exception(
                    nodeid, text, index=full_exception_index
                ),
                "root_cause_classification": cause,
                "relevant_source_paths": source_paths,
                "clean_result": kind,
                "audited_dirty_result": "NOT_RERUN_TO_PRESERVE_AUDITED_WORKTREE",
                "environment_dependence": cause == "ENVIRONMENT_OR_TOOLCHAIN_DRIFT",
                "preservation_implications": "NO_EVIDENCE_DELETION_AUTHORIZED",
                "required_repair_authority": "PHASE_B_MAINTENANCE_REPAIR",
            }
        )
    substitute_log = baseline_dir / "nonlean_inventory_pytest.log"
    substitute_text = (
        substitute_log.read_text(encoding="utf-8", errors="replace")
        if substitute_log.exists()
        else ""
    )
    substitute_status = _read_status(
        baseline_dir / "nonlean_inventory_pytest.status.txt"
    )
    substitute_counts = _summary(substitute_text)
    substitute_exception_index = _exception_index(substitute_text)
    substitute_nodes: list[dict[str, Any]] = []
    substitute_seen: set[tuple[str, str]] = set()
    for kind, nodeid in NODE_PATTERN.findall(substitute_text):
        key = (kind, nodeid)
        if key in substitute_seen:
            continue
        substitute_seen.add(key)
        cause, source_paths = _root_cause(nodeid, substitute_text)
        test_path = nodeid.split("::", 1)[0]
        if test_path not in source_paths:
            source_paths = [test_path, *source_paths]
        substitute_nodes.append(
            {
                "test_id": nodeid,
                "outcome": kind,
                "exact_command": "SEE_NONLEAN_INVENTORY_STATUS_AND_LOG",
                "first_exception": _first_exception(
                    nodeid,
                    substitute_text,
                    index=substitute_exception_index,
                ),
                "root_cause_classification": cause,
                "relevant_source_paths": source_paths,
                "clean_result": kind,
                "audited_dirty_result": "NOT_RERUN_TO_PRESERVE_AUDITED_WORKTREE",
                "environment_dependence": cause
                == "ENVIRONMENT_OR_TOOLCHAIN_DRIFT",
                "preservation_implications": "NO_EVIDENCE_DELETION_AUTHORIZED",
                "required_repair_authority": "PHASE_B_MAINTENANCE_REPAIR",
            }
        )
    commands: dict[str, Any] = {}
    for stem in (
        "pip_check",
        "conftest_gate",
        "governance_suite",
        "focused_gates",
        "v2_checks",
        "lean_committed",
        "lean_build",
    ):
        log = baseline_dir / f"{stem}.log"
        status = _read_status(baseline_dir / f"{stem}.status.txt")
        commands[stem] = {
            "log_present": log.exists(),
            "log_sha256": _sha(log) if log.exists() else None,
            "status": status,
        }
    commands["full_pytest"] = {
        "exact_command": (
            ".venv/Scripts/python.exe -B -m pytest -q -p no:cacheprovider "
            "formal/python/tests"
        ),
        "log_sha256": _sha(full_log) if full_log.exists() else None,
        "status": full_status,
        "counts": counts,
        "completed": completed,
        "exit_zero": exit_value == "0",
        "no_collection_errors": counts["errors"] == 0,
        "no_unexpected_xpass": counts["xpassed"] == 0,
    }
    commands["nonlean_inventory_pytest"] = {
        "status": substitute_status,
        "log_sha256": _sha(substitute_log) if substitute_log.exists() else None,
        "counts": substitute_counts,
        "complete": substitute_status.get("COMPLETE") == "TRUE"
        and substitute_status.get("EXIT") is not None,
        "excluded_lean_build_tests": int(
            substitute_status.get("EXCLUDED_LEAN_BUILD_TESTS", "0")
        ),
        "cannot_substitute_for_full_suite": True,
    }
    mutation_path = (
        baseline_dir.parent
        / "CLEAN_BASELINE_POST_VALIDATION_MUTATION_MANIFEST_v0.json"
    )
    mutation = (
        json.loads(mutation_path.read_text(encoding="utf-8"))
        if mutation_path.exists()
        else None
    )
    environment_path = baseline_dir / "environment.json"
    result = {
        "schema_id": "CLEAN_BASELINE_VALIDATION_RESULT_20260719_v0",
        "audited_commit": "75af1d110a57df26344ca151ccd26b9f5c1f7736",
        "clone_root": "C:/toe-b0",
        "ordinary_windows_checkout_without_longpaths": "FAILED_FILENAME_TOO_LONG",
        "short_path_checkout_with_core_longpaths": "PASS",
        "environment": (
            json.loads(environment_path.read_text(encoding="utf-8"))
            if environment_path.exists()
            else None
        ),
        "commands": commands,
        "full_suite_complete": completed,
        "full_suite_green": completed and exit_value == "0",
        "full_suite_timeout": timed_out,
        "bounded_nonlean_inventory_complete": commands[
            "nonlean_inventory_pytest"
        ]["complete"],
        "post_validation_mutation_manifest": mutation,
        "scientific_status_changed": False,
    }
    matrix = {
        "schema_id": "CLEAN_VS_AUDITED_FAILURE_MATRIX_20260719_v0",
        "audited_dirty_result": AUDITED_DIRTY_RESULT,
        "clean_failure_count": len(nodes),
        "rows": nodes,
        "complete_failure_population": completed,
        "all_failures_classified": completed
        and all(
            row["root_cause_classification"] != "UNRESOLVED" for row in nodes
        ),
        "bounded_substitute_rows": substitute_nodes,
        "bounded_substitute_failure_count": len(substitute_nodes),
        "bounded_substitute_complete": commands["nonlean_inventory_pytest"][
            "complete"
        ],
        "bounded_substitute_is_not_full_suite": True,
    }
    return result, matrix


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline-dir", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()
    result, matrix = build_result(args.baseline_dir)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "CLEAN_BASELINE_VALIDATION_RESULT_v0.json").write_bytes(
        _canonical(result)
    )
    (args.out_dir / "CLEAN_VS_AUDITED_FAILURE_MATRIX_v0.json").write_bytes(
        _canonical(matrix)
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
