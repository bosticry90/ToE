from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PAPER_DOCS_DIR = REPO_ROOT / "formal/docs/paper"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
REPORT_PATH = (
    REPO_ROOT
    / "formal/output/validation_profiles/"
    "HISTORICAL_CROSS_REFERENCE_DEBT_20260725_v0.json"
)
CURRENT_AUTHORITY = REPO_ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
CURRENT_ROOTS = (
    REPO_ROOT / "formal/docs/release/CURRENT_AUTHORITY_REACHABILITY_ROOTS_20260725_v0.json"
)
REGISTRY = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
_LINKED_FILE_PATTERN = re.compile(
    r"(?P<path>(?:formal/docs/paper/|formal/docs/release/|formal/output/|"
    r"State_of_the_Theory\.md|ARCHITECTURE_SCHEMA_v1\.json|"
    r"GOVERNANCE_VERSION_v2\.lock|README\.md|governance_suite\.ps1|py\.ps1)"
    r"[^`\s]*\.(?:md|json|lock|ps1))"
)
_MARKDOWN_LINK_PATTERN = re.compile(
    r"\]\((?P<path>(?!https?://|file://)[^)]+)\)",
    flags=re.IGNORECASE,
)


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_bytes())
    if not isinstance(payload, dict):
        raise ValueError(f"JSON root must be an object: {path}")
    return payload


def _extract_references(text: str) -> set[str]:
    refs: set[str] = set()
    for pattern in (_LINKED_FILE_PATTERN, _MARKDOWN_LINK_PATTERN):
        for match in pattern.finditer(text):
            for part in match.group("path").split(";"):
                cleaned = part.strip()
                if cleaned:
                    refs.add(cleaned)
    return refs


def _is_candidate(ref: str) -> bool:
    return (
        bool(ref)
        and not any(token in ref for token in ("<", ">", "{", "}", "*"))
        and (
            ref.startswith(
                (
                    "formal/docs/paper/",
                    "formal/docs/release/",
                    "formal/output/",
                    "./",
                    "../",
                )
            )
            or ref
            in {
                "State_of_the_Theory.md",
                "ARCHITECTURE_SCHEMA_v1.json",
                "GOVERNANCE_VERSION_v2.lock",
                "README.md",
                "governance_suite.ps1",
                "py.ps1",
            }
        )
    )


def _resolve(ref: str, source: Path) -> Path:
    cleaned = ref.strip().strip("`\"'")
    cleaned = cleaned.split("#", 1)[0].split("?", 1)[0].rstrip(".,;:)")
    cleaned = cleaned.replace("\\_", "_")
    if cleaned.startswith(("./", "../")):
        return (source.parent / cleaned).resolve()
    return (REPO_ROOT / cleaned).resolve()


def missing_references(sources: Iterable[tuple[str, Path, str]]) -> list[dict[str, str]]:
    missing: list[dict[str, str]] = []
    for label, source, text in sources:
        for ref in sorted(_extract_references(text)):
            if _is_candidate(ref) and not _resolve(ref, source).exists():
                missing.append({"source": label, "target": ref})
    return sorted(missing, key=lambda row: (row["source"], row["target"]))


def current_sources() -> list[tuple[str, Path, str]]:
    roots = load_json(CURRENT_ROOTS)
    registry = load_json(REGISTRY)
    paths = [
        CURRENT_AUTHORITY,
        CURRENT_ROOTS,
        *[
            REPO_ROOT / path
            for path in roots["current_scientific_evidence_roots"]
        ],
    ]
    sources = [
        (
            path.relative_to(REPO_ROOT).as_posix(),
            path,
            path.read_text(encoding="utf-8", errors="replace"),
        )
        for path in paths
    ]
    sources.append(
        (
            "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json#/current_projection_v0",
            REGISTRY,
            json.dumps(registry["current_projection_v0"], sort_keys=True),
        )
    )
    return sources


def historical_sources() -> list[tuple[str, Path, str]]:
    paths = [
        *sorted(PAPER_DOCS_DIR.rglob("*.md")),
        *sorted(PAPER_DOCS_DIR.rglob("*.json")),
        STATE_PATH,
    ]
    return [
        (
            path.relative_to(REPO_ROOT).as_posix(),
            path,
            path.read_text(encoding="utf-8", errors="replace"),
        )
        for path in paths
    ]


def build_report() -> dict[str, Any]:
    current_missing = missing_references(current_sources())
    historical_missing = missing_references(historical_sources())
    source_counts: dict[str, int] = {}
    for row in historical_missing:
        source_counts[row["source"]] = source_counts.get(row["source"], 0) + 1
    return {
        "schema_id": "HISTORICAL_CROSS_REFERENCE_DEBT_20260725_v0",
        "current_relative_to_commit": "380db2de3aca8c19fdf1ab9c43d0e6629d232009",
        "current_reference_missing_count": len(current_missing),
        "current_reference_missing": current_missing,
        "historical_missing_count": len(historical_missing),
        "historical_source_count": len(source_counts),
        "historical_missing_by_source": dict(sorted(source_counts.items())),
        "historical_missing": historical_missing,
        "disposition": "HISTORICAL_QUARANTINED_VISIBLE",
        "historical_reports_restored": 0,
        "current_verdict_affected": False,
        "scientific_posture": "B-BLOCKED"
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_report())
    if args.write:
        REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REPORT_PATH.write_bytes(raw)
    elif args.check:
        if not REPORT_PATH.is_file() or REPORT_PATH.read_bytes() != raw:
            raise ValueError("historical cross-reference debt report is stale")
    else:
        print(raw.decode("utf-8"), end="")
    print(
        json.dumps(
            {
                "sha256": hashlib.sha256(raw).hexdigest(),
                "path": REPORT_PATH.relative_to(REPO_ROOT).as_posix(),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
