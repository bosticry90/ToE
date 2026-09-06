from __future__ import annotations

import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import historical_cross_reference_debt as debt


REPO_ROOT = find_repo_root(Path(__file__))
PAPER_DOCS_DIR = REPO_ROOT / "formal" / "docs" / "paper"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

_LINKED_FILE_PATTERN = re.compile(
    r"(?P<path>(?:formal/docs/paper/|formal/docs/release/|formal/output/|State_of_the_Theory\.md|ARCHITECTURE_SCHEMA_v1\.json|GOVERNANCE_VERSION_v2\.lock|README\.md|governance_suite\.ps1|py\.ps1)"
    r"[^`\s]*\.(?:md|json|lock|ps1))"
)

_MARKDOWN_LINK_PATTERN = re.compile(
    r"\]\((?P<path>(?!https?://|file://)[^)]+)\)",
    flags=re.IGNORECASE,
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _is_reference_candidate(path_text: str) -> bool:
    if "<" in path_text or ">" in path_text:
        return False
    if "{" in path_text or "}" in path_text:
        return False
    if "*" in path_text:
        return False
    if not path_text:
        return False
    return True


def _normalize_reference(ref: str, source: Path) -> Path:
    cleaned = ref.strip().strip("`\"'")
    cleaned = cleaned.split("#", 1)[0].split("?", 1)[0].rstrip(".,;:)")
    cleaned = cleaned.replace("\\_", "_")
    if cleaned.startswith("./") or cleaned.startswith("../"):
        return (source.parent / cleaned).resolve()
    return (REPO_ROOT / cleaned).resolve()


def _extract_references(text: str) -> set[str]:
    refs: set[str] = set()
    for match in _LINKED_FILE_PATTERN.finditer(text):
        raw = match.group("path")
        for part in raw.split(";"):
            part = part.strip()
            if part:
                refs.add(part)
    for match in _MARKDOWN_LINK_PATTERN.finditer(text):
        raw = match.group("path")
        for part in raw.split(";"):
            part = part.strip()
            if part:
                refs.add(part)
    return refs


def test_formal_docs_paper_and_state_cross_references_resolve() -> None:
    current_missing = debt.missing_references(debt.current_sources())
    assert current_missing == []
    report = debt.load_json(debt.REPORT_PATH)
    assert report == debt.build_report()
    assert report["current_reference_missing_count"] == 0
    assert report["historical_missing_count"] > 0
    assert report["reference_resolution_domain"] == "COMMITTED_GIT_PATHS_ONLY"
    assert report["disposition"] == "HISTORICAL_QUARANTINED_VISIBLE"
    assert report["historical_reports_restored"] == 0
    assert report["preserved_tranche_scientifically_adopted"] is False
    assert report["scientific_adoption_inferred"] is False
