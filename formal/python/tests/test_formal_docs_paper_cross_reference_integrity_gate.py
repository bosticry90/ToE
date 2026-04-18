from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


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
    source_files = sorted(PAPER_DOCS_DIR.rglob("*.md"))
    source_files.extend(sorted(PAPER_DOCS_DIR.rglob("*.json")))
    source_files.append(STATE_PATH)

    missing: list[str] = []
    for source in source_files:
        text = _read(source)
        for ref in sorted(_extract_references(text)):
            if not _is_reference_candidate(ref):
                continue
            if not (
                ref.startswith("formal/docs/paper/")
                or ref.startswith("formal/docs/release/")
                or ref.startswith("formal/output/")
                or ref.startswith("./")
                or ref.startswith("../")
                or ref in {
                    "State_of_the_Theory.md",
                    "ARCHITECTURE_SCHEMA_v1.json",
                    "GOVERNANCE_VERSION_v2.lock",
                    "README.md",
                    "governance_suite.ps1",
                    "py.ps1",
                }
            ):
                continue

            resolved = _normalize_reference(ref, source)
            if not resolved.exists():
                missing.append(f"{source.relative_to(REPO_ROOT)} -> {ref}")

    assert not missing, "Unresolved cross-reference(s):\n- " + "\n- ".join(missing)
