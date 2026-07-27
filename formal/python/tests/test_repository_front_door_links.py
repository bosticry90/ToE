from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
MARKDOWN_LINK = re.compile(r"(?<!!)\[[^\]]+\]\(([^)]+)\)")
ENTRY_DOCUMENTS = (
    REPO_ROOT / "README.md",
    REPO_ROOT / "PROJECT_ENTRY_GUIDE.md",
)
REQUIRED_ENTRY_PATHS = (
    "README.md",
    "PROJECT_ENTRY_GUIDE.md",
    "DEVELOPMENT.md",
    "TOE_CLAIM_LADDER_v0.md",
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md",
    "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json",
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
    (
        "formal/docs/release/"
        "TOE_PLAIN_LANGUAGE_SCIENTIFIC_STATUS_BOUNDARY_SUMMARY_v0.md"
    ),
    (
        "formal/docs/release/"
        "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
        "CANONICAL_RESULT_REVIEW_20260715_v0.json"
    ),
    (
        "formal/docs/release/"
        "REPOSITORY_FRONT_DOOR_LINK_DISPOSITION_20260727_v0.json"
    ),
)
RETIRED_ROOT_PATHS = (
    "PUBLIC_OVERVIEW.md",
    "TECHNICAL_REPOSITORY_GUIDE.md",
    "MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md",
    "TOE_PUBLIC_RECAP_UNDER_5000_CHARS.md",
)


def _local_links(document: Path) -> list[Path]:
    links: list[Path] = []
    for target in MARKDOWN_LINK.findall(document.read_text(encoding="utf-8")):
        target = target.strip().split("#", 1)[0]
        if not target or "://" in target or target.startswith("mailto:"):
            continue
        links.append((document.parent / target).resolve())
    return links


def test_root_readme_and_entry_guide_links_resolve() -> None:
    for document in ENTRY_DOCUMENTS:
        assert document.is_file()
        links = _local_links(document)
        assert links
        missing = [
            path.relative_to(REPO_ROOT).as_posix()
            for path in links
            if not path.is_file()
        ]
        assert missing == []


def test_canonical_status_authority_and_public_entry_paths_exist() -> None:
    missing = [
        relative
        for relative in REQUIRED_ENTRY_PATHS
        if not (REPO_ROOT / relative).is_file()
    ]
    assert missing == []


def test_maintenance_pointer_resolves_to_hash_bound_authority() -> None:
    pointer = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json"
        ).read_text(encoding="utf-8")
    )
    authority = REPO_ROOT / pointer["current_authority_path"]
    assert authority.is_file()
    assert hashlib.sha256(authority.read_bytes()).hexdigest() == (
        pointer["current_authority_sha256"]
    )


def test_retired_front_door_paths_have_recorded_replacements() -> None:
    disposition = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/"
            "REPOSITORY_FRONT_DOOR_LINK_DISPOSITION_20260727_v0.json"
        ).read_text(encoding="utf-8")
    )
    records = {record["path"]: record for record in disposition["dispositions"]}
    assert set(records) == set(RETIRED_ROOT_PATHS)
    for path in RETIRED_ROOT_PATHS:
        assert not (REPO_ROOT / path).exists()
        record = records[path]
        assert record["disposition"] in {
            "RESTORE_AUTHORITATIVE_DOCUMENT",
            "REPLACE_WITH_SUCCESSOR",
            "CONSOLIDATE_AND_REDIRECT",
            "REMOVE_AS_RETIRED",
        }
        assert record["replacement_paths"]
        assert all(
            (REPO_ROOT / replacement).is_file()
            for replacement in record["replacement_paths"]
        )
