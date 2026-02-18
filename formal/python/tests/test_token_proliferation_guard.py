from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
ASSUMPTION_REGISTRY_PATH = PAPER_DIR / "ASSUMPTION_REGISTRY_v1.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _latest_lock_path() -> Path:
    versioned: list[tuple[int, Path]] = []
    for path in REPO_ROOT.glob("GOVERNANCE_VERSION_v*.lock"):
        m = re.fullmatch(r"GOVERNANCE_VERSION_v(\d+)\.lock", path.name)
        if m is None:
            continue
        versioned.append((int(m.group(1)), path))
    assert versioned, "Missing governance lock file (expected GOVERNANCE_VERSION_v*.lock)."
    versioned.sort()
    return versioned[-1][1]


def _adjudication_values() -> set[str]:
    values: set[str] = set()
    paths = [STATE_PATH] + sorted(PAPER_DIR.glob("*.md"))
    for path in paths:
        text = _read(path)
        for m in re.finditer(r"\b[A-Z0-9_]+_ADJUDICATION\s*:\s*([^\n\r]+)", text):
            raw = m.group(1).strip()
            token_match = re.match(r"`?([A-Za-z0-9_<>\-_]+)`?", raw)
            if token_match is None:
                continue
            value = token_match.group(1)
            if value.startswith("<"):
                continue
            values.add(value)
    return values


def _adjudication_suffix_pattern(value: str) -> str:
    if value.startswith("DISCHARGED_v0_"):
        return "DISCHARGED_v0_*"
    if value.startswith("DISCHARGED_CONDITIONAL_PUBLISH_v"):
        return "DISCHARGED_CONDITIONAL_PUBLISH_v*"
    if value.startswith("DISCHARGED_CONDITIONAL_v"):
        return "DISCHARGED_CONDITIONAL_v*"
    if value.startswith("NOT_YET_"):
        return "NOT_YET_*"
    return value


def _assumption_taxonomy_classes() -> set[str]:
    text = _read(ASSUMPTION_REGISTRY_PATH)
    assert "## Taxonomy Classes" in text, "ASSUMPTION_REGISTRY_v1.md is missing '## Taxonomy Classes'."
    assert "## Canonical Assumption Table" in text, (
        "ASSUMPTION_REGISTRY_v1.md is missing '## Canonical Assumption Table'."
    )
    taxonomy_block = text.split("## Taxonomy Classes", 1)[1].split("## Canonical Assumption Table", 1)[0]
    return set(re.findall(r"`([A-Z]+)`", taxonomy_block))


def _state_status_categories() -> set[str]:
    state_text = _read(STATE_PATH)
    return set(re.findall(r"`[A-Z0-9\-]+:\s*([A-Z\-]+)`", state_text))


def test_assumption_taxonomy_classes_do_not_proliferate_without_whitelist() -> None:
    lock = _read_json(_latest_lock_path())
    allowed = set(lock["baseline"]["assumption_taxonomy_classes"])
    observed = _assumption_taxonomy_classes()
    new_classes = sorted(observed - allowed)
    assert not new_classes, (
        "New assumption/token taxonomy class(es) detected. Update governance lock/version first: "
        + ", ".join(new_classes)
    )


def test_adjudication_values_and_suffix_patterns_do_not_proliferate_without_whitelist() -> None:
    lock = _read_json(_latest_lock_path())
    baseline = lock["baseline"]

    observed_values = _adjudication_values()
    allowed_values = set(baseline["adjudication_values"])
    new_values = sorted(observed_values - allowed_values)
    assert not new_values, (
        "New adjudication value(s) detected. Update governance lock/version first: "
        + ", ".join(new_values)
    )

    observed_suffixes = {_adjudication_suffix_pattern(value) for value in observed_values}
    allowed_suffixes = set(baseline["adjudication_suffix_patterns"])
    new_suffixes = sorted(observed_suffixes - allowed_suffixes)
    assert not new_suffixes, (
        "New adjudication suffix pattern(s) detected. Update governance lock/version first: "
        + ", ".join(new_suffixes)
    )


def test_state_status_categories_do_not_proliferate_without_whitelist() -> None:
    lock = _read_json(_latest_lock_path())
    allowed = set(lock["baseline"]["state_status_categories"])
    observed = _state_status_categories()
    new_categories = sorted(observed - allowed)
    assert not new_categories, (
        "New state-level status category detected. Update governance lock/version first: "
        + ", ".join(new_categories)
    )
