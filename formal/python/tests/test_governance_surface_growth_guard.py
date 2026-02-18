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
ARCHITECTURE_SCHEMA_PATH = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
ASSUMPTION_REGISTRY_PATH = PAPER_DIR / "ASSUMPTION_REGISTRY_v1.md"
RESULTS_PATH = PAPER_DIR / "RESULTS_TABLE_v0.md"


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


def _current_cycle_from_state() -> int:
    text = _read(STATE_PATH)
    matches = re.findall(r"\bCYCLE[-_]?(\d+)\b", text, flags=re.IGNORECASE)
    if not matches:
        return 0
    return max(int(m) for m in matches)


def _assumption_taxonomy_class_count() -> int:
    text = _read(ASSUMPTION_REGISTRY_PATH)
    taxonomy_block = text.split("## Taxonomy Classes", 1)[1].split("## Canonical Assumption Table", 1)[0]
    return len(set(re.findall(r"`([A-Z]+)`", taxonomy_block)))


def _adjudication_type_count() -> int:
    values: set[str] = set()
    for path in [STATE_PATH] + sorted(PAPER_DIR.glob("*.md")):
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
    return len(values)


def _governance_doc_count() -> int:
    docs: set[str] = set()
    docs.add(str(ARCHITECTURE_SCHEMA_PATH.relative_to(REPO_ROOT)))
    docs.add(str(STATE_PATH.relative_to(REPO_ROOT)))
    docs.add(str(ASSUMPTION_REGISTRY_PATH.relative_to(REPO_ROOT)))
    docs.add(str(RESULTS_PATH.relative_to(REPO_ROOT)))
    for path in PAPER_DIR.glob("DERIVATION_TARGET*.md"):
        docs.add(str(path.relative_to(REPO_ROOT)))
    for path in REPO_ROOT.glob("GOVERNANCE_VERSION_v*.lock"):
        docs.add(str(path.relative_to(REPO_ROOT)))
    return len(docs)


def test_governance_surface_growth_stays_within_cycle_bounded_delta() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    lock = _read_json(_latest_lock_path())

    growth_policy = schema["growth_policy"]
    baseline_cycle = int(growth_policy["baseline_cycle"])
    max_delta_per_cycle = growth_policy["max_delta_per_cycle"]
    baseline_counts = lock["baseline"]["governance_surface_counts"]

    current_cycle = _current_cycle_from_state()
    cycles_elapsed = max(0, current_cycle - baseline_cycle)

    observed = {
        "governance_docs": _governance_doc_count(),
        "token_categories": _assumption_taxonomy_class_count(),
        "adjudication_types": _adjudication_type_count(),
    }

    violations: list[str] = []
    for metric, observed_value in observed.items():
        baseline_value = int(baseline_counts[metric])
        allowed_delta = int(max_delta_per_cycle[metric]) * cycles_elapsed
        allowed_value = baseline_value + allowed_delta
        if observed_value > allowed_value:
            violations.append(
                f"{metric}: observed={observed_value}, allowed={allowed_value}, baseline={baseline_value}, "
                f"cycles_elapsed={cycles_elapsed}, max_delta_per_cycle={max_delta_per_cycle[metric]}"
            )

    assert not violations, "Governance surface growth exceeded allowed per-cycle delta:\n- " + "\n- ".join(violations)
