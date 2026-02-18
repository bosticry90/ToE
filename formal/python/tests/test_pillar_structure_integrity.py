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
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"

REQUIRED_TEMPLATE_HEADINGS = [
    "TARGET section",
    "ASSUMPTION FREEZE section",
    "CANONICAL ROUTE section",
    "COUNTERFACTUAL ROUTE section",
    "INDEPENDENT NECESSITY ROUTE section",
    "BOUNDED SCOPE section",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _section_body(markdown: str, heading: str) -> str | None:
    m = re.search(rf"^##\s+{re.escape(heading)}\s*$", markdown, flags=re.MULTILINE)
    if m is None:
        return None
    tail = markdown[m.end() :]
    next_heading = re.search(r"^##\s+", tail, flags=re.MULTILINE)
    if next_heading is None:
        return tail.strip()
    return tail[: next_heading.start()].strip()


def test_required_template_sections_exist_for_each_pillar_target() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    pillar_targets = schema.get("pillar_target_files", [])
    assert pillar_targets, "ARCHITECTURE_SCHEMA_v1.json must declare pillar_target_files."

    violations: list[str] = []
    for name in pillar_targets:
        path = PAPER_DIR / name
        text = _read(path)
        for heading in REQUIRED_TEMPLATE_HEADINGS:
            if _section_body(text, heading) is None:
                violations.append(f"{name}: missing required heading '## {heading}'.")

    assert not violations, "Pillar template integrity violations:\n- " + "\n- ".join(violations)


def test_bounded_scope_sections_include_explicit_non_claim_language() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    pillar_targets = schema.get("pillar_target_files", [])

    violations: list[str] = []
    for name in pillar_targets:
        path = PAPER_DIR / name
        text = _read(path)
        section = _section_body(text, "BOUNDED SCOPE section")
        if section is None:
            violations.append(f"{name}: missing BOUNDED SCOPE section.")
            continue
        section_lower = section.lower()
        if "bounded" not in section_lower:
            violations.append(f"{name}: BOUNDED SCOPE section must explicitly include bounded language.")
        if "non-claim" not in section_lower:
            violations.append(f"{name}: BOUNDED SCOPE section must explicitly include non-claim language.")

    assert not violations, "Bounded scope integrity violations:\n- " + "\n- ".join(violations)
