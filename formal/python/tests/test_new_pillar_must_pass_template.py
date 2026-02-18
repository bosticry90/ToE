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

BOUNDED_MARKERS = [
    "bounded scope section",
    "scope boundary",
    "non-claim boundary",
    "bounded theorem scope",
    "bounded/discrete",
]
ASSUMPTION_CLASS_MARKERS = [
    "assumption classes",
    "math|def|policy|scope",
    "taxonomy classes",
    "assumption freeze section",
]
COUNTERFACTUAL_MARKERS = [
    "counterfactual route section",
    "counterfactual",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _first_index(text_lower: str, markers: list[str]) -> int:
    indices = [text_lower.find(marker) for marker in markers if marker in text_lower]
    if not indices:
        return -1
    return min(indices)


def _first_derivation_token_index(text: str) -> int:
    token_match = re.search(
        r"`(?!DERIVATION_TARGET_)[^`\n]*DERIVATION[^`\n]*`|`TOE-[^`\n]*-DER-[^`\n]*`|[A-Z0-9_]*DERIVATION[A-Z0-9_]*_ADJUDICATION",
        text,
        flags=re.IGNORECASE,
    )
    if token_match is None:
        return -1
    return token_match.start()


def test_new_pillars_and_em_targets_define_structure_before_claim_tokens() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    known_targets = set(schema.get("known_derivation_target_files", []))
    all_targets = sorted(PAPER_DIR.glob("DERIVATION_TARGET*.md"))

    candidate_paths = [
        path
        for path in all_targets
        if path.name not in known_targets or "_EM_" in path.name
    ]

    if not candidate_paths:
        return

    violations: list[str] = []
    for path in candidate_paths:
        text = _read(path)
        text_lower = text.lower()

        derivation_idx = _first_derivation_token_index(text)
        bounded_idx = _first_index(text_lower, BOUNDED_MARKERS)
        if derivation_idx >= 0 and (bounded_idx < 0 or bounded_idx > derivation_idx):
            violations.append(
                f"{path.name}: bounded scope must be declared before any derivation token."
            )

        inevitability_match = re.search(r"\binevitability\b", text_lower)
        if inevitability_match is not None:
            assumption_idx = _first_index(text_lower, ASSUMPTION_CLASS_MARKERS)
            if assumption_idx < 0 or assumption_idx > inevitability_match.start():
                violations.append(
                    f"{path.name}: assumption classes must be declared before inevitability claims."
                )

        discharge_match = re.search(r"\b[A-Z0-9_]+_ADJUDICATION\s*:\s*DISCHARGED", text)
        if discharge_match is not None:
            counterfactual_idx = _first_index(text_lower, COUNTERFACTUAL_MARKERS)
            if counterfactual_idx < 0 or counterfactual_idx > discharge_match.start():
                violations.append(
                    f"{path.name}: counterfactual section must be declared before discharge adjudication."
                )

    assert not violations, "New-pillar template gate violations:\n- " + "\n- ".join(violations)
