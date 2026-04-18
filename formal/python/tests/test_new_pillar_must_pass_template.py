from __future__ import annotations

import json
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
ARCHITECTURE_SCHEMA_PATH = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
PILLAR_STATUS_MATRIX_PATH = PAPER_DIR / "PILLAR_STATUS_MATRIX_v1.json"
MATRIX_ROADMAP_COVERAGE_GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_pillar_matrix_roadmap_coverage_gate.py"

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
CLAIM_TRACEABILITY_HEADER = "claim_traceability"
TRACEABILITY_REQUIRED_FIELDS = [
    "ClaimID",
    "ClaimText",
    "Location",
    "ImpactClass",
    "EnforcementBucket",
    "EnforcingTests",
    "EnforcedArtifacts",
    "Tokens/Invariants",
    "Notes",
    "Fix (if D)",
]
TRACEABILITY_TIMELINE_PATTERN = re.compile(r"\b(CYCLE[-_ ]?\d+|BY_CYCLE_\d+|Q[1-4]-\d{4}|\d{4}-\d{2}-\d{2})\b")


def _derive_pillar_id(path_name: str) -> str | None:
    name = path_name.upper()
    if "_QFT_" in name:
        return "PILLAR-QFT"
    if "_QM_" in name:
        return "PILLAR-QM"
    if "_EM_" in name:
        return "PILLAR-EM"
    if "_SR_" in name:
        return "PILLAR-SR"
    if "_GR" in name:
        return "PILLAR-GR"
    if "THERMO" in name or "_STAT_" in name:
        return "PILLAR-STAT"
    if "COSMO" in name:
        return "PILLAR-COSMO"
    return None


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


def _extract_claim_traceability_entries(text: str, path_name: str) -> list[str]:
    text_lower = text.lower()
    start = text_lower.find(CLAIM_TRACEABILITY_HEADER)
    assert start >= 0, f"{path_name}: missing required CLAIM_TRACEABILITY section."

    section = text[start:]
    starts = list(re.finditer(r"(?m)^\* ClaimID:\s*", section))
    assert starts, f"{path_name}: CLAIM_TRACEABILITY section must include at least one `* ClaimID:` entry."

    entries: list[str] = []
    for i, match in enumerate(starts):
        entry_start = match.start()
        entry_end = starts[i + 1].start() if i + 1 < len(starts) else len(section)
        entries.append(section[entry_start:entry_end].strip())
    return entries


def _field(entry: str, field_name: str) -> str:
    m = re.search(rf"(?m)^\* {re.escape(field_name)}:\s*(.+)$", entry)
    assert m is not None, f"Missing required field `{field_name}` in entry:\n{entry}"
    value = m.group(1).strip()
    assert value, f"Field `{field_name}` must be non-empty."
    return value


def test_new_pillars_and_em_targets_define_structure_before_claim_tokens() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    matrix = _read_json(PILLAR_STATUS_MATRIX_PATH)
    matrix_pillars = set(matrix.get("pillars", {}).keys())
    known_targets = set(schema.get("known_derivation_target_files", []))
    all_targets = sorted(PAPER_DIR.glob("DERIVATION_TARGET*.md"))

    candidate_paths = [
        path
        for path in all_targets
        if path.name not in known_targets
    ]

    candidate_paths = [
        path
        for path in candidate_paths
        if not path.name.startswith("DERIVATION_TARGET_QFT_EVOL_MICRO_")
        and not path.name.startswith("DERIVATION_TARGET_QFT_GAUGE_MICRO_")
        and not path.name.startswith("DERIVATION_TARGET_EM_U1_MICRO_")
        and not path.name.startswith("DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_")
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

        if "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json" not in text:
            violations.append(
                f"{path.name}: must reference formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json as canonical pillar status matrix."
            )

        pillar_id = _derive_pillar_id(path.name)
        if pillar_id is None:
            violations.append(f"{path.name}: unable to derive pillar ID from target filename; add mapping to template gate.")
        elif pillar_id not in matrix_pillars:
            violations.append(f"{path.name}: missing required matrix row `{pillar_id}` in PILLAR_STATUS_MATRIX_v1.json.")

        if not MATRIX_ROADMAP_COVERAGE_GATE_PATH.exists():
            violations.append(
                f"{path.name}: required matrix coverage gate file missing: {MATRIX_ROADMAP_COVERAGE_GATE_PATH.as_posix()}"
            )

        if "formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py" not in text:
            violations.append(
                f"{path.name}: must pin formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py in governance test pointers."
            )

        if re.search(r"formal/python/tests/test_[a-z0-9_]*consistency_gate\.py", text) is None:
            violations.append(
                f"{path.name}: must pin at least one consistency gate test path (test_*consistency_gate.py)."
            )

        has_retirement_gate = re.search(r"formal/python/tests/test_[a-z0-9_]*retirement_gate\.py", text) is not None
        has_generic_retirement_gate = "formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py" in text
        if not (has_retirement_gate or has_generic_retirement_gate):
            violations.append(
                f"{path.name}: must pin a retirement gate test path (pillar-specific or generic)."
            )

        try:
            entries = _extract_claim_traceability_entries(text, path.name)
            if len(entries) < 3:
                violations.append(f"{path.name}: CLAIM_TRACEABILITY must include at least 3 entries.")

            for entry in entries:
                for field_name in TRACEABILITY_REQUIRED_FIELDS:
                    _field(entry, field_name)

                bucket = _field(entry, "EnforcementBucket")
                if bucket not in {"A", "B", "C", "D"}:
                    violations.append(f"{path.name}: invalid EnforcementBucket `{bucket}` in CLAIM_TRACEABILITY.")

                if bucket == "D":
                    fix_text = _field(entry, "Fix (if D)")
                    if "TODO: add gate" not in fix_text:
                        violations.append(
                            f"{path.name}: bucket D entries must include `TODO: add gate` in Fix field."
                        )
                    if TRACEABILITY_TIMELINE_PATTERN.search(fix_text) is None:
                        violations.append(
                            f"{path.name}: bucket D entries must include bounded timeline token in Fix field."
                        )
        except AssertionError as exc:
            violations.append(str(exc))

    assert not violations, "New-pillar template gate violations:\n- " + "\n- ".join(violations)
