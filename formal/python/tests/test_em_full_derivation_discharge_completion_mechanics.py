from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
REGISTRY_PATH = PAPER_DIR / "PILLAR_DISCHARGE_REGISTRY_v0.json"
EM_TARGET_PATH = PAPER_DIR / "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = PAPER_DIR / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = PAPER_DIR / "RESULTS_TABLE_v0.md"

GENERIC_COMPLETION_GATE_PATH = "formal/python/tests/test_pillar_full_discharge_completion_mechanics.py"
EM_CANONICAL_ADMISSIBILITY_LOCK_PATH = "formal/python/tests/test_em_u1_canonical_route_admissibility_lock.py"
EM_ADJUDICATION_CRITERIA_ARTIFACT_GATE_PATH = (
    "formal/python/tests/test_em_u1_full_discharge_adjudication_criteria_artifact.py"
)
EM_ADJUDICATION_CRITERIA_ARTIFACT_PATH = (
    "formal/output/em_pillar_full_discharge_adjudication_criteria_cycle46_v0.json"
)
EM_SPECIFIC_GATE_PATH = "formal/python/tests/test_em_full_derivation_discharge_completion_mechanics.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _find_em_registry_entry(registry: dict) -> dict:
    matches = [entry for entry in registry.get("pillars", []) if entry.get("pillar_key") == "EM"]
    assert len(matches) == 1, "Registry must contain exactly one EM pillar entry."
    return matches[0]


def test_em_completion_mechanics_is_delegated_to_registry_driven_generic_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    em_entry = _find_em_registry_entry(registry)

    assert em_entry["pillar_name"] == "PILLAR-EM"
    assert em_entry["discharge_doc_path"] == "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
    assert em_entry["discharge_adjudication_token"] == "PILLAR_EM_FULL_DERIVATION_DISCHARGE_ADJUDICATION"
    assert em_entry["required_results_rows"] == ["TOE-EM-DER-01", "TOE-EM-DER-02"]
    assert em_entry["required_theorem_surfaces"], "EM registry entry must pin required theorem surfaces."
    assert em_entry["lean_paths"] == ["formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean"]

    for path in [EM_TARGET_PATH, STATE_PATH, ROADMAP_PATH, RESULTS_PATH]:
        text = _read(path)
        assert (
            GENERIC_COMPLETION_GATE_PATH in text
        ), f"{path} must reference the registry-driven generic completion gate `{GENERIC_COMPLETION_GATE_PATH}`."
        assert (
            EM_CANONICAL_ADMISSIBILITY_LOCK_PATH in text
        ), f"{path} must reference the EM canonical admissibility lock `{EM_CANONICAL_ADMISSIBILITY_LOCK_PATH}`."
        assert (
            EM_ADJUDICATION_CRITERIA_ARTIFACT_GATE_PATH in text
        ), (
            f"{path} must reference the EM adjudication-criteria artifact gate "
            f"`{EM_ADJUDICATION_CRITERIA_ARTIFACT_GATE_PATH}`."
        )
        assert (
            EM_ADJUDICATION_CRITERIA_ARTIFACT_PATH in text
        ), (
            f"{path} must reference the EM adjudication-criteria artifact path "
            f"`{EM_ADJUDICATION_CRITERIA_ARTIFACT_PATH}`."
        )


def test_em_completion_surfaces_do_not_pin_em_specific_gate_as_authority() -> None:
    violations: list[str] = []
    for path in [EM_TARGET_PATH, STATE_PATH, ROADMAP_PATH, RESULTS_PATH]:
        text = _read(path)
        if EM_SPECIFIC_GATE_PATH in text:
            violations.append(str(path.relative_to(REPO_ROOT)))

    assert not violations, (
        "EM completion authority must stay single-source (generic gate only); "
        f"found legacy EM-specific gate pointer in: {', '.join(violations)}"
    )
