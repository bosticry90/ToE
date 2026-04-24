from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

REGISTRY_REL = "formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
M2_GATE_REL = "formal/python/tests/test_pillar_deep_maturity_m2_completion_gate.py"


VALID_M2 = {"NOT_STARTED_v0", "IN_PROGRESS_v0", "COMPLETE_v0", "COMPLETE_BOUNDED_v0"}
REQUIRED_M2_ROWS = (
    "analytic_completeness",
    "canonical_equivalence",
    "assumption_minimization",
    "literature_alignment",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_m2_registry_structure_and_targets_are_pinned() -> None:
    registry = _read_json(REGISTRY_PATH)

    assert registry.get("m2_gate_path") == "formal/python/tests/test_pillar_deep_maturity_m2_completion_gate.py"

    rows = registry.get("pillars", [])
    assert isinstance(rows, list) and rows, "Deep maturity registry must define pillar rows."

    for row in rows:
        pillar_id = row.get("pillar_id")
        m2_status = row.get("m2_status")
        assert m2_status in VALID_M2, f"{pillar_id}: invalid m2_status."

        m2_plan_doc = row.get("m2_plan_doc")
        assert isinstance(m2_plan_doc, str) and m2_plan_doc, f"{pillar_id}: m2_plan_doc is required."
        assert (REPO_ROOT / m2_plan_doc).exists(), f"{pillar_id}: missing m2_plan_doc file {m2_plan_doc}."

        m2_rows = row.get("m2_exit_rows")
        assert isinstance(m2_rows, dict), f"{pillar_id}: m2_exit_rows must be an object."

        for key in REQUIRED_M2_ROWS:
            entry = m2_rows.get(key)
            assert isinstance(entry, dict), f"{pillar_id}: missing m2_exit_rows.{key}."

            token_name = entry.get("token_name")
            token_value = entry.get("token_value")
            artifact_path = entry.get("artifact_path")
            gate_path = entry.get("gate_path")

            assert isinstance(token_name, str) and token_name.endswith("_v0"), (
                f"{pillar_id}: {key} token_name must be a v0 token."
            )
            assert isinstance(token_value, str) and token_value, f"{pillar_id}: {key} token_value is required."
            assert isinstance(artifact_path, str) and artifact_path, f"{pillar_id}: {key} artifact_path is required."
            assert isinstance(gate_path, str) and gate_path, f"{pillar_id}: {key} gate_path is required."

            if str(m2_status).startswith("COMPLETE"):
                assert token_value not in {"PLANNED_v0", "NOT_PRESENT_v0"}, (
                    f"{pillar_id}: {key} cannot remain planned when m2_status is complete."
                )


def test_m2_registry_and_gate_are_pinned_in_roadmap() -> None:
    roadmap_text = _read(ROADMAP_PATH)

    assert REGISTRY_REL in roadmap_text, "Roadmap must pin deep-maturity registry pointer."
    assert M2_GATE_REL in roadmap_text, "Roadmap must pin deep-maturity M2 gate pointer."
