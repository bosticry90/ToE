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
STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_PHASE_ADVANCEMENT_STANDARD_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
GOVERNANCE_SUITE_PATH = REPO_ROOT / "governance_suite.ps1"

STANDARD_REL = "formal/docs/release/PILLAR_PHASE_ADVANCEMENT_STANDARD_v0.md"
REGISTRY_REL = "formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"
GATE_REL = "formal/python/tests/test_pillar_phase_advancement_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert match is not None, f"Missing token `{token_name}`."
    return match.group(1)


def _extract_roadmap_row(text: str, pillar_id: str) -> re.Match[str]:
    match = re.search(
        rf"^\|\s*`{re.escape(pillar_id)}`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]*)`\s*\|",
        text,
        flags=re.MULTILINE,
    )
    assert match is not None, f"Missing roadmap row for {pillar_id}."
    return match


def test_pillar_phase_advancement_standard_is_pinned_globally() -> None:
    standard_text = _read(STANDARD_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    governance_suite_text = _read(GOVERNANCE_SUITE_PATH)

    for token in (
        "PILLAR_PHASE_ADVANCEMENT_STANDARD_v0",
        "CLOSED_HANDOFF",
        "CLOSED_HANDOFF_ARTIFACT",
        "PHASE_ORDERED",
        "ACTIVE_EXECUTION",
        "LOCKED_QUEUE",
        REGISTRY_REL,
        GATE_REL,
    ):
        assert token in standard_text, f"Phase advancement standard missing token `{token}`."

    for doc_text, doc_label in ((roadmap_text, "roadmap"), (state_text, "state")):
        assert STANDARD_REL in doc_text, f"{doc_label} must pin the pillar phase advancement standard path."
        assert REGISTRY_REL in doc_text, f"{doc_label} must pin the pillar phase advancement registry path."
        assert GATE_REL in doc_text, f"{doc_label} must pin the pillar phase advancement gate path."

    assert GATE_REL in governance_suite_text, "governance_suite.ps1 must include the generic pillar phase advancement gate."


def test_registry_drives_pillar_phase_advancement_semantics() -> None:
    registry = _read_json(REGISTRY_PATH)
    matrix = _read_json(MATRIX_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    assert registry.get("registry_id") == "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0"
    assert registry.get("registry_version") == 1
    assert registry.get("standard_doc") == STANDARD_REL
    assert registry.get("gate_path") == GATE_REL

    global_tokens = registry.get("global_tokens", {})
    focus_token = global_tokens.get("focus_token")
    lane_token = global_tokens.get("lane_token")
    assert focus_token == "NEXT_PILLAR_FOCUS_v0"
    assert lane_token == "NEXT_PILLAR_PRIMARY_LANE_v0"

    focus_value = _extract_token(state_text, focus_token)
    lane_value = _extract_token(state_text, lane_token)

    pillars = registry.get("pillars", [])
    assert isinstance(pillars, list) and pillars, "Phase advancement registry must define pillar entries."
    pillar_ids = [entry.get("pillar_id") for entry in pillars]
    assert len(pillar_ids) == len(set(pillar_ids)), "Phase advancement registry pillar IDs must be unique."

    matrix_pillars = matrix.get("pillars", {})

    for entry in pillars:
        pillar_id = entry["pillar_id"]
        mode = entry["mode"]
        authority_text = _read(REPO_ROOT / entry["authority_doc_path"])

        expected_matrix_status = entry.get("expected_matrix_status")
        if expected_matrix_status is not None:
            matrix_entry = matrix_pillars.get(pillar_id)
            assert isinstance(matrix_entry, dict), f"{pillar_id}: matrix row is required by phase advancement registry."
            assert matrix_entry.get("matrix_status") == expected_matrix_status, (
                f"{pillar_id}: matrix status must remain {expected_matrix_status}."
            )

        if mode == "CLOSED_HANDOFF":
            assert _extract_token(authority_text, entry["completion_token"]) == entry["completion_value"]
            proceed_token = entry.get("roadmap_proceed_token")
            if proceed_token:
                proceed_value = _extract_token(roadmap_text, proceed_token)
                assert proceed_value.startswith(entry["roadmap_proceed_prefix"]), (
                    f"{pillar_id}: roadmap proceed gate must start with {entry['roadmap_proceed_prefix']}."
                )
            assert focus_value == entry["expected_global_focus"], (
                f"{pillar_id}: global next-pillar focus drift detected."
            )
            assert lane_value == entry["expected_global_lane"], (
                f"{pillar_id}: global next-pillar lane drift detected."
            )

        elif mode == "CLOSED_HANDOFF_ARTIFACT":
            assert _extract_token(authority_text, entry["completion_token"]) == entry["completion_value"]
            for doc_text, doc_label in ((authority_text, "authority doc"), (state_text, "state")):
                assert _extract_token(doc_text, entry["handoff_token"]) == entry["handoff_value"], (
                    f"{pillar_id}: {doc_label} must pin the declared handoff token."
                )
                assert entry["handoff_artifact_path"] in doc_text, (
                    f"{pillar_id}: {doc_label} must pin the declared handoff artifact path."
                )
                assert entry["handoff_gate_path"] in doc_text, (
                    f"{pillar_id}: {doc_label} must pin the declared handoff gate path."
                )
            assert entry["handoff_artifact_path"] in roadmap_text, (
                f"{pillar_id}: roadmap must pin the declared handoff artifact path."
            )
            assert entry["handoff_gate_path"] in roadmap_text, (
                f"{pillar_id}: roadmap must pin the declared handoff gate path."
            )
            assert focus_value == entry["expected_global_focus"], (
                f"{pillar_id}: global next-pillar focus drift detected."
            )
            assert lane_value == entry["expected_global_lane"], (
                f"{pillar_id}: global next-pillar lane drift detected."
            )

        elif mode == "PHASE_ORDERED":
            for surface_text, surface_label in ((authority_text, "authority doc"), (state_text, "state")):
                for pair in entry["phase_pairs"]:
                    assert _extract_token(surface_text, pair["completion_token"]) == pair["completion_value"], (
                        f"{pillar_id}: {surface_label} completion token drift for {pair['completion_token']}."
                    )
                    assert _extract_token(surface_text, pair["next_token"]) == pair["next_value"], (
                        f"{pillar_id}: {surface_label} next-phase token drift for {pair['next_token']}."
                    )

        elif mode == "ACTIVE_EXECUTION":
            contract_text = _read(REPO_ROOT / entry["contract_doc_path"])
            roadmap_row = _extract_roadmap_row(roadmap_text, pillar_id)
            assert roadmap_row.group(1) == entry["expected_roadmap_status"], (
                f"{pillar_id}: roadmap row status must remain {entry['expected_roadmap_status']}."
            )

            for token_name, expected in sorted(entry["required_tokens"].items()):
                for surface_text, surface_label in (
                    (contract_text, "contract"),
                    (authority_text, "authority doc"),
                    (state_text, "state"),
                    (roadmap_text, "roadmap"),
                ):
                    assert _extract_token(surface_text, token_name) == expected, (
                        f"{pillar_id}: {surface_label} token drift for {token_name}."
                    )

            for surface_text, surface_label in (
                (contract_text, "contract"),
                (authority_text, "authority doc"),
                (state_text, "state"),
                (roadmap_text, "roadmap"),
            ):
                assert REGISTRY_REL in surface_text or surface_label in {"state", "roadmap"}, (
                    f"{pillar_id}: {surface_label} should remain tied to the global advancement registry."
                )
                assert GATE_REL in surface_text, f"{pillar_id}: {surface_label} must pin the generic phase advancement gate."

            reopen_token = entry["component_gate_reopen_token"]
            reopen_value = _extract_token(contract_text, reopen_token)
            if reopen_value == entry["component_gate_reopen_absent_value"]:
                component_gate_registry = _read_json(REPO_ROOT / entry["component_gate_registry_path"])
                component_gates = component_gate_registry.get(entry["component_gate_registry_key"])
                assert isinstance(component_gates, list), f"{pillar_id}: component gate registry must resolve to a list."
                assert GATE_REL in component_gates, (
                    f"{pillar_id}: generic phase advancement gate must be admitted in the component gate set."
                )
                assert len(component_gates) == int(entry["component_gate_freeze_count"]), (
                    f"{pillar_id}: component gate set cannot expand without flipping the reopen token."
                )

        elif mode == "LOCKED_QUEUE":
            row_match = _extract_roadmap_row(roadmap_text, pillar_id)
            status = row_match.group(1)
            target_id = row_match.group(2)
            prereq_field = row_match.group(4)

            assert status == entry["roadmap_status"], f"{pillar_id}: roadmap status must remain {entry['roadmap_status']}."
            assert target_id == entry["target_id"], f"{pillar_id}: roadmap target ID drift detected."
            prereqs = [value for value in prereq_field.split(";") if value]
            assert prereqs == entry["prerequisites"], f"{pillar_id}: roadmap prerequisite set drift detected."
            assert entry["target_id"] in authority_text, f"{pillar_id}: authority doc must pin its target ID."
            assert pillar_id in state_text, f"{pillar_id}: state must continue to mention the locked downstream queue pillar."

        else:
            raise AssertionError(f"Unsupported phase advancement mode: {mode}")
