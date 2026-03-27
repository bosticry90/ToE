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
SCHEMA_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STATE_CORE_SCHEMA_v0.json"
STATE_CORE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"


def _load_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def test_state_core_files_exist() -> None:
    assert SCHEMA_PATH.exists(), "Missing STATE_CORE_SCHEMA_v0.json"
    assert STATE_CORE_PATH.exists(), "Missing state_core_v0.json"


def test_state_core_matches_schema_contract() -> None:
    schema = _load_json(SCHEMA_PATH)
    state_core = _load_json(STATE_CORE_PATH)

    assert state_core["schema_id"] == schema["schema_id"]

    for key in schema["required_top_level"]:
        assert key in state_core, f"state_core missing top-level key: {key}"

    assert isinstance(state_core["tranches"], list)
    assert len(state_core["tranches"]) >= 1

    for tranche in state_core["tranches"]:
        for field in schema["required_tranche_fields"]:
            assert field in tranche, f"tranche missing required field: {field}"

        assert tranche["mode"] in schema["allowed_modes"]
        assert tranche["scientific_delta_class"] in schema["allowed_scientific_delta_classes"]

        transition = tranche["status_transition"]
        assert transition["from"] in schema["allowed_status_postures"]
        assert transition["to"] in schema["allowed_status_postures"]
        assert "decision_basis" in transition

    lineage_family = state_core["ws10_scientific_artifact_lineage_family"]
    assert lineage_family["family_id"] == "WS10_SCIENTIFIC_ARTIFACT_LINEAGE_METADATA_v0"
    assert lineage_family["active_lineage_id"].startswith("WS10-L")
    assert isinstance(lineage_family["lineages"], list)
    assert len(lineage_family["lineages"]) >= 1

    lineage_ids = [entry["id"] for entry in lineage_family["lineages"]]
    assert lineage_family["active_lineage_id"] in lineage_ids

    gate_metadata_family = state_core["ws10_scientific_artifact_gate_metadata_family"]
    assert gate_metadata_family["family_id"] == "WS10_SCIENTIFIC_ARTIFACT_GATE_METADATA_v0"
    assert gate_metadata_family["active_gate_entry_id"].startswith("WS10-G")
    assert isinstance(gate_metadata_family["entries"], list)
    assert len(gate_metadata_family["entries"]) >= 1

    gate_entry_ids = [entry["id"] for entry in gate_metadata_family["entries"]]
    assert gate_metadata_family["active_gate_entry_id"] in gate_entry_ids

    additive_candidate_family = state_core["ws10_additive_candidate_declaration_metadata_family"]
    assert additive_candidate_family["family_id"] == "WS10_ADDITIVE_CANDIDATE_DECLARATION_METADATA_v0"
    assert additive_candidate_family["active_candidate_id"].startswith("WS10-AC")
    assert isinstance(additive_candidate_family["entries"], list)
    assert len(additive_candidate_family["entries"]) >= 1

    candidate_ids = [entry["candidate_id"] for entry in additive_candidate_family["entries"]]
    assert additive_candidate_family["active_candidate_id"] in candidate_ids


def test_state_core_paths_resolve() -> None:
    state_core = _load_json(STATE_CORE_PATH)

    for tranche in state_core["tranches"]:
        artifact_path = REPO_ROOT / tranche["evidence_artifact"]
        gate_path = REPO_ROOT / tranche["gate_test"]
        assert artifact_path.exists(), f"Missing tranche evidence artifact: {artifact_path}"
        assert gate_path.exists(), f"Missing tranche gate test: {gate_path}"

    for target in state_core["mirror_targets"]:
        target_path = REPO_ROOT / target["path"]
        assert target_path.exists(), f"Missing mirror target path: {target_path}"
        assert target["marker_id"].startswith("STATE_CORE_"), "marker_id must use STATE_CORE_ prefix"

    lineage_family = state_core["ws10_scientific_artifact_lineage_family"]
    tranche_ids = {tranche["id"] for tranche in state_core["tranches"]}
    for lineage in lineage_family["lineages"]:
        artifact_path = REPO_ROOT / lineage["artifact"]
        assert artifact_path.exists(), f"Missing lineage artifact path: {artifact_path}"
        assert lineage["tranche_id"] in tranche_ids, f"Unknown tranche_id in lineage entry: {lineage['tranche_id']}"

    lineage_ids = {lineage["id"] for lineage in lineage_family["lineages"]}
    gate_metadata_family = state_core["ws10_scientific_artifact_gate_metadata_family"]
    for gate_entry in gate_metadata_family["entries"]:
        gate_path = REPO_ROOT / gate_entry["gate_test"]
        artifact_path = REPO_ROOT / gate_entry["artifact"]
        assert gate_path.exists(), f"Missing gate metadata test path: {gate_path}"
        assert artifact_path.exists(), f"Missing gate metadata artifact path: {artifact_path}"
        assert gate_entry["tranche_id"] in tranche_ids, f"Unknown tranche_id in gate metadata entry: {gate_entry['tranche_id']}"
        assert gate_entry["lineage_id"] in lineage_ids, f"Unknown lineage_id in gate metadata entry: {gate_entry['lineage_id']}"

    additive_candidate_family = state_core["ws10_additive_candidate_declaration_metadata_family"]
    for entry in additive_candidate_family["entries"]:
        decision_path = REPO_ROOT / entry["decision_linkage"]
        artifact_pointer_path = REPO_ROOT / entry["artifact_pointer"]
        assert entry["lane"] in state_core["lanes"], f"Unknown lane in additive candidate entry: {entry['lane']}"
        assert entry["cycle_target"].startswith("CYCLE"), (
            f"Unexpected cycle_target in additive candidate entry: {entry['cycle_target']}"
        )
        assert entry["status_token"].endswith("DECLARED_BOUNDED_NONREDUNDANT_PAYLOAD_v0")
        assert decision_path.exists(), f"Missing additive candidate decision linkage: {decision_path}"
        assert artifact_pointer_path.exists(), f"Missing additive candidate artifact pointer: {artifact_pointer_path}"
