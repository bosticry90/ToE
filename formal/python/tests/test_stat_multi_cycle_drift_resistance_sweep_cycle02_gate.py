from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STAT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_multi_cycle_drift_resistance_sweep_cycle02_v0.json"

EXPECTED_ARTIFACT_ID = "stat_multi_cycle_drift_resistance_sweep_cycle02_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_ARTIFACT_REL = "formal/output/stat_multi_cycle_drift_resistance_sweep_cycle02_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_multi_cycle_drift_resistance_sweep_cycle02_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_stat_multi_cycle_drift_resistance_sweep_cycle02_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    artifact_json = _read_json(ARTIFACT_PATH)

    assert ("| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text or "| `PILLAR-STAT` | `CLOSED` |" in roadmap_text), ("STAT gate requires `PILLAR-STAT` ACTIVE or CLOSED posture.")
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist for multi-cycle drift-resistance sweep gate."
    assert stat_matrix.get("matrix_status") in {"ACTIVE", "CLOSED"}, "PILLAR-STAT matrix row must be `ACTIVE` or `CLOSED`."

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("artifact_version") == "v0"
    assert artifact_json.get("placeholder_template") is True
    assert isinstance(artifact_json.get("payload"), dict)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == computed_payload_sha, (
        "STAT multi-cycle drift-resistance sweep cycle-02 payload_sha256 does not match canonical payload hash."
    )

    for token_name, expected in (
        ("STAT_MULTI_CYCLE_DRIFT_RESISTANCE_SWEEP_CYCLE02_ARTIFACT_v0", EXPECTED_ARTIFACT_ID),
        ("STAT_MULTI_CYCLE_DRIFT_RESISTANCE_SWEEP_CYCLE02_GATE_v0", EXPECTED_COUPLING_GATE),
    ):
        assert _extract_token(stat_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    stat_sha = _extract_token(stat_text, "STAT_MULTI_CYCLE_DRIFT_RESISTANCE_SWEEP_CYCLE02_SHA256_v0")
    state_sha = _extract_token(state_text, "STAT_MULTI_CYCLE_DRIFT_RESISTANCE_SWEEP_CYCLE02_SHA256_v0")
    roadmap_sha = _extract_token(roadmap_text, "STAT_MULTI_CYCLE_DRIFT_RESISTANCE_SWEEP_CYCLE02_SHA256_v0")
    assert stat_sha == state_sha == roadmap_sha == artifact_json["payload_sha256"]

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert EXPECTED_ARTIFACT_REL in doc_text, f"{doc_label} must pin STAT multi-cycle drift-resistance sweep artifact path."
        assert EXPECTED_GATE_REL in doc_text, f"{doc_label} must pin STAT multi-cycle drift-resistance sweep gate path."

    payload = artifact_json["payload"]
    assert payload.get("checkpoint") == "stat_multi_cycle_drift_resistance_sweep_cycle02"
    assert payload.get("status") == "placeholder_non_promotional"
    assert payload.get("cycle_window") == ["cycle01", "cycle02"]
    assert payload.get("drift_resistance_scope") == [
        "multi_cycle_token_stability_placeholder_only",
        "cross_surface_pointer_stability_placeholder_only",
        "no_adjudication_or_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert payload.get("discharge_row_linkage") == ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]

    assert "- non-claim boundary remains explicit and binding for this artifact." in stat_text
    assert "- bounded drift-resistance scope only; no discharge/adequacy completion claim and no external truth claim." in stat_text
