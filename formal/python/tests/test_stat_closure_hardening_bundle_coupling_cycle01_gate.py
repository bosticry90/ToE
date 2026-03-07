from __future__ import annotations

import hashlib
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
STAT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_closure_hardening_bundle_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "stat_closure_hardening_bundle_cycle01_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_ARTIFACT_REL = "formal/output/stat_closure_hardening_bundle_cycle01_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_closure_hardening_bundle_coupling_cycle01_gate.py"


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


def test_stat_closure_hardening_bundle_coupling_cycle01_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    artifact_json = _read_json(ARTIFACT_PATH)

    assert ("| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text or "| `PILLAR-STAT` | `CLOSED` |" in roadmap_text), ("STAT gate requires `PILLAR-STAT` ACTIVE or CLOSED posture.")
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist for closure-hardening gate."
    assert stat_matrix.get("matrix_status") in {"ACTIVE", "CLOSED"}, "PILLAR-STAT matrix row must be `ACTIVE` or `CLOSED`."

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("artifact_version") == "v0"
    assert artifact_json.get("placeholder_template") is True
    assert isinstance(artifact_json.get("payload"), dict)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == computed_payload_sha, (
        "STAT closure-hardening cycle-01 payload_sha256 does not match canonical payload hash."
    )

    for token_name, expected in (
        ("STAT_CLOSURE_HARDENING_BUNDLE_CYCLE01_ARTIFACT_v0", EXPECTED_ARTIFACT_ID),
        ("STAT_CLOSURE_HARDENING_BUNDLE_CYCLE01_GATE_v0", EXPECTED_COUPLING_GATE),
    ):
        assert _extract_token(stat_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    stat_sha = _extract_token(stat_text, "STAT_CLOSURE_HARDENING_BUNDLE_CYCLE01_SHA256_v0")
    state_sha = _extract_token(state_text, "STAT_CLOSURE_HARDENING_BUNDLE_CYCLE01_SHA256_v0")
    roadmap_sha = _extract_token(roadmap_text, "STAT_CLOSURE_HARDENING_BUNDLE_CYCLE01_SHA256_v0")
    assert stat_sha == state_sha == roadmap_sha == artifact_json["payload_sha256"]

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert EXPECTED_ARTIFACT_REL in doc_text, f"{doc_label} must pin STAT closure-hardening artifact path."
        assert EXPECTED_GATE_REL in doc_text, f"{doc_label} must pin STAT closure-hardening gate path."

    payload = artifact_json["payload"]
    assert payload.get("checkpoint") == "stat_closure_hardening_cycle01"
    assert payload.get("status") == "placeholder_non_promotional"
    assert payload.get("boundedness_restatement") == [
        "active_stage_pre_discharge_scope_only",
        "no_toe_stat_der_discharge_claim",
        "no_inevitability_or_adequacy_completion_claim",
        "no_external_truth_claim",
    ]
    assert payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert payload.get("discharge_row_linkage") == ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]

    assert "- non-claim boundary remains explicit and binding for this artifact." in stat_text
