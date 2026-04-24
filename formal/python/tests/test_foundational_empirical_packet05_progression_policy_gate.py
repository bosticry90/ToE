from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json"
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_PACKET05_PROGRESSION_POLICY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_packet05_progression_policy_surface_is_pinned() -> None:
    protocol_text = _read(PROTOCOL_PATH)
    policy_text = _read(POLICY_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    state_text = _read(STATE_PATH)

    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_05_ENABLEMENT_v0") == (
        "SELECTIVE_LANE_ENABLEMENT_ALLOWED_WITH_PACKET04_INCONCLUSIVE_AND_INTERMEDIATE_EVIDENCE"
    )
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_05_ALLOWED_LANE_BOOTSTRAP_v0") == "GR_SR_CYCLE01"
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_05_DECISION_BASELINE_v0") == (
        "INCONCLUSIVE_ONLY_UNTIL_LANE_SPECIFIC_ELIGIBILITY_OVERRIDE"
    )

    assert "FOUNDATIONAL_EMPIRICAL_PACKET05_PROGRESSION_POLICY_v0" in policy_text

    for ref in (
        "formal/docs/release/FOUNDATIONAL_EMPIRICAL_PACKET05_PROGRESSION_POLICY_v0.md",
        "formal/python/tests/test_foundational_empirical_packet05_progression_policy_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text


def test_packet05_lane_eligibility_uses_packet04_inconclusive_intermediate_baseline() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})

    for lane in ("GR", "SR"):
        row = rows[lane]
        source_packet04 = _read_json(REPO_ROOT / row["source_packet04_artifact_path"])
        source_payload = source_packet04.get("payload", {})
        assert source_payload.get("decision") == "INCONCLUSIVE_v0", (
            f"{lane}: packet-05 enablement requires packet-04 INCONCLUSIVE baseline."
        )
        assert source_payload.get("evidence_tier") in {"INTERMEDIATE_v0", "DISCHARGE_GRADE_v0"}, (
            f"{lane}: packet-05 enablement requires packet-04 evidence tier at least INTERMEDIATE_v0."
        )

        packet05 = _read_json(REPO_ROOT / row["artifact_path"])
        payload = packet05.get("payload", {})
        assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
        assert payload.get("decision") in {"INCONCLUSIVE_v0", "RETAIN_v0", "PRUNE_v0"}
        if payload.get("decision") != "INCONCLUSIVE_v0":
            assert (REPO_ROOT / row["override_criteria_path"]).exists(), (
                f"{lane}: non-inconclusive packet-05 decisions require override criteria surface."
            )
