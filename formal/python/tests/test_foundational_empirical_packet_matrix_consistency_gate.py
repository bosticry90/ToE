from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET_MATRIX_v0.json"
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
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


def test_empirical_packet_matrix_surface_is_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    roadmap = _read(ROADMAP_PATH)
    inventory = _read(INVENTORY_PATH)
    state = _read(STATE_PATH)

    assert matrix.get("matrix_id") == "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET_MATRIX_v0"
    assert matrix.get("matrix_version") == 3
    assert matrix.get("protocol_doc") == "formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"

    for ref in (
        "formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET_MATRIX_v0.json",
        "formal/python/tests/test_foundational_empirical_packet_matrix_consistency_gate.py",
    ):
        assert ref in roadmap, f"Roadmap must pin `{ref}`."
        assert ref in state or ref in inventory, f"Compact-State or central inventory must pin `{ref}`."


def test_empirical_packet_matrix_rows_match_docs_artifacts_and_protocol() -> None:
    matrix = _read_json(MATRIX_PATH)
    protocol_text = _read(PROTOCOL_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    state_text = _read(STATE_PATH)

    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_DECISION_SET_v0") == "RETAIN_PRUNE_INCONCLUSIVE_ONLY"

    allowed_decisions = set(matrix.get("allowed_decisions", []))
    assert allowed_decisions == {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}

    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and rows, "Matrix must define non-empty packet rows."

    for lane, row in rows.items():
        doc_path = REPO_ROOT / row["doc_path"]
        artifact_path = REPO_ROOT / row["artifact_path"]
        gate_path = REPO_ROOT / row["gate_path"]

        doc_text = _read(doc_path)
        assert artifact_path.exists(), f"{lane}: missing artifact `{artifact_path}`."
        assert gate_path.exists(), f"{lane}: missing gate `{gate_path}`."

        artifact = _read_json(artifact_path)
        payload = artifact.get("payload", {})
        assert isinstance(payload, dict), f"{lane}: payload must be object."

        status = _extract_token(doc_text, row["status_token"])
        artifact_id = _extract_token(doc_text, row["artifact_token"])
        gate_value = _extract_token(doc_text, row["gate_token"])
        decision = _extract_token(doc_text, row["decision_token"])
        evidence_tier = _extract_token(doc_text, row["evidence_tier_token"])

        assert status == "RUN_BOUNDED_v0_NONCLAIM", f"{lane}: status drift."
        assert gate_value == "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED", f"{lane}: gate drift."
        assert decision in allowed_decisions, f"{lane}: decision outside allowed set."
        assert evidence_tier in set(matrix.get("allowed_evidence_tiers", [])), (
            f"{lane}: doc evidence tier outside matrix allowed tiers."
        )

        assert artifact.get("artifact_id") == artifact_id, f"{lane}: artifact_id mismatch."
        assert payload.get("status") == status, f"{lane}: payload status mismatch."
        assert payload.get("decision") == decision, f"{lane}: payload decision mismatch."
        assert payload.get("evidence_tier") == evidence_tier, f"{lane}: payload evidence_tier mismatch."

        for field in (
            "artifact_pointer",
            "bridge_pointer",
            "prediction_pointer",
            "discriminator_output_pointer",
            "uncertainty_annotation",
            "bounded_validity_window",
            "evidence_tier",
        ):
            assert isinstance(payload.get(field), str) and payload.get(field), f"{lane}: missing payload field `{field}`."

        for ref in (row["doc_path"], row["gate_path"]):
            assert ref in roadmap_text, f"{lane}: roadmap must pin `{ref}`."
            assert ref in state_text or ref in inventory_text, f"{lane}: compact-State or central inventory must pin `{ref}`."


def test_intermediate_evidence_rows_require_promotion_surfaces() -> None:
    matrix = _read_json(MATRIX_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    state_text = _read(STATE_PATH)

    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and rows, "Matrix must define non-empty packet rows."

    found_intermediate = False
    for lane, row in rows.items():
        artifact_path = REPO_ROOT / row["artifact_path"]
        artifact = _read_json(artifact_path)
        payload = artifact.get("payload", {})
        evidence_tier = payload.get("evidence_tier")

        if evidence_tier != "INTERMEDIATE_v0":
            continue

        found_intermediate = True
        doc_path = row["doc_path"]
        assert doc_path.endswith("_EMPIRICAL_COMPARISON_PACKET_01_v0.md"), (
            f"{lane}: unexpected doc naming for promotion derivation."
        )

        promotion_doc_rel = doc_path.replace(
            "_EMPIRICAL_COMPARISON_PACKET_01_v0.md",
            "_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md",
        )
        assert promotion_doc_rel in roadmap_text, f"{lane}: roadmap must pin `{promotion_doc_rel}` for INTERMEDIATE evidence tier."
        assert promotion_doc_rel in state_text or promotion_doc_rel in inventory_text, (
            f"{lane}: compact-State or central inventory must pin `{promotion_doc_rel}` for INTERMEDIATE evidence tier."
        )
        assert (REPO_ROOT / promotion_doc_rel).exists(), (
            f"{lane}: expected promotion doc file missing `{promotion_doc_rel}`."
        )

        gate_path = row["gate_path"]
        assert gate_path.endswith("_empirical_comparison_packet_01_gate.py"), (
            f"{lane}: unexpected gate naming for promotion derivation."
        )
        promotion_gate_rel = gate_path.replace(
            "_empirical_comparison_packet_01_gate.py",
            "_empirical_packet_01_evidence_promotion_gate.py",
        )
        assert promotion_gate_rel in roadmap_text, f"{lane}: roadmap must pin `{promotion_gate_rel}` for INTERMEDIATE evidence tier."
        assert promotion_gate_rel in state_text or promotion_gate_rel in inventory_text, (
            f"{lane}: compact-State or central inventory must pin `{promotion_gate_rel}` for INTERMEDIATE evidence tier."
        )
        assert (REPO_ROOT / promotion_gate_rel).exists(), (
            f"{lane}: expected promotion gate file missing `{promotion_gate_rel}`."
        )

    assert found_intermediate, "At least one INTERMEDIATE evidence-tier row is expected for promotion-lane coverage."
