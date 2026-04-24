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
PACKET02_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_empirical_progression_policy_surface_is_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    protocol_text = _read(PROTOCOL_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    state_text = _read(STATE_PATH)

    assert matrix.get("matrix_id") == "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET_MATRIX_v0"
    assert matrix.get("matrix_version") == 3
    assert matrix.get("progression_policy") == "NO_DIRECT_PRUNE_WITH_SCAFFOLD_UNCERTAINTY"
    assert matrix.get("progression_mode") == "CYCLE_ORDERED_BOUNDED_NONCLAIM"
    assert matrix.get("allowed_evidence_tiers") == ["SCAFFOLD_v0", "INTERMEDIATE_v0", "DISCHARGE_GRADE_v0"]
    assert matrix.get("prune_min_evidence_tier") == "INTERMEDIATE_v0"

    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PRUNE_GUARD_v0") == (
        "NO_DIRECT_PRUNE_WITH_SCAFFOLD_UNCERTAINTY"
    )
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROGRESSION_MODE_v0") == (
        "CYCLE_ORDERED_BOUNDED_NONCLAIM"
    )
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_01_BASELINE_DECISION_v0") == (
        "INCONCLUSIVE_ONLY_UNTIL_PACKET02_OR_HIGHER"
    )
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_02_DECISION_ELIGIBILITY_v0") == (
        "RETAIN_OR_PRUNE_ALLOWED_WITH_PROTOCOL_GUARDS"
    )
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_EVIDENCE_TIERS_v0") == (
        "SCAFFOLD_INTERMEDIATE_DISCHARGE_GRADE"
    )
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PRUNE_MIN_EVIDENCE_TIER_v0") == (
        "INTERMEDIATE_v0"
    )

    for ref in (
        "formal/python/tests/test_foundational_empirical_packet_progression_policy_gate.py",
        "formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET_MATRIX_v0.json",
    ):
        assert ref in roadmap_text, f"Roadmap must pin `{ref}`."
        assert ref in state_text or ref in inventory_text, f"Compact-State or central inventory must pin `{ref}`."


def test_empirical_progression_policy_disallows_direct_prune_with_scaffold_uncertainty() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and rows

    allowed_evidence_tiers = set(matrix.get("allowed_evidence_tiers", []))
    assert allowed_evidence_tiers == {"SCAFFOLD_v0", "INTERMEDIATE_v0", "DISCHARGE_GRADE_v0"}

    evidence_rank = {
        "SCAFFOLD_v0": 0,
        "INTERMEDIATE_v0": 1,
        "DISCHARGE_GRADE_v0": 2,
    }
    prune_min_tier = matrix.get("prune_min_evidence_tier")
    assert prune_min_tier == "INTERMEDIATE_v0"

    for lane, row in rows.items():
        artifact_path = REPO_ROOT / row["artifact_path"]
        artifact = _read_json(artifact_path)
        payload = artifact.get("payload", {})
        decision = payload.get("decision")
        uncertainty = str(payload.get("uncertainty_annotation", ""))
        evidence_tier = payload.get("evidence_tier")

        assert evidence_tier in allowed_evidence_tiers, (
            f"{lane}: evidence_tier must be in allowed evidence tier set."
        )

        if decision == "PRUNE_v0":
            assert "scaffold" not in uncertainty.lower(), (
                f"{lane}: direct PRUNE_v0 is forbidden while uncertainty remains scaffold-level."
            )
            assert evidence_rank[evidence_tier] >= evidence_rank[prune_min_tier], (
                f"{lane}: PRUNE_v0 requires evidence_tier >= {prune_min_tier}."
            )

        assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM", (
            f"{lane}: progression policy requires bounded non-claim packet status."
        )


def test_packet01_baseline_decision_is_explicitly_inconclusive() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and rows

    for lane, row in rows.items():
        artifact_path = REPO_ROOT / row["artifact_path"]
        artifact = _read_json(artifact_path)
        payload = artifact.get("payload", {})
        assert payload.get("decision") == "INCONCLUSIVE_v0", (
            f"{lane}: packet-01 baseline decision must remain INCONCLUSIVE_v0 until packet02-or-higher policy transition."
        )


def test_packet02_decision_eligibility_contract_when_present() -> None:
    if not PACKET02_MATRIX_PATH.exists():
        return

    packet02_matrix = _read_json(PACKET02_MATRIX_PATH)
    rows = packet02_matrix.get("rows", {})
    assert isinstance(rows, dict) and rows

    for lane, row in rows.items():
        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        payload = artifact.get("payload", {})
        assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM", f"{lane}: packet-02 status drift."
        assert payload.get("decision") in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}, f"{lane}: invalid packet-02 decision."
        assert payload.get("evidence_tier") in {"INTERMEDIATE_v0", "DISCHARGE_GRADE_v0"}, f"{lane}: invalid packet-02 evidence tier."

        eligibility = payload.get("decision_eligibility")
        assert isinstance(eligibility, dict), f"{lane}: missing packet-02 decision_eligibility object."
        assert eligibility.get("retain_allowed") is True, f"{lane}: retain_allowed must be true."
        assert eligibility.get("prune_allowed") is True, f"{lane}: prune_allowed must be true."
        assert eligibility.get("prune_guard_satisfied") is True, f"{lane}: prune_guard_satisfied must be true."

        if payload.get("decision") == "PRUNE_v0":
            uncertainty = str(payload.get("uncertainty_annotation", "")).lower()
            assert "scaffold" not in uncertainty, f"{lane}: scaffold uncertainty cannot support PRUNE_v0."
