from __future__ import annotations

from pathlib import Path
import json
import re
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CANDIDATE_MASTER_ACTION_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"

STANDARD_REL = "formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md"
CANDIDATE_MASTER_ACTION_REL = "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
GATE_REL = "formal/python/tests/test_foundational_derivation_chain_coverage_gate.py"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json"

M3_LANE_TARGETS = {
    "QM_M3": "formal/docs/paper/DERIVATION_TARGET_QM_M3_COMPLETION_PROMOTION_v0.md",
    "GR_M3": "formal/docs/paper/DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md",
    "STAT_M3": "formal/docs/paper/DERIVATION_TARGET_STAT_M3_COMPLETION_PROMOTION_v0.md",
    "COSMO_M3": "formal/docs/paper/DERIVATION_TARGET_COSMO_M3_COMPLETION_PROMOTION_v0.md",
    "EM_M3": "formal/docs/paper/DERIVATION_TARGET_EM_M3_COMPLETION_PROMOTION_v0.md",
    "QFT_M3": "formal/docs/paper/DERIVATION_TARGET_QFT_M3_COMPLETION_PROMOTION_v0.md",
    "SR_M3": "formal/docs/paper/DERIVATION_TARGET_SR_M3_COMPLETION_PROMOTION_v0.md",
}

CHAIN_SUFFIXES = [
    "ACTION_STAGE_STATUS_v0",
    "VARIATION_STAGE_STATUS_v0",
    "BRIDGE_STAGE_STATUS_v0",
    "OPERATOR_STAGE_STATUS_v0",
    "TRANSPORT_STAGE_STATUS_v0",
    "RESIDUAL_LAW_STAGE_STATUS_v0",
    "REGIME_LIMIT_STAGE_STATUS_v0",
]

STATUS_RANK = {
    "NOT_STARTED_v0": 0,
    "SCAFFOLD_PINNED_v0": 1,
    "RUN_BOUNDED_v0_NONCLAIM": 2,
    "COMPLETE_BOUNDED_v0": 3,
    "DISCHARGED_v0_DERIVATION_GRADE": 4,
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert match is not None, f"Missing token `{token_name}`."
    return match.group(1)


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_foundational_derivation_chain_standard_is_globally_pinned() -> None:
    standard_text = _read(STANDARD_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    required_standard_tokens = (
        "FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0",
        "ACTION",
        "VARIATION",
        "BRIDGE",
        "OPERATOR",
        "TRANSPORT",
        "RESIDUAL_LAW",
        "REGIME_LIMIT",
        "<LANE>_ACTION_STAGE_STATUS_v0",
        "<LANE>_VARIATION_STAGE_STATUS_v0",
        "<LANE>_BRIDGE_STAGE_STATUS_v0",
        "<LANE>_OPERATOR_STAGE_STATUS_v0",
        "<LANE>_TRANSPORT_STAGE_STATUS_v0",
        "<LANE>_RESIDUAL_LAW_STAGE_STATUS_v0",
        "<LANE>_REGIME_LIMIT_STAGE_STATUS_v0",
        "NOT_STARTED_v0",
        "SCAFFOLD_PINNED_v0",
        "RUN_BOUNDED_v0_NONCLAIM",
        "COMPLETE_BOUNDED_v0",
        "DISCHARGED_v0_DERIVATION_GRADE",
        CANDIDATE_MASTER_ACTION_REL,
        GATE_REL,
    )
    for token in required_standard_tokens:
        assert token in standard_text, f"Foundational derivation chain standard missing token `{token}`."

    assert STANDARD_REL in roadmap_text, "Roadmap must pin foundational derivation chain standard path."
    assert CANDIDATE_MASTER_ACTION_REL in roadmap_text, "Roadmap must pin candidate master action path."
    assert STANDARD_REL in state_text, "State must pin foundational derivation chain standard path."
    assert CANDIDATE_MASTER_ACTION_REL in state_text, "State must pin candidate master action path."


def test_candidate_master_action_is_chain_aligned() -> None:
    candidate_text = _read(CANDIDATE_MASTER_ACTION_PATH)

    required_candidate_tokens = (
        "TOE_CANDIDATE_MASTER_ACTION_v0",
        "working-form artifact only",
        "explicitly non-canonical",
        "delta S_ToE = 0",
        "ACTION",
        "VARIATION",
        "BRIDGE",
        "OPERATOR",
        "TRANSPORT",
        "RESIDUAL_LAW",
        "REGIME_LIMIT",
        "cross-pillar compatibility",
        "bridge admissibility",
        "transport consistency",
    )
    for token in required_candidate_tokens:
        assert token in candidate_text, f"Candidate master action artifact missing token `{token}`."


def test_m3_lane_targets_pin_full_chain_stage_bundles() -> None:
    for lane_prefix, rel_path in sorted(M3_LANE_TARGETS.items()):
        text = _read(REPO_ROOT / rel_path)

        assert "Foundational derivation-chain stage bundle (v0):" in text, (
            f"{lane_prefix}: missing chain-stage bundle section label."
        )

        for suffix in CHAIN_SUFFIXES:
            token = f"{lane_prefix}_{suffix}"
            value = _extract_token(text, token)
            assert value in STATUS_RANK, f"{lane_prefix}: token `{token}` has invalid status value `{value}`."


def test_m3_lane_chain_stage_progression_is_non_decreasing() -> None:
    for lane_prefix, rel_path in sorted(M3_LANE_TARGETS.items()):
        text = _read(REPO_ROOT / rel_path)
        ranks = []
        for suffix in CHAIN_SUFFIXES:
            token = f"{lane_prefix}_{suffix}"
            value = _extract_token(text, token)
            ranks.append(STATUS_RANK[value])

        assert ranks == sorted(ranks), (
            f"{lane_prefix}: stage progression must be non-decreasing across ACTION->...->REGIME_LIMIT."
        )

        assert ranks[-1] >= STATUS_RANK["RUN_BOUNDED_v0_NONCLAIM"], (
            f"{lane_prefix}: REGIME_LIMIT stage is too immature for M3 completion posture."
        )

        assert ranks[3] >= STATUS_RANK["COMPLETE_BOUNDED_v0"], (
            f"{lane_prefix}: OPERATOR stage must be at least COMPLETE_BOUNDED_v0."
        )

        assert ranks[5] >= STATUS_RANK["COMPLETE_BOUNDED_v0"], (
            f"{lane_prefix}: RESIDUAL_LAW stage must be at least COMPLETE_BOUNDED_v0."
        )


def test_phase_rows_pin_m2_m3_m4_chain_coverage_surfaces() -> None:
    matrix = _read_json(MATRIX_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    phase_rows = matrix.get("phase_rows", {})
    assert isinstance(phase_rows, dict) and phase_rows, "Derivation chain matrix must define non-empty phase rows."

    for pillar, row in sorted(phase_rows.items()):
        for phase in ("m2", "m3", "m4"):
            phase_row = row.get(phase)
            assert isinstance(phase_row, dict), f"{pillar}/{phase}: missing phase-row mapping."

            source_doc_rel = phase_row["source_doc"]
            source_doc_text = _read(REPO_ROOT / source_doc_rel)
            status_token = phase_row["status_token"]
            expected_status = phase_row["expected_status"]

            assert expected_status in {
                "NOT_STARTED_v0",
                "SCAFFOLD_PINNED_NONCLAIM",
                "RUN_BOUNDED_v0_NONCLAIM",
                "COMPLETE_BOUNDED_v0",
                "DISCHARGED_v0",
                "DISCHARGED_v0_DERIVATION_GRADE",
            }, f"{pillar}/{phase}: unsupported expected status `{expected_status}`."

            assert _extract_token(source_doc_text, status_token) == expected_status, (
                f"{pillar}/{phase}: source doc drift for `{status_token}`."
            )
            assert _extract_token(roadmap_text, status_token) == expected_status, (
                f"{pillar}/{phase}: roadmap drift for `{status_token}`."
            )
            assert _extract_token(state_text, status_token) == expected_status, (
                f"{pillar}/{phase}: state drift for `{status_token}`."
            )
