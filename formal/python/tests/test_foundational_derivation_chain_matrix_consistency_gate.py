from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

SUFFIXES = [
    "ACTION_STAGE_STATUS_v0",
    "VARIATION_STAGE_STATUS_v0",
    "BRIDGE_STAGE_STATUS_v0",
    "OPERATOR_STAGE_STATUS_v0",
    "TRANSPORT_STAGE_STATUS_v0",
    "RESIDUAL_LAW_STAGE_STATUS_v0",
    "REGIME_LIMIT_STAGE_STATUS_v0",
]

RANK = {
    "NOT_STARTED_v0": 0,
    "SCAFFOLD_PINNED_v0": 1,
    "RUN_BOUNDED_v0_NONCLAIM": 2,
    "COMPLETE_BOUNDED_v0": 3,
    "DISCHARGED_v0_DERIVATION_GRADE": 4,
}

PHASE_RANK = {
    "NOT_STARTED_v0": 0,
    "SCAFFOLD_PINNED_NONCLAIM": 1,
    "RUN_BOUNDED_v0_NONCLAIM": 2,
    "COMPLETE_BOUNDED_v0": 3,
    "DISCHARGED_v0_DERIVATION_GRADE": 4,
    "DISCHARGED_v0": 4,
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_chain_matrix_surface_is_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    roadmap = _read(ROADMAP_PATH)
    state = _read(STATE_PATH)

    assert matrix.get("matrix_id") == "FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0"
    assert matrix.get("matrix_version") == 3
    assert matrix.get("standard_doc") == "formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md"

    for ref in (
        "formal/docs/paper/FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json",
        "formal/python/tests/test_foundational_derivation_chain_matrix_consistency_gate.py",
    ):
        assert ref in roadmap
        assert ref in state


def test_chain_matrix_matches_lane_docs_and_ordering() -> None:
    matrix = _read_json(MATRIX_PATH)
    lanes = matrix.get("lanes", {})
    assert isinstance(lanes, dict) and lanes

    for lane, row in lanes.items():
        target_doc = REPO_ROOT / row["target_doc"]
        doc_text = _read(target_doc)

        ranks = []
        for suffix in SUFFIXES:
            expected = row[suffix]
            assert expected in RANK, f"{lane}: invalid matrix status `{expected}` for {suffix}."
            token = f"{lane}_{suffix}"
            got = _extract_token(doc_text, token)
            assert got == expected, f"{lane}: matrix/doc drift for `{token}`."
            ranks.append(RANK[got])

        assert ranks == sorted(ranks), f"{lane}: stage ordering must be non-decreasing."


def test_chain_matrix_phase_rows_match_cross_surfaces_and_ordering() -> None:
    matrix = _read_json(MATRIX_PATH)
    phase_rows = matrix.get("phase_rows", {})
    assert isinstance(phase_rows, dict) and phase_rows, "Matrix must define non-empty `phase_rows`."

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for pillar, row in phase_rows.items():
        for phase in ("m2", "m3", "m4"):
            assert phase in row, f"{pillar}: missing phase row `{phase}`."
            phase_row = row[phase]
            source_doc = REPO_ROOT / phase_row["source_doc"]
            source_text = _read(source_doc)
            token = phase_row["status_token"]
            expected = phase_row["expected_status"]

            assert expected in PHASE_RANK, f"{pillar}/{phase}: unsupported expected status `{expected}`."
            assert _extract_token(source_text, token) == expected, f"{pillar}/{phase}: source-doc drift for `{token}`."
            assert _extract_token(roadmap_text, token) == expected, f"{pillar}/{phase}: roadmap drift for `{token}`."
            assert _extract_token(state_text, token) == expected, f"{pillar}/{phase}: state drift for `{token}`."

        m2_status = row["m2"]["expected_status"]
        m3_status = row["m3"]["expected_status"]
        m4_status = row["m4"]["expected_status"]

        m2_rank = PHASE_RANK[m2_status]
        m3_rank = PHASE_RANK[m3_status]
        m4_rank = PHASE_RANK[m4_status]

        assert m2_rank <= m3_rank <= m4_rank, (
            f"{pillar}: cross-phase maturity must be non-decreasing (M2 <= M3 <= M4)."
        )

        if m4_rank >= PHASE_RANK["COMPLETE_BOUNDED_v0"]:
            assert m3_rank >= PHASE_RANK["COMPLETE_BOUNDED_v0"], (
                f"{pillar}: M4 complete posture requires M3 complete posture."
            )
            assert m2_rank >= PHASE_RANK["COMPLETE_BOUNDED_v0"], (
                f"{pillar}: M4 complete posture requires M2 complete posture."
            )


def test_chain_matrix_m2_subphase_rows_match_cross_surfaces() -> None:
    matrix = _read_json(MATRIX_PATH)
    phase_rows = matrix.get("phase_rows", {})
    m2_subphase_rows = matrix.get("m2_subphase_rows", {})
    assert isinstance(m2_subphase_rows, dict) and m2_subphase_rows, "Matrix must define non-empty `m2_subphase_rows`."

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    suffixes = (
        "ANALYTIC_COMPLETENESS_STATUS_v0",
        "CANONICAL_EQUIVALENCE_STATUS_v0",
        "ASSUMPTION_MINIMIZATION_STATUS_v0",
        "LITERATURE_ALIGNMENT_STATUS_v0",
    )

    for pillar, sub_row in m2_subphase_rows.items():
        assert pillar in phase_rows, f"{pillar}: missing phase row entry required by m2_subphase_rows."
        source_doc = REPO_ROOT / sub_row["source_doc"]
        source_text = _read(source_doc)

        # Keep source-doc linkage explicit with the declared M2 phase row source.
        assert sub_row["source_doc"] == phase_rows[pillar]["m2"]["source_doc"], (
            f"{pillar}: m2_subphase source_doc must match phase_rows.m2.source_doc."
        )

        for suffix in suffixes:
            expected = sub_row[suffix]
            assert expected in PHASE_RANK, f"{pillar}: unsupported subphase status `{expected}` for `{suffix}`."
            token = f"{pillar}_M2_{suffix}"
            assert _extract_token(source_text, token) == expected, f"{pillar}: source-doc drift for `{token}`."
            assert _extract_token(roadmap_text, token) == expected, f"{pillar}: roadmap drift for `{token}`."
            assert _extract_token(state_text, token) == expected, f"{pillar}: state drift for `{token}`."

        m2_phase_expected = phase_rows[pillar]["m2"]["expected_status"]
        m2_phase_rank = PHASE_RANK[m2_phase_expected]
        subphase_min_rank = min(PHASE_RANK[sub_row[suffix]] for suffix in suffixes)

        # If M2 phase is complete, subphases must at least be explicitly scaffolded.
        if m2_phase_rank >= PHASE_RANK["COMPLETE_BOUNDED_v0"]:
            assert subphase_min_rank >= PHASE_RANK["SCAFFOLD_PINNED_NONCLAIM"], (
                f"{pillar}: M2 complete posture requires explicit subphase scaffolds."
            )


def test_m4_seam_docs_pin_full_stage_bundles() -> None:
    matrix = _read_json(MATRIX_PATH)
    phase_rows = matrix.get("phase_rows", {})
    assert isinstance(phase_rows, dict) and phase_rows

    for pillar, row in phase_rows.items():
        m4 = row.get("m4", {})
        source_doc = REPO_ROOT / m4["source_doc"]
        source_text = _read(source_doc)
        lane = f"{pillar}_M4"

        ranks = []
        for suffix in SUFFIXES:
            token = f"{lane}_{suffix}"
            value = _extract_token(source_text, token)
            assert value in RANK, f"{lane}: unsupported M4 stage status `{value}` for `{token}`."
            ranks.append(RANK[value])

        assert ranks == sorted(ranks), f"{lane}: M4 stage ordering must be non-decreasing."

        m4_expected = m4.get("expected_status")
        assert m4_expected in PHASE_RANK, f"{lane}: unsupported M4 expected status `{m4_expected}`."
        if PHASE_RANK[m4_expected] >= PHASE_RANK["COMPLETE_BOUNDED_v0"]:
            assert all(r >= RANK["COMPLETE_BOUNDED_v0"] for r in ranks), (
                f"{lane}: complete M4 posture requires all M4 stage tokens at COMPLETE_BOUNDED_v0 or higher."
            )
