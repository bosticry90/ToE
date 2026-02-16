from __future__ import annotations

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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _extract_gap_blocks(text: str, *, gap_id: str) -> list[str]:
    marker_re = re.compile(rf"^GapID:\s*{re.escape(gap_id)}\s*$", flags=re.MULTILINE)
    blocks: list[str] = []
    for m in marker_re.finditer(text):
        start = m.start()
        nxt = re.search(r"^GapID:\s*\S+\s*$", text[m.end() :], flags=re.MULTILINE)
        if nxt is None:
            blocks.append(text[start:])
        else:
            blocks.append(text[start : m.end() + nxt.start()])
    if not blocks:
        raise AssertionError(f"Could not find exact gap marker for GapID: {gap_id!r}")
    return blocks


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def test_comp_fn_derive_block_records_non_tautological_rep32_bridge_progress() -> None:
    text = STATE_PATH.read_text(encoding="utf-8")
    blocks = _extract_gap_blocks(text, gap_id="COMP-FN-DERIVE")
    assert len(blocks) == 1, "Expected exactly one COMP-FN-DERIVE block; remove duplicates."
    block = blocks[0]

    status = _first_field(block, "Status") or ""
    assert "In progress" in status
    assert "non-tautological EL/P derivation route" in status

    evidence = _first_field(block, "Evidence path") or ""
    required_evidence = [
        "formal/toe_formal/ToeFormal/Variational/ActionToFirstVariationBridgeRep32.lean",
        "formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean",
        "formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md",
        "formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md",
        "formal/markdown/locks/functionals/FN-DERIVE_default_quotient_bridge_discharge_object_v0.md",
        "formal/markdown/locks/functionals/FN-DERIVE_EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions_v0.md",
        "formal/python/tests/test_lean_non_tautological_el_derivation_rep32.py",
        "formal/python/tests/test_lean_non_tautological_el_derivation_rep32_build_guard.py",
        "formal/python/tests/test_fn_derive_default_quotient_discharge_artifacts.py",
    ]
    for token in required_evidence:
        assert token in evidence, f"Missing COMP-FN-DERIVE evidence token: {token}"

    assert "ActionRep32ELMatchesP_of_bridge_and_finiteDifferenceRepresentsP" in block


def test_next_required_action_tracks_remaining_fn_bridge_discharge_only() -> None:
    text = STATE_PATH.read_text(encoding="utf-8")
    assert "NEXT REQUIRED ACTION" in text
    assert "ActionRep32FiniteDifferenceRepresentsP (ε, hε)" in text
    assert "then replace evolution linkage assumptions" not in text


def test_next_required_action_includes_explicit_default_path_checklist_and_rac_policy() -> None:
    text = STATE_PATH.read_text(encoding="utf-8")
    required_tokens = [
        "Remaining default-quotient discharge checklist (COMP-FN-DERIVE)",
        "`hAction` source:",
        "`hRAC` source:",
        "Bridge-side source:",
        "FN-DERIVE_default_quotient_hAction_provenance_v0.md",
        "FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md",
        "FN-DERIVE_default_quotient_bridge_discharge_object_v0.md",
        "FN-DERIVE_EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions_v0.md",
        "Rep32CubicLaneAssumptions.hAction",
        "RACRep32CubicObligationSet",
        "ActionRep32FiniteDifferenceRepresentsP_declared_g_of_action_and_obligation_set",
        "EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions",
        "FN-DERIVE scope statement (paper-facing):",
        "RAC is policy-level",
        "RAC completion policy (inevitability plan)",
        "declared admissibility principle (policy-level)",
        "Plan-complete criterion (policy-level)",
        "Theorem-complete criterion (future)",
    ]
    for token in required_tokens:
        assert token in text, f"Missing FN blocker checklist/RAC policy token: {token}"
