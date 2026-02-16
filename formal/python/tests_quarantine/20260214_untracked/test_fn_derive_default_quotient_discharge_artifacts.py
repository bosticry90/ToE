from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
STATE_DOC = REPO_ROOT / "State_of_the_Theory.md"
LEAN_LANE = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionRep32CubicLane.lean"
)
HACTION_LOCK = (
    REPO_ROOT
    / "formal"
    / "markdown"
    / "locks"
    / "functionals"
    / "FN-DERIVE_default_quotient_hAction_provenance_v0.md"
)
HRAC_LOCK = (
    REPO_ROOT
    / "formal"
    / "markdown"
    / "locks"
    / "functionals"
    / "FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md"
)
BRIDGE_LOCK = (
    REPO_ROOT
    / "formal"
    / "markdown"
    / "locks"
    / "functionals"
    / "FN-DERIVE_default_quotient_bridge_discharge_object_v0.md"
)
THEOREM_LOCK = (
    REPO_ROOT
    / "formal"
    / "markdown"
    / "locks"
    / "functionals"
    / "FN-DERIVE_EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def test_fn_derive_haction_provenance_artifact_and_state_doc_reference() -> None:
    lock_text = _read(HACTION_LOCK)
    state_text = _read(STATE_DOC)

    required_lock_tokens = [
        "FN-DERIVE/default_quotient_hAction_provenance/v0",
        "Rep32CubicLaneAssumptions.hAction",
        "Rep32_cubic_lane_declared_g",
        "actionRep32.action = actionRep32Cubic declared_g_rep32",
    ]
    for token in required_lock_tokens:
        assert token in lock_text, f"Missing hAction provenance token: {token}"

    required_state_tokens = [
        "FN-DERIVE_default_quotient_hAction_provenance_v0.md",
        "Rep32CubicLaneAssumptions.hAction",
    ]
    for token in required_state_tokens:
        assert token in state_text, f"State doc missing hAction provenance reference: {token}"


def test_fn_derive_hrac_obligation_bundle_is_named_and_referenced() -> None:
    lean_text = _read(LEAN_LANE)
    lock_text = _read(HRAC_LOCK)
    state_text = _read(STATE_DOC)

    required_lean_tokens = [
        "structure RACRep32CubicObligationSet",
        "theorem RAC_Rep32_Cubic_of_obligation_set",
        "theorem RACRep32CubicObligationSet_of_RAC",
    ]
    for token in required_lean_tokens:
        assert token in lean_text, f"Lean lane missing RAC obligation token: {token}"

    required_lock_tokens = [
        "FN-DERIVE/default_quotient_hRAC_obligation_bundle/v0",
        "RACRep32CubicObligationSet",
        "ActionRep32CubicLinearMatchesP declared_g_rep32",
        "ActionRep32CubicNoSecondOrder declared_g_rep32",
        "ActionRep32CubicNoThirdOrder declared_g_rep32",
        "ActionRep32CubicNoFourthOrder declared_g_rep32",
    ]
    for token in required_lock_tokens:
        assert token in lock_text, f"Missing hRAC bundle token: {token}"

    required_state_tokens = [
        "RACRep32CubicObligationSet",
        "RAC_Rep32_Cubic_of_obligation_set",
        "FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md",
    ]
    for token in required_state_tokens:
        assert token in state_text, f"State doc missing hRAC bundle reference: {token}"


def test_fn_derive_bridge_discharge_object_is_pinned_and_referenced() -> None:
    lean_text = _read(LEAN_LANE)
    lock_text = _read(BRIDGE_LOCK)
    state_text = _read(STATE_DOC)

    assert "ActionRep32FiniteDifferenceRepresentsP_declared_g_of_action_and_obligation_set" in lean_text

    required_lock_tokens = [
        "FN-DERIVE/default_quotient_bridge_discharge_object/v0",
        "ActionRep32FiniteDifferenceRepresentsP_declared_g_of_action_and_obligation_set",
        "\"hRAC : RACRep32CubicObligationSet declared_g_rep32\"",
        "\"output\": \"ActionRep32FiniteDifferenceRepresentsP ε hε\"",
    ]
    for token in required_lock_tokens:
        assert token in lock_text, f"Missing bridge discharge artifact token: {token}"

    required_state_tokens = [
        "FN-DERIVE_default_quotient_bridge_discharge_object_v0.md",
        "ActionRep32FiniteDifferenceRepresentsP_declared_g_of_action_and_obligation_set",
    ]
    for token in required_state_tokens:
        assert token in state_text, f"State doc missing bridge discharge reference: {token}"


def test_fn_derive_paper_facing_conditional_theorem_is_pinned_and_inventory_labeled() -> None:
    lean_text = _read(LEAN_LANE)
    lock_text = _read(THEOREM_LOCK)
    state_text = _read(STATE_DOC)

    theorem_name = "EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions"
    assert theorem_name in lean_text, "Missing paper-facing FN-DERIVE conditional theorem."

    required_lock_tokens = [
        "FN-DERIVE/EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions/v0",
        "\"classification\": \"T-CONDITIONAL\"",
        f"\"theorem_name\": \"{theorem_name}\"",
        "\"hAction : actionRep32.action = actionRep32Cubic declared_g_rep32\"",
        "\"hRAC : RACRep32CubicObligationSet declared_g_rep32\"",
    ]
    for token in required_lock_tokens:
        assert token in lock_text, f"Missing theorem lock token: {token}"

    required_state_tokens = [
        "[T-CONDITIONAL]",
        theorem_name,
        "FN-DERIVE_EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions_v0.md",
    ]
    for token in required_state_tokens:
        assert token in state_text, f"State doc missing T-CONDITIONAL theorem inventory token: {token}"
