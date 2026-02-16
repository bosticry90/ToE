from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
ALIGNMENT_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md"
)
ROADMAP_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CHECKLIST_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md"
)
NEWTONIAN_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md"
)
ACTION_RAC_STANCE_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ACTION_RAC_STANCE_v0.md"
)
STATE_DOC = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def test_action_rac_retirement_alignment_doc_is_present_and_tokenized() -> None:
    text = _read(ALIGNMENT_DOC)
    for token in [
        "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0",
        "TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN",
        "## Required Alignment Deliverables (all required)",
        "## Mandatory Failure Triggers",
        "## Discharged Alignment Endpoint Definition (v0 conditional-publish posture)",
        "Alignment adjudication token (machine-checkable):",
        "ALIGNMENT_ADJUDICATION: <allowed value>",
        "ALIGNMENT_ADJUDICATION: NOT_YET_DISCHARGED",
        "conditional-publish endpoint",
        "hAction",
        "hRAC",
        "BLK-01",
        "BLK-02",
        "FN-DERIVE_default_quotient_hAction_provenance_v0.md",
        "FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md",
        "FN-DERIVE_default_quotient_bridge_discharge_object_v0.md",
    ]:
        assert token in text, f"Action/RAC retirement-alignment doc missing token: {token}"


def test_action_rac_retirement_alignment_target_is_wired_across_control_surfaces() -> None:
    roadmap = _read(ROADMAP_DOC)
    checklist = _read(CHECKLIST_DOC)
    newtonian = _read(NEWTONIAN_DOC)
    stance = _read(ACTION_RAC_STANCE_DOC)
    state = _read(STATE_DOC)

    required = [
        "TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN",
        "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md",
    ]
    for token in required:
        assert token in roadmap, f"Roadmap missing action/RAC alignment token: {token}"
        assert token in checklist, f"Checklist missing action/RAC alignment token: {token}"
        assert token in newtonian, f"Newtonian target missing action/RAC alignment token: {token}"
        assert token in stance, f"Action/RAC stance doc missing alignment pointer token: {token}"
        assert token in state, f"State inventory missing action/RAC alignment token: {token}"


def test_action_rac_alignment_adjudication_enum_is_singleton_and_controls_state_blocker_phrase() -> None:
    text = _read(ALIGNMENT_DOC)
    state = _read(STATE_DOC)

    adjudications = re.findall(
        r"^\s*-\s*`ALIGNMENT_ADJUDICATION:\s*(NOT_YET_DISCHARGED|DISCHARGED_CONDITIONAL_PUBLISH_v0)`\s*$",
        text,
        flags=re.MULTILINE,
    )
    assert len(adjudications) == 1, (
        "Action/RAC alignment target must contain exactly one alignment adjudication token."
    )

    has_action_rac_blocker_phrase = (
        "dominant remaining blockers are explicit action/RAC retirement alignment plus conservation compatibility `TOE-GR-CONS-01`"
        in state
    )
    if adjudications[0] == "DISCHARGED_CONDITIONAL_PUBLISH_v0":
        assert not has_action_rac_blocker_phrase, (
            "State inventory cannot keep action/RAC retirement alignment in the "
            "dominant blocker summary after DISCHARGED_CONDITIONAL_PUBLISH_v0 is set."
        )
    else:
        assert has_action_rac_blocker_phrase, (
            "State inventory must keep action/RAC retirement alignment in the "
            "dominant blocker summary while NOT_YET_DISCHARGED is set."
        )
