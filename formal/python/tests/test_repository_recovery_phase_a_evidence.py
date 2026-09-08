from __future__ import annotations

from formal.python.tools import repository_recovery_phase_a_evidence as evidence


def test_phase_a_constants_bind_audited_state() -> None:
    assert evidence.AUDITED_COMMIT == "75af1d110a57df26344ca151ccd26b9f5c1f7736"
    assert evidence.REGISTRY_BASE_COMMIT == "0e194f72"
    assert evidence.EXPECTED_DIRTY_COUNT == 629
    assert evidence.EXPECTED_TRACKED_DIRTY_COUNT == 7
    assert evidence.EXPECTED_UNTRACKED_COUNT == 622


def test_classification_rules_keep_scalar_work_noncurrent() -> None:
    classification, rule, confidence, disposition = evidence._classification(
        "formal/python/tools/scalar_only_yukawa_candidate.py", "??"
    )
    assert classification == "SCIENTIFIC_ARTIFACT"
    assert rule == "path_rule_scalar_yukawa_lane"
    assert confidence == "HIGH"
    assert disposition == "PRESERVE_NONCURRENT_NO_FURTHER_EXECUTION"


def test_classification_does_not_treat_extension_as_authority() -> None:
    classification, _, confidence, disposition = evidence._classification(
        "notes/unknown.json", "??"
    )
    assert classification == "UNKNOWN_MANUAL_REVIEW"
    assert confidence == "LOW"
    assert disposition == "PRESERVE_PENDING_MANUAL_REVIEW"
