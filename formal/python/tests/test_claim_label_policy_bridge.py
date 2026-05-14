from __future__ import annotations

from formal.python.tools.claim_label_policy import (
    CURRENT_RELEASE_LABELS,
    is_current_release_label,
    is_legacy_label_allowed,
    validate_labels,
    validate_release_claim_row,
)


def test_current_release_labels_are_accepted_in_release_contexts() -> None:
    for label in CURRENT_RELEASE_LABELS:
        assert is_current_release_label(label)
        assert validate_labels(label, [], "v01_alpha_ledger") == []


def test_legacy_labels_are_machine_context_bounded() -> None:
    assert is_legacy_label_allowed("T-PROVED", "historical")
    assert is_legacy_label_allowed("T-CONDITIONAL", "archived_packet")
    assert not is_legacy_label_allowed("T-PROVED", "active_release")
    assert not is_legacy_label_allowed("T-CONDITIONAL", "v01_alpha_ledger")


def test_legacy_labels_fail_in_release_facing_contexts() -> None:
    errors = validate_labels("T-PROVED", ["S-SUPPLIED"], "active_release")
    assert "legacy label 'T-PROVED' is not allowed in 'active_release'" in errors


def test_t_lean_uncond_requires_strict_dependency_audit() -> None:
    row = {
        "primary_label": "T-LEAN-UNCOND",
        "supporting_labels": [],
        "context_type": "v01_alpha_ledger",
        "dependency_audit": {"audit_status": "pending"},
    }
    assert validate_release_claim_row(row) == [
        "T-LEAN-UNCOND requires dependency_audit.audit_status=unconditional_certified"
    ]

    row["dependency_audit"] = {"audit_status": "unconditional_certified"}
    assert validate_release_claim_row(row) == []
