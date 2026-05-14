from __future__ import annotations

CURRENT_RELEASE_LABELS = frozenset(
    {
        "T-LEAN-UNCOND",
        "T-LEAN-COND",
        "T-LEAN-AXIOMED",
        "E-REPRO",
        "S-SUPPLIED",
        "B-BLOCKED",
        "P-POLICY",
        "H-HYP",
    }
)

LEGACY_LABELS = frozenset(
    {
        "T-PROVED",
        "T-CONDITIONAL",
        "DISCHARGED_v0",
        "DISCHARGED_CONDITIONAL_PUBLISH_v0",
        "DISCHARGED_CONDITIONAL_v0",
        "SATISFIED_v0_DISCRETE",
        "PUBLISHED_POLICY_BASELINE_2026Q1",
        "NOT_YET_",
        "LOCKED",
    }
)

ACTIVE_RELEASE_CONTEXTS = frozenset(
    {
        "active_release",
        "active_public_summary",
        "v01_alpha_ledger",
    }
)

LEGACY_ALLOWED_CONTEXTS = frozenset(
    {
        "historical",
        "archived_packet",
        "unmigrated_nonrelease",
    }
)

KNOWN_CONTEXT_TYPES = ACTIVE_RELEASE_CONTEXTS | LEGACY_ALLOWED_CONTEXTS


def is_current_release_label(label: str) -> bool:
    return label in CURRENT_RELEASE_LABELS


def is_legacy_label_allowed(label: str, context_type: str) -> bool:
    if context_type not in KNOWN_CONTEXT_TYPES:
        return False
    return label in LEGACY_LABELS and context_type in LEGACY_ALLOWED_CONTEXTS


def validate_labels(
    primary_label: str,
    supporting_labels: list[str] | tuple[str, ...],
    context_type: str,
) -> list[str]:
    errors: list[str] = []
    if context_type not in KNOWN_CONTEXT_TYPES:
        errors.append(f"unknown context_type: {context_type!r}")
        return errors

    labels = [primary_label, *list(supporting_labels)]
    for label in labels:
        if is_current_release_label(label):
            continue
        if is_legacy_label_allowed(label, context_type):
            continue
        if label in LEGACY_LABELS and context_type in ACTIVE_RELEASE_CONTEXTS:
            errors.append(f"legacy label {label!r} is not allowed in {context_type!r}")
        else:
            errors.append(f"unknown claim label {label!r}")

    return errors


def validate_release_claim_row(row: dict) -> list[str]:
    errors: list[str] = []
    context_type = str(row.get("context_type", "v01_alpha_ledger"))
    primary_label = str(row.get("primary_label", ""))
    supporting_labels = row.get("supporting_labels", [])
    if not isinstance(supporting_labels, list):
        errors.append("supporting_labels must be a list")
        supporting_labels = []

    errors.extend(validate_labels(primary_label, supporting_labels, context_type))

    if primary_label == "T-LEAN-UNCOND":
        audit = row.get("dependency_audit", {})
        if not isinstance(audit, dict) or audit.get("audit_status") != "unconditional_certified":
            errors.append("T-LEAN-UNCOND requires dependency_audit.audit_status=unconditional_certified")

    return errors
