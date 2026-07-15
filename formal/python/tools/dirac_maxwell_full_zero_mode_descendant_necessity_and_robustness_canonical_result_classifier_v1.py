from __future__ import annotations

import math
from typing import Any


SCIENTIFIC_ROW_COUNT = 14
MATERIAL_GATE = 0.1
DOMINATED_GATE = 0.5
ROBUSTNESS_CLASSES = (
    "NUMERICALLY_BLOCKED",
    "MODEL_DOMAIN_LIMITED",
    "THRESHOLD_SENSITIVE",
    "BROADLY_ROBUST",
    "CONDITIONALLY_ROBUST",
)
DESCENDANT_SIGNIFICANCE_CLASSES = (
    "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL",
    "INTERMEDIATE_DESCENDANT_CONTRIBUTION",
    "DESCENDANT_DOMINATED_REGIME",
)


def _require_bool(payload: dict[str, Any], key: str) -> bool:
    value = payload.get(key)
    if not isinstance(value, bool):
        raise ValueError(f"{key} must be Boolean")
    return value


def _finite_nonnegative(values: Any, key: str) -> list[float]:
    if not isinstance(values, list):
        raise ValueError(f"{key} must be a list")
    result = [float(value) for value in values]
    if any(not math.isfinite(value) or value < 0.0 for value in result):
        raise ValueError(f"{key} must contain finite nonnegative values")
    return result


def classify_registered_result(payload: dict[str, Any]) -> dict[str, Any]:
    """Apply only the v1 frozen precedence; this function never runs simulations."""
    custody_ok = _require_bool(payload, "custody_ok")
    controls_ok = _require_bool(payload, "controls_ok")
    evidence_complete = _require_bool(payload, "evidence_complete")
    model_domain_limited = _require_bool(payload, "model_domain_limited")
    threshold_sensitive = _require_bool(payload, "threshold_sensitive")
    necessity_resolved = _require_bool(payload, "necessity_resolved")
    numerical_floor_resolved = _require_bool(payload, "numerical_floor_resolved")
    row_results = payload.get("row_results")
    if not isinstance(row_results, list) or len(row_results) != SCIENTIFIC_ROW_COUNT:
        raise ValueError("row_results must contain exactly fourteen preregistered rows")
    row_ids = []
    row_passes = []
    for item in row_results:
        if not isinstance(item, dict) or not isinstance(item.get("row_id"), str):
            raise ValueError("every row result needs a row_id")
        if not isinstance(item.get("robustness_pass"), bool):
            raise ValueError("every row result needs a Boolean robustness_pass")
        row_ids.append(item["row_id"])
        row_passes.append(item["robustness_pass"])
    if len(set(row_ids)) != SCIENTIFIC_ROW_COUNT:
        raise ValueError("row result identities must be unique")
    r_perp = _finite_nonnegative(payload.get("r_perp_maxima"), "r_perp_maxima")
    f_exchange = _finite_nonnegative(payload.get("f_exchange_perp"), "f_exchange_perp")

    base = {
        "classifier_id": "DM_ROBUSTNESS_CANONICAL_RESULT_CLASSIFIER_v1",
        "robustness_status": None,
        "descendant_significance_status": None,
        "passing_scientific_row_ids": [row_id for row_id, passed in zip(row_ids, row_passes, strict=True) if passed],
        "failing_scientific_row_ids": [row_id for row_id, passed in zip(row_ids, row_passes, strict=True) if not passed],
        "scientific_claim_authorized": False,
    }
    if not custody_ok:
        return {**base, "execution_status": "B-BLOCKED_CUSTODY", "reason": "custody or matrix completeness failed before scientific classification"}
    if not controls_ok:
        return {**base, "execution_status": "B-BLOCKED_CONTROL_DISCRIMINATION", "reason": "positive or negative controls failed before scientific classification"}
    if not evidence_complete:
        return {**base, "execution_status": "CLASSIFIED_BLOCKED", "robustness_status": "NUMERICALLY_BLOCKED", "reason": "one or more required rows lack classifiable numerical evidence"}
    if model_domain_limited:
        return {**base, "execution_status": "CLASSIFIED_BLOCKED", "robustness_status": "MODEL_DOMAIN_LIMITED", "reason": "one or more rows exit the frozen admitted c-number PDE model domain"}

    if threshold_sensitive:
        robustness = "THRESHOLD_SENSITIVE"
    elif all(row_passes):
        robustness = "BROADLY_ROBUST"
    elif any(row_passes):
        robustness = "CONDITIONALLY_ROBUST"
    else:
        robustness = "NUMERICALLY_BLOCKED"

    significance = None
    significance_reason = "descendant significance unavailable"
    if necessity_resolved and numerical_floor_resolved:
        maximum = max([0.0, *r_perp, *f_exchange])
        if maximum >= DOMINATED_GATE:
            significance = "DESCENDANT_DOMINATED_REGIME"
        elif maximum >= MATERIAL_GATE:
            significance = "INTERMEDIATE_DESCENDANT_CONTRIBUTION"
        else:
            significance = "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL"
        significance_reason = "classified independently from robustness using the frozen 0.1 and 0.5 gates"

    reason = "all fourteen preregistered rows pass" if robustness == "BROADLY_ROBUST" else "a nonempty preregistered passing subdomain remains" if robustness == "CONDITIONALLY_ROBUST" else "frozen sensitivity analysis changes a conclusion" if robustness == "THRESHOLD_SENSITIVE" else "no preregistered row passes; no positive robustness class is available"
    return {
        **base,
        "execution_status": "CLASSIFIED",
        "robustness_status": robustness,
        "descendant_significance_status": significance,
        "reason": reason,
        "descendant_significance_reason": significance_reason,
    }
