from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ov01_fit_family_robustness import (
    OV01FitFamilyRobustnessReport,
    ov01_fit_family_robustness_failure_reasons,
)


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON record block")
    return json.loads(m.group(1))


def _report_from_lock_payload(payload: dict) -> OV01FitFamilyRobustnessReport:
    return OV01FitFamilyRobustnessReport(
        config_tag=str(payload["config_tag"]),
        adequacy_policy=str(payload.get("adequacy_policy", "unknown")),
        fn_fingerprint=str(payload["fn_fingerprint"]),
        linear_report_fingerprint=str(payload["linear_report_fingerprint"]),
        curved_report_fingerprint=str(payload["curved_report_fingerprint"]),
        r_max_linear=float(payload["r_max_linear"]),
        r_rms_linear=float(payload["r_rms_linear"]),
        r_max_curved=float(payload["r_max_curved"]),
        r_rms_curved=float(payload["r_rms_curved"]),
        q_ratio=float(payload["q_ratio"]),
        q_threshold=float(payload["q_threshold"]),
        curved_adequacy_passes=bool(payload["curved_adequacy_passes"]),
        prefer_curved=bool(payload["prefer_curved"]),
        robustness_failed=bool(payload["robustness_failed"]),
    )


def test_post_path2_policy_state_is_clean_and_interpretable() -> None:
    # OV-04x is decisive under DQ-01_v1.
    ov04x_lock = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-04x_fit_family_robustness_DS02_lowk.md"
    )
    rep04 = _report_from_lock_payload(_extract_json_block(ov04x_lock.read_text(encoding="utf-8")))
    reasons04 = ov01_fit_family_robustness_failure_reasons(rep04)

    assert rep04.curved_adequacy_passes is True
    assert rep04.prefer_curved is True
    assert rep04.robustness_failed is False
    assert reasons04 == []

    # OV-03x remains undecided only because q_ratio is above threshold.
    ov03x_lock = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-03x_fit_family_robustness_B1_dataset.md"
    )
    rep03 = _report_from_lock_payload(_extract_json_block(ov03x_lock.read_text(encoding="utf-8")))
    reasons03 = ov01_fit_family_robustness_failure_reasons(rep03)

    assert rep03.curved_adequacy_passes is True
    assert rep03.prefer_curved is False
    assert rep03.robustness_failed is True
    assert "q_ratio_above_threshold" in reasons03
    assert "curved_adequacy_failed" not in reasons03

    # Overlap-only comparison remains one-decisive and agreement is false.
    xd04_lock = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-XD-04_overlap_only_preference_comparison.md"
    )
    xd04 = _extract_json_block(xd04_lock.read_text(encoding="utf-8"))

    assert xd04["schema"] == "OV-XD-04/v1"
    assert xd04["decisiveness"] == "one-decisive"
    assert bool(xd04["agreement"]) is False
