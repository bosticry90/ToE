"""OV-XD-02: deterministic cross-dataset preference agreement record.

Purpose
- Provide a small, deterministic, non-interpretive *record* of whether the
  robustness-only fit-family preference outcomes match across datasets.

Scope / limits
- Summary/record only.
- This is not a physics claim and must not be used for β inference.
- No filesystem I/O.

Design constraints
- Deterministic (no RNG).
- Small surface area.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Literal


OVPreferredFamily = Literal["curved", "undecided"]


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _preferred_family(*, prefer_curved: bool, robustness_failed: bool) -> OVPreferredFamily:
    # Align with OV-01 family selection policy: selection is decisive only when
    # prefer_curved is true and robustness_failed is false.
    prefer = bool(prefer_curved and (not robustness_failed))
    return "curved" if prefer else "undecided"


@dataclass(frozen=True)
class OVXD02PreferenceAgreementRecord:
    config_tag: str

    ov01g_report_fingerprint: str
    ov02x_report_fingerprint: str
    ov03x_report_fingerprint: str

    ov01g_preferred_family: OVPreferredFamily
    ov03x_preferred_family: OVPreferredFamily

    ov02x_all_scenarios_match_baseline: bool

    agreement: bool

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "ov01g_report_fingerprint": self.ov01g_report_fingerprint,
            "ov02x_report_fingerprint": self.ov02x_report_fingerprint,
            "ov03x_report_fingerprint": self.ov03x_report_fingerprint,
            "ov01g_preferred_family": self.ov01g_preferred_family,
            "ov03x_preferred_family": self.ov03x_preferred_family,
            "ov02x_all_scenarios_match_baseline": bool(self.ov02x_all_scenarios_match_baseline),
            "agreement": bool(self.agreement),
        }
        return _sha256_json(payload)


def ovxd02_preference_agreement_record(
    *,
    ov01g_report_fingerprint: str,
    ov01g_prefer_curved: bool,
    ov01g_robustness_failed: bool,
    ov02x_report_fingerprint: str,
    ov02x_all_scenarios_match_baseline: bool,
    ov03x_report_fingerprint: str,
    ov03x_prefer_curved: bool,
    ov03x_robustness_failed: bool,
    config_tag: str = "OV-XD-02_preference_agreement_record_v1",
) -> OVXD02PreferenceAgreementRecord:
    """Create a deterministic cross-dataset preference agreement record."""

    fam01 = _preferred_family(prefer_curved=ov01g_prefer_curved, robustness_failed=ov01g_robustness_failed)
    fam03 = _preferred_family(prefer_curved=ov03x_prefer_curved, robustness_failed=ov03x_robustness_failed)

    agreement = bool((fam01 == fam03) and bool(ov02x_all_scenarios_match_baseline))

    return OVXD02PreferenceAgreementRecord(
        config_tag=str(config_tag),
        ov01g_report_fingerprint=str(ov01g_report_fingerprint),
        ov02x_report_fingerprint=str(ov02x_report_fingerprint),
        ov03x_report_fingerprint=str(ov03x_report_fingerprint),
        ov01g_preferred_family=fam01,
        ov03x_preferred_family=fam03,
        ov02x_all_scenarios_match_baseline=bool(ov02x_all_scenarios_match_baseline),
        agreement=agreement,
    )
