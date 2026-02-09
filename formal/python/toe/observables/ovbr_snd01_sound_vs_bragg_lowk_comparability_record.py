"""OV-BR-SND-01: comparability / non-comparability record (sound propagation vs low-k Bragg).

Purpose
- Provide an explicit, scope-fenced bookkeeping statement about whether and how
  the sound-propagation speed anchor (OV-SND-02) is comparable to the low-k Bragg
  anchor used in the selection pipeline (OV-04x / DS-02).

This record is intentionally conservative.
- It does not compute a cross-anchor match.
- It does not assert continuity.
- It declares the *conditions* under which a comparison would be meaningful, and
  the current reasons it is *not* performed.

Scope / limits
- Bookkeeping only; no physics claim.
- No averaging across regimes; no continuity claim.
- Non-decisive by design.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovsnd02_sound_speed_from_propagation_record import (
    ovsnd02_sound_speed_from_propagation_record,
)


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


@dataclass(frozen=True)
class OVBR_SND01SoundVsBraggLowKComparabilityRecord:
    schema: str
    date: str

    sound_anchor: dict[str, Any]
    bragg_anchor: dict[str, Any]

    comparability: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "sound_anchor": dict(self.sound_anchor),
            "bragg_anchor": dict(self.bragg_anchor),
            "comparability": dict(self.comparability),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovbr_snd01_sound_vs_bragg_lowk_comparability_record(*, date: str = "2026-01-24") -> OVBR_SND01SoundVsBraggLowKComparabilityRecord:
    snd02 = ovsnd02_sound_speed_from_propagation_record(date=str(date))

    sound_anchor = {
        "observable_id": "OV-SND-02",
        "record_schema": snd02.schema,
        "record_fingerprint": snd02.fingerprint(),
        "quantity": "sound_speed_c",
        "units": "m/s",
        "extraction": "slope_from_distance_time_points",
    }

    # Cross-lane comparison consumes a Bragg-derived velocity candidate exported by OV-BR-05
    # (itself derived from locked OV-BR-04A/04B). This record stays bookkeeping-only.
    bragg_anchor = {
        "observable_id": "OV-BR-05",
        "dataset": "DS-02 (low-k)",
        "quantity": "velocity_candidate_c",
        "units": "mm/s (convertible to m/s via pinned unit identity)",
        "notes": "OV-BR-05 exports c_mm_per_s derived from locked OV-BR-04A/04B; no additional equivalence is asserted here.",
    }

    comparability = {
        "status": "not_compared_quantitatively",
        "comparable_in_principle": True,
        "principle_conditions": [
            "phonon_regime_low_k",
            "same_definition_of_c (group_velocity at k→0)",
            "explicit_density_and_geometry_calibration (no hidden averaging)",
            "explicit_cross_lane_pairing_present (no implicit condition identity)",
        ],
        # Gate definition for downstream tooling: this lock is considered gate_ok when
        # comparable_in_principle is True and current_blockers is empty.
        "current_blockers": [],
        "conditional_notes": [
            "No physics claim: this record only declares governance conditions for comparison.",
            "Quantitative comparison remains fail-closed unless an explicit Bragg↔Sound pairing tuple is declared (OV-BR-SND-03 mapping tuples).",
            "Downstream density-dependent checks remain governed by OV-BR-SND-02; this record does not infer density n.",
        ],
        "non_comparability_statement": (
            "A quantitative sound-vs-Bragg comparison is only performed under explicit pairing and audit gates. "
            "This record declares the conditions for comparability and forbids implicit averaging or density inference."
        ),
        "forbidden_behaviors": [
            "no_cross_regime_averaging",
            "no_continuity_claim",
            "no_density_inference",
            "no_parameter_matching_without_pinned_calibration",
        ],
    }

    scope_limits = [
        "bookkeeping_only",
        "no_physics_claim",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVBR_SND01SoundVsBraggLowKComparabilityRecord(
        schema="OV-BR-SND-01_sound_vs_bragg_lowk_comparability/v1",
        date=str(date),
        sound_anchor=sound_anchor,
        bragg_anchor=bragg_anchor,
        comparability=comparability,
        scope_limits=scope_limits,
    )


def render_ovbr_snd01_lock_markdown(record: OVBR_SND01SoundVsBraggLowKComparabilityRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-SND-01 — Sound vs low-k Bragg comparability (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping only; no physics claim\n"
        "- Declares comparability conditions and current blockers; no continuity/averaging\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr_snd01_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-BR-SND-01_sound_vs_bragg_lowk_comparability.md"
        )

    rec = ovbr_snd01_sound_vs_bragg_lowk_comparability_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr_snd01_lock_markdown(rec), encoding="utf-8")
    return out
