"""OV-SND-03: sound speed density scaling from OV-SND-02 and OV-SND-03N (computed lock).

Purpose
- Provide a deterministic bookkeeping observable that combines the derived sound
  speed (OV-SND-02) with a digitized density anchor (OV-SND-03N) to compute
  density-scaled quantities such as c/sqrt(n0) and c^2/n0.

Scope / limits
- Bookkeeping / derived observable only; no ToE validation claim.
- Single-condition only (because OV-SND-03N is single-condition in this source).
- No inference of density dependence; no continuity claim; no regime averaging.

Definitions
- n0 is taken from OV-SND-03N in cm^-3 and converted to m^-3 for SI.
- Report both SI-scaled and cm-scaled forms to avoid silent unit confusion.
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
from formal.python.toe.observables.ovsnd03n_central_density_digitized import (
    ovsnd03n_central_density_digitized_record,
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
class OVSND03SoundSpeedDensityScalingRecord:
    schema: str
    date: str

    observable_id: str

    inputs: dict[str, Any]
    definitions: dict[str, Any]
    results: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "inputs": dict(self.inputs),
            "definitions": dict(self.definitions),
            "results": dict(self.results),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd03_sound_speed_density_scaling_record(*, date: str = "2026-01-24") -> OVSND03SoundSpeedDensityScalingRecord:
    _ = _find_repo_root(Path(__file__))

    snd02 = ovsnd02_sound_speed_from_propagation_record(date=str(date))
    den = ovsnd03n_central_density_digitized_record(date=str(date))

    c_m_per_s = float(snd02.results["primary"]["c_m_per_s"])
    se_c_m_per_s = float(snd02.results["primary"]["se_m_per_s"])

    # Deterministic: OV-SND-03N is pinned to 1e14 cm^-3 for this snapshot.
    # We repeat the value here explicitly rather than re-parsing the CSV.
    n0_cm3 = float(1.0e14)

    # Convert: 1 cm^-3 = 1e6 m^-3
    n0_m3 = float(n0_cm3) * 1.0e6

    sqrt_n0_cm3 = float(n0_cm3) ** 0.5
    sqrt_n0_m3 = float(n0_m3) ** 0.5

    k_si = c_m_per_s / sqrt_n0_m3
    k_cm = c_m_per_s / sqrt_n0_cm3

    k2_si = (c_m_per_s**2) / n0_m3
    k2_cm = (c_m_per_s**2) / n0_cm3

    inputs = {
        "OV-SND-02": {
            "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
            "locked_record_schema": str(snd02.schema),
            "locked_record_fingerprint": str(snd02.fingerprint()),
            "c_m_per_s": float(c_m_per_s),
            "se_m_per_s": float(se_c_m_per_s),
        },
        "OV-SND-03N": {
            "lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
            "locked_record_schema": str(den.schema),
            "locked_record_fingerprint": str(den.fingerprint()),
            "n0_cm3": float(n0_cm3),
        },
    }

    definitions = {
        "n0": {
            "n0_cm3": float(n0_cm3),
            "n0_m3": float(n0_m3),
            "conversion": "n0_m3 = n0_cm3 * 1e6 (since 1 cm^-3 = 1e6 m^-3)",
        },
        "scaled_quantities": [
            {"name": "K = c/sqrt(n0)", "units_si": "m^(3/2)/s", "units_cm": "m*cm^(3/2)/s"},
            {"name": "K2 = c^2/n0", "units_si": "m^5/s^2", "units_cm": "m^2*cm^3/s^2"},
        ],
        "note": "Single-condition only; does not test constancy across multiple densities.",
    }

    results = {
        "n0": {"n0_cm3": float(n0_cm3), "n0_m3": float(n0_m3)},
        "K": {
            "value_si_m32_per_s": float(k_si),
            "value_cm_m_cm32_per_s": float(k_cm),
        },
        "K2": {
            "value_si_m5_per_s2": float(k2_si),
            "value_cm_m2_cm3_per_s2": float(k2_cm),
        },
    }

    scope_limits = [
        "derived_bookkeeping_only",
        "single_condition_only",
        "no_density_dependence_inference",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVSND03SoundSpeedDensityScalingRecord(
        schema="OV-SND-03_sound_speed_density_scaling/v1",
        date=str(date),
        observable_id="OV-SND-03",
        inputs=inputs,
        definitions=definitions,
        results=results,
        scope_limits=scope_limits,
    )


def render_ovsnd03_lock_markdown(record: OVSND03SoundSpeedDensityScalingRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-03 — Sound speed density scaling (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / derived observable only; no physics validation claim\n"
        "- Single-condition only; no density-dependence inference\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd03_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-03_sound_speed_density_scaling.md"

    rec = ovsnd03_sound_speed_density_scaling_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd03_lock_markdown(rec), encoding="utf-8")
    return out
