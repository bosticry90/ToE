"""OV-SND-04: multi-condition density constancy check (computed lock).

Purpose
- Compute density-scaled quantities (c/sqrt(n0) and c^2/n0) across multiple
  (c_i, n0_i) condition pairs and report a pinned summary of spread without
  fitting or claiming universality.

Scope / limits
- Bookkeeping / derived observable only; no ToE validation claim.
- No inference of density dependence beyond reporting spread statistics.
- No continuity claim; no regime averaging.

Current status
- This record is expected to be BLOCKED until >=2 condition pairs exist.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.toe.observables.ovsnd02_sound_speed_from_propagation_record import (
    ovsnd02_sound_speed_from_propagation_record,
)
from formal.python.toe.observables.ovsnd02b_sound_speed_from_propagation_seriesb_record import (
    ovsnd02b_sound_speed_from_propagation_record,
)
from formal.python.toe.observables.ovsnd03n_central_density_digitized import (
    ovsnd03n_central_density_digitized_record,
)
from formal.python.toe.observables.ovsnd03n2_secondary_density_conditions_digitized import (
    ovsnd03n2_secondary_density_conditions_digitized_record,
)
from formal.python.toe.observables.ovbr_snd02_cross_source_density_mapping_record import (
    ovbr_snd02_cross_source_density_mapping_record,
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


def _read_secondary_density_csv(csv_path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        expected = ["density_condition_key", "n0_cm3", "source_locator", "notes"]
        if r.fieldnames != expected:
            raise ValueError(f"Unexpected columns: {r.fieldnames} (expected {expected})")
        for row in r:
            rows.append(
                {
                    "density_condition_key": str(row["density_condition_key"]),
                    "n0_cm3": float(row["n0_cm3"]),
                    "source_locator": str(row["source_locator"]),
                    "notes": str(row["notes"]),
                }
            )
    return rows


def _cv(x: np.ndarray) -> float:
    mu = float(np.mean(x))
    if mu == 0.0:
        return float("nan")
    return float(np.std(x, ddof=1) / mu) if x.size >= 2 else float("nan")


@dataclass(frozen=True)
class OVSND04SoundSpeedDensityConstancyRecord:
    schema: str
    date: str

    observable_id: str

    status: dict[str, Any]
    inputs: dict[str, Any]
    condition_rows: list[dict[str, Any]]
    summary: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "condition_rows": list(self.condition_rows),
            "summary": dict(self.summary),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd04_sound_speed_density_constancy_record(*, date: str = "2026-01-24") -> OVSND04SoundSpeedDensityConstancyRecord:
    repo_root = _find_repo_root(Path(__file__))

    snd02 = ovsnd02_sound_speed_from_propagation_record(date=str(date))
    snd02b = ovsnd02b_sound_speed_from_propagation_record(date=str(date))
    den = ovsnd03n_central_density_digitized_record(date=str(date))
    den2 = ovsnd03n2_secondary_density_conditions_digitized_record(date=str(date))

    mapping_rec = ovbr_snd02_cross_source_density_mapping_record(date=str(date))

    # Speed conditions.
    speed_by_key: dict[str, dict[str, float]] = {}
    speed_by_key["snd02_single"] = {
        "c_m_per_s": float(snd02.results["primary"]["c_m_per_s"]),
        "se_c_m_per_s": float(snd02.results["primary"]["se_m_per_s"]),
    }

    if not bool(snd02b.status.get("blocked")) and snd02b.results is not None:
        speed_by_key["snd02b_seriesB"] = {
            "c_m_per_s": float(snd02b.results["primary"]["c_m_per_s"]),
            "se_c_m_per_s": float(snd02b.results["primary"]["se_m_per_s"]),
        }

    # Density conditions.
    density_by_key: dict[str, dict[str, float]] = {
        "central": {"n0_cm3": float(1.0e14)}
    }

    if not bool(den2.status.get("blocked")) and den2.dataset is not None:
        csv_rel = str(den2.dataset.get("csv_relpath"))
        if csv_rel:
            rows2 = _read_secondary_density_csv(repo_root / csv_rel)
            for r in rows2:
                k = str(r["density_condition_key"])
                if k in density_by_key:
                    # Defensive: do not silently override keys.
                    continue
                density_by_key[k] = {"n0_cm3": float(r["n0_cm3"])}

    mapping = mapping_rec.mapping
    mapping_tuples = list(mapping.get("mapping_tuples") or [])

    rows: list[dict[str, Any]] = []
    blockers: list[str] = []

    if str(mapping.get("status")) != "unblocked" or not bool(mapping.get("mapping_is_complete")):
        blockers.append("mapping_record_blocked")

    # Enforce one-to-one mapping: each speed key maps to at most one density key.
    speed_keys = [str(t.get("propagation_condition_key", "")) for t in mapping_tuples]
    density_keys = [str(t.get("density_condition_key", "")) for t in mapping_tuples]
    if len(speed_keys) != len(set(speed_keys)):
        blockers.append("many_densities_to_one_speed_key_forbidden")

    if len(density_keys) != len(set(density_keys)):
        blockers.append("many_speeds_to_one_density_key_forbidden")

    if not blockers:
        for t in mapping_tuples:
            speed_key = str(t["propagation_condition_key"])
            den_key = str(t["density_condition_key"])

            if speed_key not in speed_by_key:
                blockers.append(f"missing_speed_condition:{speed_key}")
                continue
            if den_key not in density_by_key:
                blockers.append(f"missing_density_condition:{den_key}")
                continue

            c_m_per_s = float(speed_by_key[speed_key]["c_m_per_s"])
            se_c_m_per_s = float(speed_by_key[speed_key]["se_c_m_per_s"])

            n0_cm3 = float(density_by_key[den_key]["n0_cm3"])
            n0_m3 = float(n0_cm3) * 1.0e6

            k_si = c_m_per_s / float(np.sqrt(n0_m3))
            k2_si = (c_m_per_s**2) / n0_m3

            rows.append(
                {
                    "condition_id": f"{speed_key}__{den_key}",
                    "propagation_condition_key": speed_key,
                    "density_condition_key": den_key,
                    "pair_type": t.get("pair_type"),
                    "source_locators": dict(t.get("source_locators") or {}),
                    "rationale": t.get("rationale"),
                    "c_m_per_s": float(c_m_per_s),
                    "se_c_m_per_s": float(se_c_m_per_s),
                    "n0_cm3": float(n0_cm3),
                    "n0_m3": float(n0_m3),
                    "K_si_m32_per_s": float(k_si),
                    "K2_si_m5_per_s2": float(k2_si),
                }
            )

    # Preserve a single-condition scaffold row even while blocked, so the record
    # remains a concrete (but explicitly non-claiming) computed object.
    if not rows:
        c0 = float(speed_by_key["snd02_single"]["c_m_per_s"])
        se0 = float(speed_by_key["snd02_single"]["se_c_m_per_s"])
        n0_cm3 = float(density_by_key["central"]["n0_cm3"])
        n0_m3 = float(n0_cm3) * 1.0e6

        rows.append(
            {
                "condition_id": "scaffold__snd02_single__central",
                "propagation_condition_key": "snd02_single",
                "density_condition_key": "central",
                "c_m_per_s": float(c0),
                "se_c_m_per_s": float(se0),
                "n0_cm3": float(n0_cm3),
                "n0_m3": float(n0_m3),
                "K_si_m32_per_s": float(c0 / float(np.sqrt(n0_m3))),
                "K2_si_m5_per_s2": float((c0**2) / n0_m3),
                "row_role": "scaffold_only",
            }
        )

    n_pairs = int(len(rows))
    if n_pairs < 2:
        blockers.append("insufficient_condition_pairs")

    blocked = bool(blockers)
    status = {
        "blocked": bool(blocked),
        "reason": None if not blocked else "blocked_by_mapping_or_coverage",
        "required_min_pairs": 2,
        "n_pairs": int(n_pairs),
        "blockers": list(blockers),
    }

    inputs = {
        "OV-SND-02": {
            "record_schema": str(snd02.schema),
            "record_fingerprint": str(snd02.fingerprint()),
            "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
        },
        "OV-SND-02B": {
            "record_schema": str(snd02b.schema),
            "record_fingerprint": str(snd02b.fingerprint()),
            "lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
            "blocked": bool(snd02b.status.get("blocked")),
            "blockers": list(snd02b.status.get("blockers") or []),
        },
        "OV-SND-03N": {
            "record_schema": str(den.schema),
            "record_fingerprint": str(den.fingerprint()),
            "lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
        },
        "OV-SND-03N2": {
            "record_schema": str(den2.schema),
            "record_fingerprint": str(den2.fingerprint()),
            "lock_path": "formal/markdown/locks/observables/OV-SND-03N2_secondary_density_conditions_digitized.md",
            "blocked": bool(den2.status.get("blocked")),
            "blockers": list(den2.status.get("blockers") or []),
            "row_count": int(den2.dataset.get("row_count", 0)) if den2.dataset else None,
        },
        "OV-BR-SND-02": {
            "record_schema": str(mapping_rec.schema),
            "record_fingerprint": str(mapping_rec.fingerprint()),
            "lock_path": "formal/markdown/locks/observables/OV-BR-SND-02_cross_source_density_mapping.md",
        },
    }

    summary: dict[str, Any] = {
        "metrics": None,
        "note": (
            "Blocked until OV-BR-SND-02 is unblocked and yields >=2 one-to-one mapped (c_i, n0_i) pairs. "
            "This record does not perform cross-source identity assumptions."
        ),
    }

    if not blocked:
        k = np.asarray([float(r["K_si_m32_per_s"]) for r in rows], dtype=float)
        k2 = np.asarray([float(r["K2_si_m5_per_s2"]) for r in rows], dtype=float)

        k_mu = float(np.mean(k))
        k2_mu = float(np.mean(k2))

        # Pinned spread statistics (no fitting)
        summary = {
            "metrics": {
                "K": {
                    "mean": float(k_mu),
                    "cv": float(_cv(k)),
                    "max_fractional_deviation_from_mean": float(np.max(np.abs(k - k_mu) / abs(k_mu))) if k_mu != 0 else float("nan"),
                },
                "K2": {
                    "mean": float(k2_mu),
                    "cv": float(_cv(k2)),
                    "max_fractional_deviation_from_mean": float(np.max(np.abs(k2 - k2_mu) / abs(k2_mu))) if k2_mu != 0 else float("nan"),
                },
                "n_pairs": int(n_pairs),
            },
            "assumptions": [
                "no_density_uncertainty_modeled (density treated as fixed per digitization)",
                "speed_uncertainty_propagation_not_modeled_in_spread_metrics",
            ],
        }

    scope_limits = [
        "derived_bookkeeping_only",
        "no_universality_claim",
        "no_density_dependence_inference_beyond_spread_metrics",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVSND04SoundSpeedDensityConstancyRecord(
        schema="OV-SND-04_sound_speed_density_constancy/v2",
        date=str(date),
        observable_id="OV-SND-04",
        status=status,
        inputs=inputs,
        condition_rows=rows,
        summary=summary,
        scope_limits=scope_limits,
    )


def render_ovsnd04_lock_markdown(record: OVSND04SoundSpeedDensityConstancyRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-04 — Sound speed density constancy check (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / derived observable only; no physics validation claim\n"
        "- Reports spread metrics only; no fitting; no universality/continuity claims\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd04_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-04_sound_speed_density_constancy.md"

    rec = ovsnd04_sound_speed_density_constancy_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd04_lock_markdown(rec), encoding="utf-8")
    return out
