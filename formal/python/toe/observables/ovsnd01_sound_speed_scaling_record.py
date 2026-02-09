"""OV-SND-01: sound-speed scaling anchor (computed lock).

Purpose
- Introduce a second, external, non-controversial anchor observable: BEC sound
  propagation / sound speed scaling.

This is a symbolic-first anchor:
- Locks dependency structure only (e.g., $c \propto \sqrt{n}$).
- No fitting, no parameter inference, no ToE validation claim.

Source
- ArXiv:9711224v1 (Kavoulakis & Pethick, 1997) discusses sound propagation in
  elongated condensates and references the Andrews et al. experiment.

Scope / limits
- Bookkeeping / anchor definition only; no physics validation claim.
- No continuity/averaging across regimes.
- Benchmark non-participation: this anchor is not used for selection decisions
  unless explicitly activated by future records.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


@dataclass(frozen=True)
class OVSND01SoundSpeedScalingRecord:
    schema: str
    date: str

    observable_id: str

    source: dict[str, Any]
    statement: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "source": dict(self.source),
            "statement": dict(self.statement),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd01_sound_speed_scaling_record(*, date: str = "2026-01-24") -> OVSND01SoundSpeedScalingRecord:
    repo_root = _find_repo_root(Path(__file__))

    pdf_rel = "formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf"
    pdf_sha = _sha256_file(repo_root / pdf_rel)

    source = {
        "citation": "Kavoulakis & Pethick (1997), arXiv:9711224v1 — Sound Propagation in Elongated Bose-Einstein Condensed Clouds (references Andrews et al. experiment)",
        "arxiv_pdf_relpath": pdf_rel,
        "arxiv_pdf_sha256": pdf_sha,
    }

    statement = {
        "regime": "phonon / hydrodynamic (low-k)",
        "scaling": {
            "c_proportional_to": "sqrt(n)",
            "canonical_relation": "c^2 = dP/dρ ≈ n U0 / m (homogeneous, T≈0)",
            "notes": "In an elongated trapped condensate, cross-section averaging can introduce geometric factors (e.g., average density ~ 1/2 of axial density for harmonic transverse confinement).",
        },
        "observable_definition": "Sound speed c inferred from propagation of a density disturbance along the long axis; anchor focuses on the dependency structure, not parameter extraction.",
    }

    scope_limits = [
        "symbolic_only",
        "no_fitting",
        "no_parameter_inference",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVSND01SoundSpeedScalingRecord(
        schema="OV-SND-01_sound_speed_scaling_anchor/v1",
        date=str(date),
        observable_id="OV-SND-01",
        source=source,
        statement=statement,
        scope_limits=scope_limits,
    )


def render_ovsnd01_lock_markdown(record: OVSND01SoundSpeedScalingRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-01 — Sound-speed scaling anchor (computed)\n\n"
        "Scope / limits\n"
        "- Symbolic-first anchor; dependency structure only; no physics validation claim\n"
        "- No fitting; no parameter inference; no continuity/averaging across regimes\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd01_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-01_sound_speed_scaling_anchor.md"

    rec = ovsnd01_sound_speed_scaling_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd01_lock_markdown(rec), encoding="utf-8")
    return out
