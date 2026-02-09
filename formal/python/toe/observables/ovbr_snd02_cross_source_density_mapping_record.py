"""OV-BR-SND-02: cross-source density mapping record (computed lock).

Purpose
- Provide an explicit bookkeeping statement about whether and how density values
  from a *secondary* source could be mapped onto the sound-propagation condition
  used by OV-SND-01N/OV-SND-02.

This record is intentionally conservative.
- It does not import new external PDFs.
- It does not assert that conditions match across sources.
- It records the intended mapping structure and the current blockers.

Scope / limits
- Bookkeeping only; no physics claim.
- No continuity claim; no averaging.
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
from formal.python.toe.observables.ovsnd02b_sound_speed_from_propagation_seriesb_record import (
    ovsnd02b_sound_speed_from_propagation_record,
)
from formal.python.toe.observables.ovsnd03n_density_coverage_report_record import (
    ovsnd03n_density_coverage_report_record,
)
from formal.python.toe.observables.ovsnd03n2_secondary_density_conditions_digitized import (
    ovsnd03n2_secondary_density_conditions_digitized_record,
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


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _safe_load_mapping_tuples(*, path: Path) -> tuple[list[dict[str, Any]] | None, dict[str, Any]]:
    """Load explicit mapping tuples if present.

    Returns (mapping_tuples_or_none, info_dict).
    """

    if not path.exists():
        return None, {"exists": False, "path": str(path.as_posix()).replace("\\", "/")}

    text = path.read_text(encoding="utf-8")
    payload = json.loads(text)
    tuples = payload.get("mapping_tuples")
    if tuples is None:
        return None, {"exists": True, "path": str(path.as_posix()).replace("\\", "/"), "error": "missing mapping_tuples"}
    if not isinstance(tuples, list):
        return None, {"exists": True, "path": str(path.as_posix()).replace("\\", "/"), "error": "mapping_tuples not a list"}

    out: list[dict[str, Any]] = []
    for t in tuples:
        if isinstance(t, dict):
            out.append(dict(t))

    return out, {
        "exists": True,
        "path": str(path.as_posix()).replace("\\", "/"),
        "sha256": _sha256_file(path),
        "row_count": int(len(out)),
        "schema": payload.get("schema"),
    }


@dataclass(frozen=True)
class OVBR_SND02CrossSourceDensityMappingRecord:
    schema: str
    date: str

    sound_anchor: dict[str, Any]
    density_sources: dict[str, Any]

    mapping: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "sound_anchor": dict(self.sound_anchor),
            "density_sources": dict(self.density_sources),
            "mapping": dict(self.mapping),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovbr_snd02_cross_source_density_mapping_record(*, date: str = "2026-01-24") -> OVBR_SND02CrossSourceDensityMappingRecord:
    repo_root = _find_repo_root(Path(__file__))

    snd02 = ovsnd02_sound_speed_from_propagation_record(date=str(date))
    snd02b = ovsnd02b_sound_speed_from_propagation_record(date=str(date))
    cov = ovsnd03n_density_coverage_report_record(date=str(date))
    den2 = ovsnd03n2_secondary_density_conditions_digitized_record(date=str(date))

    sound_anchor = {
        "primary_speed": {
            "observable_id": "OV-SND-02",
            "record_schema": snd02.schema,
            "record_fingerprint": snd02.fingerprint(),
            "propagation_condition_key": "snd02_single",
            "condition_label": "single_condition_from_OV-SND-01N_Fig2_squares_seriesA",
        },
        "secondary_speed": {
            "observable_id": "OV-SND-02B",
            "record_schema": snd02b.schema,
            "record_fingerprint": snd02b.fingerprint(),
            "propagation_condition_key": "snd02b_seriesB",
            "blocked": bool(snd02b.status.get("blocked")),
            "blockers": list(snd02b.status.get("blockers") or []),
            "condition_label": "second_condition_from_OV-SND-01N2_seriesB",
        },
        "available_propagation_condition_keys": ["snd02_single", "snd02b_seriesB"],
    }

    density_sources = {
        "same_source": {
            "status": "present",
            "coverage_report": {
                "observable_id": cov.observable_id,
                "record_schema": cov.schema,
                "record_fingerprint": cov.fingerprint(),
                "n_density_conditions_supported": int(cov.decision["n_density_conditions_supported"]),
            },
            "notes": "Pinned sound note provides only one explicit density under current digitization method.",
        },
        "secondary_source": {
            "status": "present_but_blocked" if bool(den2.status.get("blocked")) else "present_unblocked",
            "candidate": "Experimental source with multiple explicit density conditions (preferred: same experiment as sound propagation)",
            "expected_repo_location": {
                "folder": "formal/external_evidence/bec_sound_density_secondary_TBD/",
                "pdf": "formal/external_evidence/bec_sound_density_secondary_TBD/source.pdf",
                "metadata": "formal/external_evidence/bec_sound_density_secondary_TBD/source.metadata.json",
                "density_table_csv": "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/density_conditions.csv",
                "density_table_metadata": "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/density_conditions.metadata.json",
                "mapping_tuples": "formal/external_evidence/bec_sound_density_secondary_TBD/ovbr_snd02_density_mapping/mapping_tuples.json",
            },
            "required_artifacts": [
                "density_conditions.csv (multi-row)",
                "density_conditions.metadata.json (hashes + provenance)",
                "mapping_tuples.json (explicit cross-source mapping tuples)",
            ],
            "ingestion_gate": {
                "observable_id": "OV-SND-03N2",
                "record_schema": str(den2.schema),
                "record_fingerprint": str(den2.fingerprint()),
                "blocked": bool(den2.status.get("blocked")),
                "blockers": list(den2.status.get("blockers") or []),
                "lock_path": "formal/markdown/locks/observables/OV-SND-03N2_secondary_density_conditions_digitized.md",
            },
        },
    }

    # Derive blockers from pinned artifacts and explicit mapping file.
    blockers: list[str] = []
    sec_pdf = repo_root / "formal" / "external_evidence" / "bec_sound_density_secondary_TBD" / "source.pdf"
    sec_meta = repo_root / "formal" / "external_evidence" / "bec_sound_density_secondary_TBD" / "source.metadata.json"
    if not sec_pdf.exists() or not sec_meta.exists():
        blockers.append("secondary_density_source_not_pinned")

    if bool(den2.status.get("blocked")) or den2.dataset is None or int(den2.dataset.get("row_count", 0)) < 2:
        blockers.append("density_conditions_table_not_digitized")

    mapping_path = repo_root / "formal" / "external_evidence" / "bec_sound_density_secondary_TBD" / "ovbr_snd02_density_mapping" / "mapping_tuples.json"
    mapping_tuples_loaded, mapping_file_info = _safe_load_mapping_tuples(path=mapping_path)
    mapping_tuples: list[dict[str, Any]] = []
    if mapping_tuples_loaded is not None:
        mapping_tuples = list(mapping_tuples_loaded)

    if not mapping_tuples:
        blockers.append("no_explicit_mapping_keys_recorded")

    mapping_is_complete = bool(len(blockers) == 0)
    status = "unblocked" if mapping_is_complete else "blocked"

    mapping = {
        "status": status,
        "mapping_is_complete": bool(mapping_is_complete),
        "mapping_tuples": mapping_tuples,
        "required_mapping_keys": [
            "propagation_condition_key",
            "density_condition_key",
            "source_locators",
        ],
        "recognized_density_condition_keys": (
            ["central"]
            + [str(r.get("density_condition_key")) for r in (den2.dataset.get("rows_preview") or [])]
            if den2.dataset is not None
            else ["central"]
        ),
        "mapping_file": dict(mapping_file_info),
        "allowed_computations": [
            "compute_OV-SND-04_only_when_mapping_unblocked_and_pairs>=2",
        ],
        "forbidden_computations": [
            "many_densities_to_one_speed_key (variant1_nonphysical_unless_explicitly_labeled)",
            "assume_condition_identity_across_sources",
            "impute_missing_density",
            "average_across_regimes",
            "make_continuity_or_universality_claims",
        ],
        "current_blockers": list(blockers),
        "non_mapping_statement": (
            "No cross-source density mapping is asserted at present. This record exists to prevent implicit condition identity. "
            "OV-SND-04 must remain blocked unless this mapping is explicitly unblocked and yields >=2 valid pairs."
        ),
    }

    scope_limits = [
        "bookkeeping_only",
        "no_physics_claim",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVBR_SND02CrossSourceDensityMappingRecord(
        schema="OV-BR-SND-02_cross_source_density_mapping/v1",
        date=str(date),
        sound_anchor=sound_anchor,
        density_sources=density_sources,
        mapping=mapping,
        scope_limits=scope_limits,
    )


def render_ovbr_snd02_lock_markdown(record: OVBR_SND02CrossSourceDensityMappingRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-SND-02 — Cross-source density mapping record (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping only; no physics claim\n"
        "- Declares intended mapping structure and current blockers; no continuity/averaging\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr_snd02_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-BR-SND-02_cross_source_density_mapping.md"

    rec = ovbr_snd02_cross_source_density_mapping_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr_snd02_lock_markdown(rec), encoding="utf-8")
    return out
