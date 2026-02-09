"""OV-XD-03: cross-dataset k-band overlap record (computed).

Purpose
- Deterministically compute the k-coverage bands for the datasets used by the
  cross-dataset robustness bookkeeping (OV-XD family), and compute their
  overlap band.

Scope / limits
- Bookkeeping only; no physics claim.
- No network, no randomness.

Notes
- This module reads frozen CSVs from the repository to compute k_min/k_max.
  This is intentional: the record is about the operational dataset extents.

Update (v2)
- Adds an optional DS-02 low-k band slot (OV-04x). If DS-02 is not yet
    populated, OV-04x is explicitly excluded with a reason.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


@dataclass(frozen=True)
class KBand:
    k_min: float
    k_max: float


@dataclass(frozen=True)
class OverlapBand:
    k_min: float
    k_max: float
    non_empty: bool


@dataclass(frozen=True)
class OVXD03OverlapBandRecord:
    schema: str
    bands: dict[str, KBand]
    overlap: OverlapBand
    included_band_ids: tuple[str, ...]
    excluded: dict[str, str]
    provenance: dict[str, dict[str, str]]
    notes: str

    def to_jsonable(self) -> dict:
        return {
            "schema": self.schema,
            "bands": {k: {"k_min": float(v.k_min), "k_max": float(v.k_max)} for (k, v) in self.bands.items()},
            "overlap": {
                "k_min": float(self.overlap.k_min),
                "k_max": float(self.overlap.k_max),
                "non_empty": bool(self.overlap.non_empty),
            },
            "included_band_ids": list(self.included_band_ids),
            "excluded": dict(self.excluded),
            "provenance": {k: dict(v) for (k, v) in self.provenance.items()},
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable())


def _band_from_csv(csv_path: Path) -> KBand:
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        ks = [float(row["k_um_inv"]) for row in reader]

    if not ks:
        raise ValueError(f"No rows found in {csv_path}")

    # Rounded to keep the record stable and readable; the CSV hashes are also
    # recorded to preserve full provenance.
    return KBand(k_min=round(min(ks), 12), k_max=round(max(ks), 12))


def ovxd03_overlap_band_record() -> OVXD03OverlapBandRecord:
    """Compute k-bands and overlap band for OV-01g / OV-02x / OV-03x datasets."""

    repo_root = _find_repo_root(Path(__file__))

    # Dataset keys are stable inventory IDs.
    steinhauer_csv = (
        repo_root / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001" / "omega_k_data.csv"
    )
    ernst_b1_csv = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_bragg_b1_second_dataset_TBD"
        / "omega_k_data.csv"
    )

    ds02_lowk_csv = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_bragg_ds02_lowk_dataset_TBD"
        / "omega_k_data.csv"
    )

    bands: dict[str, KBand] = {
        "OV-01g": _band_from_csv(steinhauer_csv),
        "OV-02x": _band_from_csv(steinhauer_csv),
        "OV-03x": _band_from_csv(ernst_b1_csv),
    }

    excluded: dict[str, str] = {}

    # Optional DS-02 low-k slot (OV-04x). Keep the repo green while DS-02 is
    # still a scaffold (header-only CSV).
    if ds02_lowk_csv.exists():
        try:
            bands["OV-04x"] = _band_from_csv(ds02_lowk_csv)
        except ValueError as e:
            excluded["OV-04x"] = f"not included: {e}"
    else:
        excluded["OV-04x"] = "not included: DS-02 CSV not present"

    overlap_k_min = max(b.k_min for b in bands.values())
    overlap_k_max = min(b.k_max for b in bands.values())
    non_empty = bool(overlap_k_max >= overlap_k_min)

    provenance = {
        "OV-01g": {"csv_path": str(steinhauer_csv.as_posix()), "csv_sha256": _sha256_file(steinhauer_csv)},
        "OV-02x": {"csv_path": str(steinhauer_csv.as_posix()), "csv_sha256": _sha256_file(steinhauer_csv)},
        "OV-03x": {"csv_path": str(ernst_b1_csv.as_posix()), "csv_sha256": _sha256_file(ernst_b1_csv)},
    }

    if "OV-04x" in bands:
        provenance["OV-04x"] = {"csv_path": str(ds02_lowk_csv.as_posix()), "csv_sha256": _sha256_file(ds02_lowk_csv)}

    return OVXD03OverlapBandRecord(
        schema="OV-XD-03/v2",
        bands=bands,
        overlap=OverlapBand(k_min=float(overlap_k_min), k_max=float(overlap_k_max), non_empty=non_empty),
        included_band_ids=tuple(sorted(bands.keys())),
        excluded=dict(excluded),
        provenance=provenance,
        notes=(
            "Operational only; bookkeeping record; no physics claim. "
            "Overlap is computed as the intersection across included bands; excluded slots are listed explicitly."
        ),
    )


def render_ovxd03_lock_markdown(record: OVXD03OverlapBandRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-XD-03 — Cross-dataset overlap band record (computed)\n\n"
        "Purpose\n"
        "- Deterministically compute per-dataset k-coverage bands for the datasets used by OV-XD bookkeeping and compute their overlap band.\n\n"
        "Scope / limits\n"
        "- Bookkeeping only; no physics claim.\n"
        "- Must not be used for β inference.\n"
        "- Computed overlap is the intersection of k-coverage bands (not a union).\n\n"
        "Inclusion policy (v2)\n"
        "- OV-04x (DS-02 low-k slot) is included only when DS-02 is populated; otherwise it is explicitly excluded with a reason.\n\n"
        "Computation\n"
        "- Module: `formal/python/toe/observables/ovxd03_overlap_band_record.py`\n"
        "- Inputs: frozen CSVs in `formal/external_evidence/...`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovxd03_lock(*, lock_path: Path | None = None) -> Path:
    """Write the OV-XD-03 lock markdown deterministically."""

    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-XD-03_cross_dataset_overlap_band_record.md"
        )

    rec = ovxd03_overlap_band_record()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovxd03_lock_markdown(rec), encoding="utf-8")
    return out
