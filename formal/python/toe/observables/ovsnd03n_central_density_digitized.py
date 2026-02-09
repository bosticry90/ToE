"""OV-SND-03N: minimal digitized central density anchor from pinned sound PDF (computed lock).

Digitization target
- Source PDF: arXiv:9711224v1 (Kavoulakis & Pethick, 1997)
- Context: text near Fig. 1 / Fig. 2 discussion (page 4 in the pinned PDF)
- Quantity:
  - Central density n0 [cm^-3]

Purpose
- Provide a deterministic, frozen external density artifact to enable sound-lane
  density-dependent bookkeeping checks (e.g., c/sqrt(n0), c^2/n0) without
  inventing continuity or performing regime averaging.

Scope / limits
- Anchor numeric ingestion only; no physics validation claim.
- Single-condition anchor only (this source provides one explicit n0 value in
  extractable text under the current digitization method).
- No fitting, no imputation, no averaging across regimes.

Design
- Deterministic: extracts text using pdfplumber and matches a pinned regex.
- Writes a frozen CSV + JSON metadata wrapper under formal/external_evidence.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
import re
from pathlib import Path
from typing import Any


def _require_pdfplumber():
    try:
        import pdfplumber  # type: ignore
    except ModuleNotFoundError as e:  # pragma: no cover
        raise RuntimeError(
            "pdfplumber is required only for PDF extraction paths. "
            "Regen from frozen artifacts should not call this path; install pdfplumber into the active interpreter/venv "
            "only if you need to (re)extract from the pinned PDF."
        ) from e
    return pdfplumber


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _normalize_extracted_text(s: str) -> str:
    # Normalize common PDF-extracted punctuation variants.
    return (
        s.replace("\u2212", "-")  # minus
        .replace("\u2013", "-")  # en dash
        .replace("\u2014", "-")  # em dash
        .replace("\u00d7", "x")  # multiplication sign
    )


def _extract_central_density_from_pdf(*, pdf_path: Path) -> dict[str, Any]:
    """Return {n0_cm3, match_text, page_number}.

    Note: In this pinned PDF, the text extractor collapses 10^14 to 1014.
    We treat a match of '1014 cm-3' as the intended 10^14 cm^-3.
    """

    pdfplumber = _require_pdfplumber()
    with pdfplumber.open(str(pdf_path)) as pdf:
        full_text = "\n".join((page.extract_text() or "") for page in pdf.pages)
        full_text = _normalize_extracted_text(full_text)

    # Stable on the current pinned snapshot: "1014 cm-3" appears in the page-4 region.
    # We keep the regex narrow to avoid ambiguity.
    pat = re.compile(r"\b1014\s*cm\s*-\s*3\b", flags=re.IGNORECASE)

    matches = list(pat.finditer(full_text))
    if len(matches) != 1:
        raise RuntimeError(f"Expected exactly 1 central-density match, got N={len(matches)}")

    m = matches[0]
    match_text = str(m.group(0))

    # Attempt to locate page number deterministically by scanning per-page.
    page_number: int | None = None
    with pdfplumber.open(str(pdf_path)) as pdf:
        for i, page in enumerate(pdf.pages, start=1):
            t = _normalize_extracted_text(page.extract_text() or "")
            if pat.search(t) is not None:
                page_number = int(i)
                break

    if page_number is None:
        raise RuntimeError("Could not locate match on any individual page")

    return {
        "n0_cm3": float(1.0e14),
        "match_text": match_text,
        "page_number": int(page_number),
    }


def _render_csv_text(*, n0_cm3: float) -> str:
    # One-row dataset, newline-stable.
    header = ["condition_id", "n0_cm3"]
    lines = [",".join(header)]
    lines.append(f"central,{n0_cm3:.12g}")
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class OVSND03NCentralDensityDigitizedRecord:
    schema: str
    digitization_id: str
    date: str

    observable_id: str

    source: dict[str, Any]
    dataset: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "digitization_id": str(self.digitization_id),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "source": dict(self.source),
            "dataset": dict(self.dataset),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd03n_central_density_digitized_record(*, date: str = "2026-01-24") -> OVSND03NCentralDensityDigitizedRecord:
    repo_root = _find_repo_root(Path(__file__))

    pdf_rel = "formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf"
    csv_rel = "formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.csv"
    meta_rel = "formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.metadata.json"

    csv_path = repo_root / csv_rel
    meta_path = repo_root / meta_rel

    # Prefer frozen artifacts (governance-safe, avoids optional PDF toolchain at runtime).
    if csv_path.exists() and meta_path.exists():
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        csv_text = csv_path.read_text(encoding="utf-8")

        expected_sha = str(meta.get("dataset", {}).get("csv_sha256") or "")
        if expected_sha and _sha256_text(csv_text) != expected_sha:
            raise RuntimeError("Frozen OV-SND-03N CSV sha256 does not match metadata")

        reader = csv.DictReader(csv_text.splitlines())
        expected_cols = ["condition_id", "n0_cm3"]
        if reader.fieldnames != expected_cols:
            raise RuntimeError(f"Unexpected OV-SND-03N CSV columns: {reader.fieldnames}")
        rows = list(reader)
        if len(rows) != 1 or str(rows[0].get("condition_id")) != "central":
            raise RuntimeError("Frozen OV-SND-03N CSV must contain exactly one row with condition_id=central")

        dataset = dict(meta.get("dataset") or {})
        source = dict(meta.get("source") or {})
    else:
        # Fallback path (requires pdfplumber): re-extract and compute payload.
        pdf_sha = _sha256_file(repo_root / pdf_rel)
        extracted = _extract_central_density_from_pdf(pdf_path=repo_root / pdf_rel)
        n0_cm3 = float(extracted["n0_cm3"])
        csv_text = _render_csv_text(n0_cm3=n0_cm3)

        dataset = {
            "csv_relpath": csv_rel,
            "metadata_relpath": meta_rel,
            "row_count": 1,
            "columns": [
                {"name": "condition_id", "unit": "(label)", "dtype": "string"},
                {"name": "n0_cm3", "unit": "cm^-3", "dtype": "float"},
            ],
            "csv_sha256": _sha256_text(csv_text),
        }

        source = {
            "citation": "Kavoulakis & Pethick (1997), arXiv:9711224v1 — Sound Propagation in Elongated Bose-Einstein Condensed Clouds",
            "arxiv_pdf_relpath": pdf_rel,
            "arxiv_pdf_sha256": pdf_sha,
            "extraction_method": "pdfplumber_text_regex",
            "matched_text": str(extracted["match_text"]),
            "page_number": int(extracted["page_number"]),
            "notes": (
                "PDF text extraction collapses the typeset 10^14 to '1014' in this snapshot; "
                "the parser interprets '1014 cm-3' as 1e14 cm^-3."
            ),
        }

    scope_limits = [
        "anchor_numeric_only",
        "single_condition_only",
        "no_fitting",
        "no_imputation",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVSND03NCentralDensityDigitizedRecord(
        schema="OV-SND-03_central_density_digitized/v1",
        digitization_id="OV-SND-03N",
        date=str(date),
        observable_id="OV-SND-03N",
        source=source,
        dataset=dataset,
        scope_limits=scope_limits,
    )


def write_ovsnd03n_digitized_artifacts(*, date: str = "2026-01-24") -> dict[str, Path]:
    repo_root = _find_repo_root(Path(__file__))
    rec = ovsnd03n_central_density_digitized_record(date=str(date))

    pdf_path = repo_root / rec.source["arxiv_pdf_relpath"]
    if not pdf_path.exists():
        raise FileNotFoundError(f"Missing pinned PDF: {pdf_path}")

    extracted = _extract_central_density_from_pdf(pdf_path=pdf_path)
    csv_text = _render_csv_text(n0_cm3=float(extracted["n0_cm3"]))

    csv_path = repo_root / rec.dataset["csv_relpath"]
    meta_path = repo_root / rec.dataset["metadata_relpath"]

    csv_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.parent.mkdir(parents=True, exist_ok=True)

    csv_path.write_text(csv_text, encoding="utf-8", newline="\n")

    meta_payload = {
        "schema": "OV-SND-03_digitized_density_metadata/v1",
        "date": rec.date,
        "observable_id": rec.observable_id,
        "digitization_id": rec.digitization_id,
        "source": rec.source,
        "dataset": rec.dataset,
        "scope_limits": rec.scope_limits,
        "record_fingerprint": rec.fingerprint(),
    }

    meta_path.write_text(json.dumps(meta_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return {"csv": csv_path, "metadata": meta_path}


def render_ovsnd03n_digitized_lock_markdown(record: OVSND03NCentralDensityDigitizedRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-03N — Digitized anchor: central density from pinned sound PDF (computed)\n\n"
        "Scope / limits\n"
        "- Anchor numeric ingestion only; no physics validation claim\n"
        "- Single-condition density anchor only (no constancy across conditions tested)\n"
        "- No fitting; no imputation; no continuity/averaging across regimes\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd03n_digitized_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-03_central_density_digitized.md"

    rec = ovsnd03n_central_density_digitized_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd03n_digitized_lock_markdown(rec), encoding="utf-8")
    return out
