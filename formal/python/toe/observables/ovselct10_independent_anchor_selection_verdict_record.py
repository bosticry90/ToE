"""OV-SEL-CT10-01: deterministic CT-10 candidate selection verdict record.

Purpose
- Produce a deterministic, policy-auditable admission verdict for CT-10 pre-activation.
- Enforce the CT-10 independent-anchor selection filter before any comparator lane exists.

Scope / limits
- Pre-activation governance only.
- external_anchor_only posture; no comparator claims.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_text(text: str) -> str:
    return _sha256_bytes(text.encode("utf-8"))


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


def _load_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class OVSELCT1001SelectionVerdictRecord:
    schema: str
    status_date: str
    candidate_id: str
    source_family_id: str
    observable_surface_id: str
    verdict: str
    failed_checks: list[str]
    checks: dict[str, dict[str, Any]]
    policy: dict[str, Any]
    fingerprints: dict[str, str]
    notes: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "candidate_id": str(self.candidate_id),
            "source_family_id": str(self.source_family_id),
            "observable_surface_id": str(self.observable_surface_id),
            "verdict": str(self.verdict),
            "failed_checks": list(self.failed_checks),
            "checks": dict(self.checks),
            "policy": dict(self.policy),
            "fingerprints": dict(self.fingerprints),
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovselct10_selection_verdict_record(*, status_date: str = "2026-02-12") -> OVSELCT1001SelectionVerdictRecord:
    repo_root = _find_repo_root(Path(__file__))
    intake_dir = repo_root / "formal" / "external_evidence" / "ct10_independent_external_anchor_tbd"
    filter_doc = (
        repo_root / "formal" / "docs" / "programs" / "CT10_independent_external_anchor_selection_filter_v0.md"
    )

    metadata_path = intake_dir / "dataset_metadata.json"
    citation_path = intake_dir / "source_citation.md"
    preprocessing_path = intake_dir / "preprocessing_lineage.md"

    metadata = _load_json(metadata_path)
    citation_text = _load_text(citation_path)
    preprocessing_text = _load_text(preprocessing_path)
    filter_text = _load_text(filter_doc)

    dataset_relpath = str(metadata.get("dataset_relpath", "")).strip()
    dataset_path = repo_root / dataset_relpath if dataset_relpath else intake_dir / "__missing__"

    source_family_id = str(metadata.get("source_family_id", ""))
    observable_surface_id = str(metadata.get("observable_surface_id", ""))
    source_lineage = str(metadata.get("source_lineage_independence_statement", ""))
    preprocessing_lineage = str(metadata.get("preprocessing_lineage_independence_statement", ""))
    is_bec_derived = bool(metadata.get("is_bec_derived", True))

    forbidden_source_families = {
        "steinhauer2001_fig3a_digitized_v1",
        "andrews1997_fig2_distancetime_digitized_v1",
        "bec_bragg_steinhauer_2001",
        "bec_sound_andrews_1997",
    }
    forbidden_observable_surfaces = {
        "dispersion_k_omega",
        "distance_um_vs_time_ms",
    }

    checks: dict[str, dict[str, Any]] = {}

    def _add_check(name: str, ok: bool, detail: str) -> None:
        checks[name] = {"ok": bool(ok), "detail": str(detail)}

    _add_check(
        "required_intake_files_present",
        metadata_path.exists() and citation_path.exists() and preprocessing_path.exists() and dataset_path.exists(),
        "metadata/citation/preprocessing/dataset files must all exist",
    )
    _add_check(
        "metadata_schema_v1",
        str(metadata.get("schema", "")) == "CT-10/independent_external_anchor_dataset_metadata/v1",
        "metadata schema must match CT-10 v1",
    )
    _add_check(
        "not_bec_derived",
        is_bec_derived is False,
        "candidate must be explicitly non-BEC-derived",
    )
    _add_check(
        "source_family_independent",
        source_family_id.lower() not in forbidden_source_families and len(source_family_id) > 0,
        "source family must differ from CT-06/07/08 and CT-09 families",
    )
    _add_check(
        "observable_surface_independent",
        observable_surface_id.lower() not in forbidden_observable_surfaces and len(observable_surface_id) > 0,
        "observable surface must differ from existing dispersion and distance-time anchors",
    )
    _add_check(
        "source_lineage_statement_present",
        "independent" in source_lineage.lower() and len(source_lineage.strip()) > 24,
        "source lineage independence statement must be explicit",
    )
    _add_check(
        "preprocessing_lineage_statement_present",
        "no shared preprocessing lineage" in preprocessing_lineage.lower()
        and len(preprocessing_lineage.strip()) > 24,
        "preprocessing lineage independence statement must be explicit",
    )
    _add_check(
        "citation_declares_non_bec_and_independence",
        ("not bec-derived" in citation_text.lower()) and ("independent" in citation_text.lower()),
        "source citation must declare independence and non-BEC posture",
    )
    _add_check(
        "preprocessing_declares_no_shared_lineage",
        "no shared preprocessing lineage" in preprocessing_text.lower(),
        "preprocessing notes must declare no shared lineage",
    )
    _add_check(
        "filter_doc_has_admission_gate_language",
        ("selection filter" in filter_text.lower()) and ("admission gate" in filter_text.lower()),
        "CT-10 filter doc must contain selection-filter admission-gate posture",
    )

    failed = [name for name, row in checks.items() if not bool(row["ok"])]
    verdict = "admissible" if not failed else "rejected"

    fingerprints = {
        "filter_doc_sha256": _sha256_text(filter_text),
        "metadata_sha256": _sha256_bytes(metadata_path.read_bytes()),
        "source_citation_sha256": _sha256_text(citation_text),
        "preprocessing_lineage_sha256": _sha256_text(preprocessing_text),
        "dataset_sha256": _sha256_bytes(dataset_path.read_bytes()) if dataset_path.exists() else "",
    }

    notes = (
        "CT-10 selection verdict is pre-activation governance only. "
        "No comparator claim, no lane activation, and no external truth claim."
    )

    return OVSELCT1001SelectionVerdictRecord(
        schema="OV-SEL-CT10-01_independent_anchor_selection_verdict/v1",
        status_date=str(status_date),
        candidate_id=str(metadata.get("dataset_id", "")),
        source_family_id=source_family_id,
        observable_surface_id=observable_surface_id,
        verdict=verdict,
        failed_checks=failed,
        checks=checks,
        policy={
            "mode": "pre_activation_admission_gate_only",
            "filter_doc": "formal/docs/programs/CT10_independent_external_anchor_selection_filter_v0.md",
            "scope_limit": "external_anchor_only",
        },
        fingerprints=fingerprints,
        notes=notes,
    )


def render_ovselct10_lock_markdown(record: OVSELCT1001SelectionVerdictRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)
    return (
        "# OV-SEL-CT10-01 - CT-10 independent anchor selection verdict (pre-activation)\n\n"
        "Scope / limits\n"
        "- Governance-only pre-activation admission gate\n"
        "- external_anchor_only posture\n"
        "- No comparator claims are permitted\n"
        "- No external truth claim\n\n"
        "Record (deterministic)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovselct10_lock(
    *, lock_path: Path | None = None, status_date: str = "2026-02-12"
) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SEL-CT10-01_independent_anchor_selection_verdict.md"
        )

    rec = ovselct10_selection_verdict_record(status_date=str(status_date))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovselct10_lock_markdown(rec), encoding="utf-8")
    return out
