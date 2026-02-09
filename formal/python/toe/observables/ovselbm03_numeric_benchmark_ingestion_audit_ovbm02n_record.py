"""OV-SEL-BM-03: numeric benchmark ingestion audit for OV-BM-02N (computed lock).

Purpose
- Provide an OV-SEL-style audit lock confirming that adding OV-BM-02N (a minimal
  digitized benchmark dataset) does not trigger policy/regime/selection changes.

Design
- Deterministic.
- Recomputes and checks existing governance locks (OV-SEL-01/02, OV-XD-04, OV-BR-02,
  OV-DQ-02) remain lock==computed.
- Checks OV-BM-02N digitized benchmark lock and that its CSV/metadata exist.

Scope / limits
- Bookkeeping / narrative only; no physics claim.
- Benchmark-only numeric ingestion: no fitting, no averaging, no continuity claim.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovbm02_linewidth_quadrature_composition_digitized import (
    ovbm02_digitized_linewidth_dataset_record,
)
from formal.python.toe.observables.ovbr02_regime_bridge_record import ovbr02_regime_bridge_record
from formal.python.toe.observables.ovdq02_dq01_v2_threshold_update_record import ovdq02_dq01_v2_threshold_update_record
from formal.python.toe.observables.ovsel01_selection_status_record import ovsel01_selection_status_record
from formal.python.toe.observables.ovsel02_selection_status_record import ovsel02_selection_status_record
from formal.python.toe.observables.ovxd04_overlap_only_preference_comparison_record import (
    ovxd04_overlap_only_preference_comparison_record,
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


def _extract_json_block(md_text: str) -> dict[str, Any]:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise ValueError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing record fingerprint line")
    return m.group(1)


def _check_lock_matches(*, repo_root: Path, lock_rel_path: str, computed_payload: dict[str, Any]) -> dict[str, Any]:
    p = repo_root / Path(lock_rel_path)
    text = p.read_text(encoding="utf-8")
    locked = _extract_json_block(text)
    fp = _extract_fingerprint(text)

    ok = bool(locked == computed_payload)

    return {
        "lock_path": str(lock_rel_path).replace("\\", "/"),
        "lock_fingerprint": str(fp),
        "ok": bool(ok),
    }


def _check_path_exists(*, repo_root: Path, rel_path: str) -> dict[str, Any]:
    p = repo_root / Path(rel_path)
    return {
        "path": str(rel_path).replace("\\", "/"),
        "exists": bool(p.exists()),
    }


@dataclass(frozen=True)
class OVSELBM03NumericBenchmarkIngestionRecord:
    schema: str
    status_date: str

    benchmark_numeric: dict[str, Any]
    checks: dict[str, Any]

    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "benchmark_numeric": dict(self.benchmark_numeric),
            "checks": dict(self.checks),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovselbm03_numeric_benchmark_ingestion_record(
    *,
    status_date: str = "2026-01-24",
) -> OVSELBM03NumericBenchmarkIngestionRecord:
    repo_root = _find_repo_root(Path(__file__))

    # New numeric benchmark record.
    bm02n = ovbm02_digitized_linewidth_dataset_record(date=str(status_date))

    # Recompute canonical selection/regime bookkeeping records.
    sel01 = ovsel01_selection_status_record(status_date=str(status_date))
    sel02 = ovsel02_selection_status_record(status_date=str(status_date))
    xd04_v1 = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v1", q_threshold=0.90)
    br02_v1 = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v1", q_threshold=0.90)
    dq02 = ovdq02_dq01_v2_threshold_update_record(date=str(status_date))

    # Parallel v2 downstream bookkeeping records.
    xd04_v2 = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)
    br02_v2 = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)

    checks: dict[str, Any] = {
        "OV-BM-02N lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition_digitized.md",
            computed_payload=bm02n.to_jsonable(),
        ),
        "OV-BM-02N CSV exists": _check_path_exists(repo_root=repo_root, rel_path=bm02n.dataset["csv_relpath"]),
        "OV-BM-02N metadata exists": _check_path_exists(
            repo_root=repo_root, rel_path=bm02n.dataset["metadata_relpath"]
        ),
        "OV-SEL-01": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
            computed_payload=sel01.to_jsonable(),
        ),
        "OV-SEL-02": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
            computed_payload=sel02.to_jsonable(),
        ),
        "OV-XD-04 (v1)": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md",
            computed_payload=xd04_v1.to_jsonable(),
        ),
        "OV-BR-02 (v1)": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
            computed_payload=br02_v1.to_jsonable(),
        ),
        "OV-DQ-02": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/policies/DQ-01_v2_threshold_update.md",
            computed_payload=dq02.to_jsonable(),
        ),
        "OV-XD-04 (DQ-01_v2)": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
            computed_payload=xd04_v2.to_jsonable(),
        ),
        "OV-BR-02 (DQ-01_v2)": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-02_regime_bridge_record_DQ-01_v2.md",
            computed_payload=br02_v2.to_jsonable(),
        ),
    }

    all_ok = all(bool(v.get("ok", True)) for v in checks.values() if isinstance(v, dict)) and all(
        bool(v.get("exists", True)) for v in checks.values() if isinstance(v, dict)
    )

    benchmark_numeric = {
        "digitization_id": bm02n.digitization_id,
        "observable_id": bm02n.observable_id,
        "schema": bm02n.schema,
        "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition_digitized.md",
        "record_fingerprint": bm02n.fingerprint(),
        "csv_relpath": bm02n.dataset["csv_relpath"],
        "csv_sha256": bm02n.dataset["csv_sha256"],
        "benchmark_only": True,
    }

    narrative = (
        "Numeric benchmark ingestion audit (bookkeeping-only; no physics claim):\n"
        "1) What changed? Added OV-BM-02N: a minimal numeric digitization (linewidth vs peak density) plus pinned CSV/metadata and a computed benchmark lock.\n"
        "2) What did not change? No policy thresholds changed; no regime bridge behavior changed; no selection logic consequences; no continuity or averaging inferred.\n"
        "3) Why? OV-BM-02N is explicitly benchmark-only and scope-fenced; it is not part of fit-family selection and is introduced solely to stress-test numeric ingestion determinism.\n"
        f"\nSelf-checks (lock==computed + file existence) all_ok={bool(all_ok)} for OV-BM-02N and canonical/DQ-01_v2-parallel governance locks."
    )

    return OVSELBM03NumericBenchmarkIngestionRecord(
        schema="OV-SEL-BM-03_numeric_benchmark_ingestion_audit_OV-BM-02N/v1",
        status_date=str(status_date),
        benchmark_numeric=benchmark_numeric,
        checks=checks,
        narrative=narrative,
    )


def render_ovselbm03_lock_markdown(record: OVSELBM03NumericBenchmarkIngestionRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-BM-03 — Numeric benchmark ingestion audit (OV-BM-02N) (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- Benchmark-only numeric ingestion; no fitting; no averaging; no continuity claim\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovselbm03_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SEL-BM-03_numeric_benchmark_ingestion_audit_OV-BM-02N.md"
        )

    rec = ovselbm03_numeric_benchmark_ingestion_record(status_date=str(status_date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovselbm03_lock_markdown(rec), encoding="utf-8")
    return out
