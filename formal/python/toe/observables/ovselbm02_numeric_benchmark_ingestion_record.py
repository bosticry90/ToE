"""OV-SEL-BM-02: numeric benchmark ingestion narrative (computed lock).

Purpose
- Provide an OV-SEL-style audit lock confirming that adding a minimal numeric
  benchmark artifact (OV-BM-01N) does not trigger policy/regime/selection changes.

Design
- Deterministic.
- Recomputes and checks existing governance locks (OV-SEL-01/02, OV-XD-04, OV-BR-02,
  OV-DQ-02) remain lock==computed.
- Also checks the new OV-BM-01N digitized benchmark lock and that its CSV/metadata
  exist at pinned paths.

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

from formal.python.toe.observables.ovbm01_mean_field_line_shift_scaling_digitized import (
    ovbm01_digitized_mean_shift_dataset_record,
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
class OVSELBM02NumericBenchmarkIngestionRecord:
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


def ovselbm02_numeric_benchmark_ingestion_record(
    *,
    status_date: str = "2026-01-23",
) -> OVSELBM02NumericBenchmarkIngestionRecord:
    repo_root = _find_repo_root(Path(__file__))

    # New numeric benchmark record.
    bm01n = ovbm01_digitized_mean_shift_dataset_record(date=str(status_date))

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
        "OV-BM-01N lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling_digitized.md",
            computed_payload=bm01n.to_jsonable(),
        ),
        "OV-BM-01N CSV exists": _check_path_exists(repo_root=repo_root, rel_path=bm01n.dataset["csv_relpath"]),
        "OV-BM-01N metadata exists": _check_path_exists(
            repo_root=repo_root, rel_path=bm01n.dataset["metadata_relpath"]
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
        "digitization_id": bm01n.digitization_id,
        "observable_id": bm01n.observable_id,
        "schema": bm01n.schema,
        "lock_path": "formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling_digitized.md",
        "record_fingerprint": bm01n.fingerprint(),
        "csv_relpath": bm01n.dataset["csv_relpath"],
        "csv_sha256": bm01n.dataset["csv_sha256"],
        "benchmark_only": True,
    }

    narrative = (
        "Numeric benchmark ingestion audit (bookkeeping-only; no physics claim):\n"
        "1) What changed? Added OV-BM-01N: a minimal numeric digitization (mean shift vs peak density) plus pinned CSV/metadata and a computed benchmark lock.\n"
        "2) What did not change? No policy thresholds changed; no regime bridge behavior changed; no selection logic consequences; no continuity or averaging inferred.\n"
        "3) Why? OV-BM-01N is explicitly benchmark-only and scope-fenced; it is not part of fit-family selection and is introduced solely to stress-test numeric ingestion determinism.\n"
        f"\nSelf-checks (lock==computed + file existence) all_ok={bool(all_ok)} for OV-BM-01N and canonical/DQ-01_v2-parallel governance locks."
    )

    return OVSELBM02NumericBenchmarkIngestionRecord(
        schema="OV-SEL-BM-02_numeric_benchmark_ingestion_audit/v1",
        status_date=str(status_date),
        benchmark_numeric=benchmark_numeric,
        checks=checks,
        narrative=narrative,
    )


def render_ovselbm02_lock_markdown(record: OVSELBM02NumericBenchmarkIngestionRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-BM-02 — Numeric benchmark ingestion audit (computed)\n\n"
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


def write_ovselbm02_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-23") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SEL-BM-02_numeric_benchmark_ingestion_audit.md"
        )

    rec = ovselbm02_numeric_benchmark_ingestion_record(status_date=str(status_date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovselbm02_lock_markdown(rec), encoding="utf-8")
    return out
