"""OV-SEL-BM-01: benchmark ingestion stress-test narrative (computed lock).

Purpose
- Provide an OV-SEL-style, plain-language audit lock confirming that introducing
  symbolic-only benchmark observables does not trigger model selection, regime
  averaging, or policy changes.

Design
- Deterministic.
- Reads existing locks and recomputes corresponding records to confirm equality.
- Records benchmark-only classification and scope fences.

Scope / limits
- Bookkeeping / narrative only; no physics claim.
- This is a stress-test of regime/selection machinery boundaries, not validation.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovbm01_mean_field_line_shift_scaling_benchmark import (
    ovbm01_mean_field_line_shift_scaling_benchmark,
)
from formal.python.toe.observables.ovbm02_linewidth_quadrature_composition_benchmark import (
    ovbm02_linewidth_quadrature_composition_benchmark,
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


@dataclass(frozen=True)
class OVSELBM01BenchmarkIngestionStressTestRecord:
    schema: str
    status_date: str

    benchmarks: dict[str, Any]
    checks: dict[str, Any]

    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "benchmarks": dict(self.benchmarks),
            "checks": dict(self.checks),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovselbm01_benchmark_ingestion_stress_test_record(
    *,
    status_date: str = "2026-01-23",
) -> OVSELBM01BenchmarkIngestionStressTestRecord:
    repo_root = _find_repo_root(Path(__file__))

    bm01 = ovbm01_mean_field_line_shift_scaling_benchmark()
    bm02 = ovbm02_linewidth_quadrature_composition_benchmark()

    # Compute canonical selection/regime bookkeeping records.
    sel01 = ovsel01_selection_status_record(status_date=str(status_date))
    sel02 = ovsel02_selection_status_record(status_date=str(status_date))
    xd04_v1 = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v1", q_threshold=0.90)
    br02_v1 = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v1", q_threshold=0.90)
    dq02 = ovdq02_dq01_v2_threshold_update_record(date=str(status_date))

    # Compute the parallel v2 downstream bookkeeping records.
    xd04_v2 = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)
    br02_v2 = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)

    # Confirm the canonical and v2 locks match their computed records.
    checks: dict[str, Any] = {
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

    benchmarks = {
        "OV-BM-01": {
            "schema": bm01.schema,
            "lock_path": "formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling.md",
            "record_fingerprint": bm01.fingerprint(),
            "non_decisive_by_design": True,
            "symbolic_only": True,
        },
        "OV-BM-02": {
            "schema": bm02.schema,
            "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition.md",
            "record_fingerprint": bm02.fingerprint(),
            "non_decisive_by_design": True,
            "symbolic_only": True,
        },
        "scope_fences": {
            "no_digitization": True,
            "no_curve_fitting": True,
            "no_regime_averaging": True,
            "no_continuity_claim": True,
            "no_cross_observable_inference": True,
        },
    }

    all_ok = all(bool(v.get("ok")) for v in checks.values())

    narrative = (
        "Benchmark ingestion stress test (bookkeeping-only; no physics claim):\n"
        "1) What changed? Added two symbolic-only benchmark observables OV-BM-01 and OV-BM-02 (Stenger 1999 reference provenance).\n"
        "2) What did not change? No regime decisions, no preferences, no thresholds, no selection logic consequences.\n"
        "3) Why? Benchmarks are non-decisive by design and are explicitly scope-fenced (no digitization, no fitting, no averaging, no continuity).\n"
        f"\nSelf-checks (lock==computed) all_ok={bool(all_ok)} for canonical and DQ-01_v2-parallel downstream bookkeeping locks."
    )

    return OVSELBM01BenchmarkIngestionStressTestRecord(
        schema="OV-SEL-BM-01_benchmark_ingestion_stress_test/v1",
        status_date=str(status_date),
        benchmarks=benchmarks,
        checks=checks,
        narrative=narrative,
    )


def render_ovselbm01_lock_markdown(record: OVSELBM01BenchmarkIngestionStressTestRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-BM-01 — Benchmark ingestion stress test (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- Symbolic-only benchmarks; no digitization, no fitting\n"
        "- No regime averaging; no continuity claim; no cross-observable inference\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovselbm01_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-23") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SEL-BM-01_benchmark_ingestion_stress_test.md"
        )

    rec = ovselbm01_benchmark_ingestion_stress_test_record(status_date=str(status_date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovselbm01_lock_markdown(rec), encoding="utf-8")
    return out
