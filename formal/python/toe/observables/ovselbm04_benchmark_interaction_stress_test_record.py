"""OV-SEL-BM-04: benchmark interaction stress-test (computed lock).

Purpose
- Prove (as a test-enforced, lock==computed record) that benchmark observables
  (OV-BM-01/02 and OV-BM-01N) do not participate in regime logic, overlap
  bookkeeping, or selection outcomes.

What this *does*
- Enumerates explicit "forbidden behaviors" (continuity inference, regime
  averaging, benchmark-driven selection flips).
- Confirms key governance locks remain lock==computed.
- Adds structural "negative checks" (e.g., OV-XD/OV-BR/OV-SEL locks must not
  reference OV-BM-*; overlap-band included IDs must be limited to non-benchmark
  dataset observables).

What this *does not* do
- No new physics claims.
- No new digitization.
- No changes to selection policies.

Design constraints
- Deterministic (no RNG, no network).
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
from formal.python.toe.observables.ovbm01_mean_field_line_shift_scaling_digitized import (
    ovbm01_digitized_mean_shift_dataset_record,
)
from formal.python.toe.observables.ovbr02_regime_bridge_record import ovbr02_regime_bridge_record
from formal.python.toe.observables.ovdq02_dq01_v2_threshold_update_record import ovdq02_dq01_v2_threshold_update_record
from formal.python.toe.observables.ovsel01_selection_status_record import ovsel01_selection_status_record
from formal.python.toe.observables.ovsel02_selection_status_record import ovsel02_selection_status_record
from formal.python.toe.observables.ovselbm01_benchmark_ingestion_stress_test_record import (
    ovselbm01_benchmark_ingestion_stress_test_record,
)
from formal.python.toe.observables.ovselbm02_numeric_benchmark_ingestion_record import (
    ovselbm02_numeric_benchmark_ingestion_record,
)
from formal.python.toe.observables.ovxd03_overlap_band_record import ovxd03_overlap_band_record
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


def _check_no_benchmark_references(*, repo_root: Path, lock_rel_path: str) -> dict[str, Any]:
    p = repo_root / Path(lock_rel_path)
    text = p.read_text(encoding="utf-8")

    # Conservative: no OV-BM-* references in selection/regime bookkeeping locks.
    forbidden = ["OV-BM-01", "OV-BM-01N", "OV-BM-02", "OV-BM-"]
    found = sorted({t for t in forbidden if t in text})

    return {
        "lock_path": str(lock_rel_path).replace("\\", "/"),
        "forbidden_tokens_found": list(found),
        "ok": bool(len(found) == 0),
    }


def _check_xd03_band_ids_are_non_benchmark(*, included_band_ids: list[str]) -> dict[str, Any]:
    allowed = {"OV-01g", "OV-02x", "OV-03x", "OV-04x"}
    extra = sorted({str(x) for x in included_band_ids if str(x) not in allowed})
    return {
        "allowed": sorted(allowed),
        "included_band_ids": list(included_band_ids),
        "unexpected_ids": list(extra),
        "ok": bool(len(extra) == 0),
    }


@dataclass(frozen=True)
class OVSELBM04BenchmarkInteractionStressTestRecord:
    schema: str
    status_date: str

    forbidden_behaviors: list[str]
    checks: dict[str, Any]
    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "forbidden_behaviors": list(self.forbidden_behaviors),
            "checks": dict(self.checks),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovselbm04_benchmark_interaction_stress_test_record(
    *,
    status_date: str = "2026-01-23",
) -> OVSELBM04BenchmarkInteractionStressTestRecord:
    repo_root = _find_repo_root(Path(__file__))

    # Benchmarks: confirm their locks still compute, but treat them as non-participating.
    bm01 = ovbm01_mean_field_line_shift_scaling_benchmark()
    bm02 = ovbm02_linewidth_quadrature_composition_benchmark()
    bm01n = ovbm01_digitized_mean_shift_dataset_record(date=str(status_date))

    # Compute canonical governance locks.
    xd03 = ovxd03_overlap_band_record()
    sel01 = ovsel01_selection_status_record(status_date=str(status_date))
    sel02 = ovsel02_selection_status_record(status_date=str(status_date))

    xd04_v1 = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v1", q_threshold=0.90)
    br02_v1 = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v1", q_threshold=0.90)

    dq02 = ovdq02_dq01_v2_threshold_update_record(date=str(status_date))

    xd04_v2 = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)
    br02_v2 = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)

    # Existing benchmark bookkeeping locks.
    bm01_stress = ovselbm01_benchmark_ingestion_stress_test_record(status_date=str(status_date))
    bm02_audit = ovselbm02_numeric_benchmark_ingestion_record(status_date=str(status_date))

    forbidden_behaviors = [
        "infer_continuity_across_benchmark_and_dataset_regimes",
        "average_across_regimes_or_overlap_bands",
        "allow_benchmarks_to_participate_in_selection_logic",
        "allow_benchmarks_to_flip_preferences_or_threshold_outcomes",
    ]

    checks: dict[str, Any] = {
        # Benchmarks remain benchmark-only and non-decisive.
        "OV-BM-01 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling.md",
            computed_payload=bm01.to_jsonable(),
        ),
        "OV-BM-02 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition.md",
            computed_payload=bm02.to_jsonable(),
        ),
        "OV-BM-01N lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling_digitized.md",
            computed_payload=bm01n.to_jsonable(),
        ),
        # Primary regime/selection bookkeeping locks must remain lock==computed.
        "OV-XD-03 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
            computed_payload=xd03.to_jsonable(),
        ),
        "OV-SEL-01 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
            computed_payload=sel01.to_jsonable(),
        ),
        "OV-SEL-02 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
            computed_payload=sel02.to_jsonable(),
        ),
        "OV-XD-04 (v1) lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md",
            computed_payload=xd04_v1.to_jsonable(),
        ),
        "OV-BR-02 (v1) lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
            computed_payload=br02_v1.to_jsonable(),
        ),
        "OV-DQ-02 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/policies/DQ-01_v2_threshold_update.md",
            computed_payload=dq02.to_jsonable(),
        ),
        "OV-XD-04 (DQ-01_v2) lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
            computed_payload=xd04_v2.to_jsonable(),
        ),
        "OV-BR-02 (DQ-01_v2) lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-02_regime_bridge_record_DQ-01_v2.md",
            computed_payload=br02_v2.to_jsonable(),
        ),
        # Benchmark audit locks still hold.
        "OV-SEL-BM-01 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-BM-01_benchmark_ingestion_stress_test.md",
            computed_payload=bm01_stress.to_jsonable(),
        ),
        "OV-SEL-BM-02 lock": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-BM-02_numeric_benchmark_ingestion_audit.md",
            computed_payload=bm02_audit.to_jsonable(),
        ),
        # Negative checks: selection/regime locks must not mention OV-BM-*.
        "No benchmark refs in OV-XD-03": _check_no_benchmark_references(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
        ),
        "No benchmark refs in OV-XD-04 (v1)": _check_no_benchmark_references(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md",
        ),
        "No benchmark refs in OV-BR-02 (v1)": _check_no_benchmark_references(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
        ),
        "No benchmark refs in OV-SEL-01": _check_no_benchmark_references(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
        ),
        "No benchmark refs in OV-SEL-02": _check_no_benchmark_references(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
        ),
        # Structural checks: OV-XD-03 included band ids must be limited to dataset observables.
        "OV-XD-03 band IDs are non-benchmark": _check_xd03_band_ids_are_non_benchmark(
            included_band_ids=list(xd03.to_jsonable().get("included_band_ids", []))
        ),
        # Structural checks: OV-XD-04/OV-BR-02 must remain only OV-04x vs OV-03x.
        "OV-XD-04 (v1) compares datasets": {
            "low_observable_id": xd04_v1.low_observable_id,
            "high_observable_id": xd04_v1.high_observable_id,
            "ok": bool(xd04_v1.low_observable_id == "OV-04x" and xd04_v1.high_observable_id == "OV-03x"),
        },
        "OV-BR-02 (v1) compares datasets": {
            "low_pref_observable_id": str(br02_v1.low_preference.get("observable_id")),
            "high_pref_observable_id": str(br02_v1.high_preference.get("observable_id")),
            "ok": bool(
                str(br02_v1.low_preference.get("observable_id")) == "OV-04x"
                and str(br02_v1.high_preference.get("observable_id")) == "OV-03x"
            ),
        },
    }

    # Determine overall OK.
    def _ok(v: Any) -> bool:
        if isinstance(v, dict) and "ok" in v:
            return bool(v["ok"])
        return True

    all_ok = all(_ok(v) for v in checks.values())

    narrative = (
        "Benchmark interaction stress-test (bookkeeping-only; no physics claim):\n"
        "Forbidden behaviors enumerated and blocked by construction: "
        + ", ".join(forbidden_behaviors)
        + ".\n"
        "This record confirms that benchmark observables remain non-participating nodes: "
        "OV-XD/OV-BR/OV-SEL bookkeeping locks do not reference OV-BM-* and their computed payloads remain unchanged.\n"
        f"\nSelf-checks (lock==computed + negative reference checks) all_ok={bool(all_ok)}."
    )

    return OVSELBM04BenchmarkInteractionStressTestRecord(
        schema="OV-SEL-BM-04_benchmark_interaction_stress_test/v1",
        status_date=str(status_date),
        forbidden_behaviors=list(forbidden_behaviors),
        checks=checks,
        narrative=narrative,
    )


def render_ovselbm04_lock_markdown(record: OVSELBM04BenchmarkInteractionStressTestRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-BM-04 — Benchmark interaction stress test (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- Stress-tests that benchmarks cannot affect regime logic or selection\n"
        "- No fitting; no averaging; no continuity claim; no cross-observable inference\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovselbm04_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-23") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SEL-BM-04_benchmark_interaction_stress_test.md"
        )

    rec = ovselbm04_benchmark_interaction_stress_test_record(status_date=str(status_date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovselbm04_lock_markdown(rec), encoding="utf-8")
    return out
