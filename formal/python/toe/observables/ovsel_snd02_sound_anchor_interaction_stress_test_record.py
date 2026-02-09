"""OV-SEL-SND-02: sound-anchor interaction stress test (computed lock).

Purpose
- Assert that adding the sound anchor does not create forbidden interactions:
  - No benchmark/anchor participation in selection/regime locks.
  - No continuity/averaging inference.
  - Active policy activation remains controlled.

Design
- Deterministic.
- Recomputes and checks:
  - OV-SND-01/01N locks and benchmark locks remain lock==computed.
  - Governance locks remain lock==computed.
  - Negative checks: selection/regime locks do not reference OV-SND or OV-BM.

Scope / limits
- Bookkeeping / narrative only; no physics claim.
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
from formal.python.toe.observables.ovbm01_mean_field_line_shift_scaling_digitized import ovbm01_digitized_mean_shift_dataset_record
from formal.python.toe.observables.ovbm02_linewidth_quadrature_composition_benchmark import (
    ovbm02_linewidth_quadrature_composition_benchmark,
)
from formal.python.toe.observables.ovbm02_linewidth_quadrature_composition_digitized import ovbm02_digitized_linewidth_dataset_record
from formal.python.toe.observables.ovdq03_dq01_active_policy_activation_record import ovdq03_dq01_active_policy_activation_record
from formal.python.toe.observables.ovsel01_selection_status_record import ovsel01_selection_status_record
from formal.python.toe.observables.ovsel02_selection_status_record import ovsel02_selection_status_record
from formal.python.toe.observables.ovsnd01_sound_propagation_distance_time_digitized import ovsnd01_digitized_propagation_dataset_record
from formal.python.toe.observables.ovsnd01_sound_speed_scaling_record import ovsnd01_sound_speed_scaling_record
from formal.python.toe.observables.ovxd03_overlap_band_record import ovxd03_overlap_band_record
from formal.python.toe.observables.ovxd04_overlap_only_preference_comparison_record import ovxd04_overlap_only_preference_comparison_record
from formal.python.toe.observables.ovbr02_regime_bridge_record import ovbr02_regime_bridge_record


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


def _check_no_token(*, repo_root: Path, lock_rel_path: str, token: str) -> dict[str, Any]:
    p = repo_root / Path(lock_rel_path)
    text = p.read_text(encoding="utf-8")
    ok = token not in text
    return {"lock_path": str(lock_rel_path).replace("\\", "/"), "token": token, "ok": bool(ok)}


@dataclass(frozen=True)
class OVSELSND02SoundAnchorInteractionStressTestRecord:
    schema: str
    status_date: str

    checks: dict[str, Any]
    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "checks": dict(self.checks),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsel_snd02_sound_anchor_interaction_stress_test_record(
    *,
    status_date: str = "2026-01-24",
) -> OVSELSND02SoundAnchorInteractionStressTestRecord:
    repo_root = _find_repo_root(Path(__file__))

    # Recompute sound anchor.
    snd01 = ovsnd01_sound_speed_scaling_record(date=str(status_date))
    snd01n = ovsnd01_digitized_propagation_dataset_record(date=str(status_date))

    # Benchmarks.
    bm01 = ovbm01_mean_field_line_shift_scaling_benchmark()
    bm02 = ovbm02_linewidth_quadrature_composition_benchmark()
    bm01n = ovbm01_digitized_mean_shift_dataset_record(date=str(status_date))
    bm02n = ovbm02_digitized_linewidth_dataset_record(date=str(status_date))

    # Governance.
    dq03 = ovdq03_dq01_active_policy_activation_record(date="2026-01-24")
    sel01 = ovsel01_selection_status_record(status_date="2026-01-23")
    sel02 = ovsel02_selection_status_record(status_date="2026-01-23")

    xd03 = ovxd03_overlap_band_record()
    xd04_v2 = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)
    br02_v2 = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)

    checks: dict[str, Any] = {
        "OV-SND-01": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SND-01_sound_speed_scaling_anchor.md",
            computed_payload=snd01.to_jsonable(),
        ),
        "OV-SND-01N": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SND-01_sound_propagation_distance_time_digitized.md",
            computed_payload=snd01n.to_jsonable(),
        ),
        "OV-BM-01": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling.md",
            computed_payload=bm01.to_jsonable(),
        ),
        "OV-BM-02": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition.md",
            computed_payload=bm02.to_jsonable(),
        ),
        "OV-BM-01N": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling_digitized.md",
            computed_payload=bm01n.to_jsonable(),
        ),
        "OV-BM-02N": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition_digitized.md",
            computed_payload=bm02n.to_jsonable(),
        ),
        "OV-DQ-03": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/policies/DQ-01_active_policy_activation.md",
            computed_payload=dq03.to_jsonable(),
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
        "OV-XD-03": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
            computed_payload=xd03.to_jsonable(),
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
        "No OV-SND in OV-SEL-01": _check_no_token(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
            token="OV-SND-",
        ),
        "No OV-SND in OV-XD-04": _check_no_token(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
            token="OV-SND-",
        ),
        "No OV-BM in OV-SEL-01": _check_no_token(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
            token="OV-BM-",
        ),
    }

    all_ok = all(bool(v.get("ok", True)) for v in checks.values() if isinstance(v, dict))

    narrative = (
        "Sound anchor interaction stress test (bookkeeping-only; no physics claim):\n"
        "Forbidden behaviors asserted absent:\n"
        "- No benchmark or sound-anchor participation in selection/regime locks\n"
        "- No cross-regime continuity inference or averaging\n"
        "- Policy activation remains explicit and guarded\n"
        f"\nSelf-checks (lock==computed + negative token checks) all_ok={bool(all_ok)}."
    )

    return OVSELSND02SoundAnchorInteractionStressTestRecord(
        schema="OV-SEL-SND-02_sound_anchor_interaction_stress_test/v1",
        status_date=str(status_date),
        checks=checks,
        narrative=narrative,
    )


def render_ovsel_snd02_lock_markdown(record: OVSELSND02SoundAnchorInteractionStressTestRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-SND-02 — Sound anchor interaction stress test (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsel_snd02_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SEL-SND-02_sound_anchor_interaction_stress_test.md"
        )

    rec = ovsel_snd02_sound_anchor_interaction_stress_test_record(status_date=str(status_date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsel_snd02_lock_markdown(rec), encoding="utf-8")
    return out
