from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA_ID = "RUNTIME_MEASUREMENT_HISTORY_20260411_v0"
MAX_ROLE_SAMPLES = 50


def _ts() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {
            "schema_id": SCHEMA_ID,
            "status": "ACTIVE_NONLIVE_NONCLAIM",
            "captured_at_utc": _ts(),
            "samples": {
                "baseline": [],
                "snapshot": [],
            },
            "non_claim_boundary": "Repository-local runtime history only; no scientific adequacy claim.",
        }
    return json.loads(path.read_text(encoding="utf-8"))


def record_runtime_sample(
    *,
    history_path: Path,
    role: str,
    measurement_mode: str,
    runtime_seconds: dict[str, float],
    command_sha256: dict[str, str],
) -> tuple[int, dict[str, float]]:
    if role not in {"baseline", "snapshot"}:
        raise ValueError("role must be baseline or snapshot")

    payload = _read_json(history_path)
    samples = payload.setdefault("samples", {})
    role_samples = list(samples.get(role, []))

    role_samples.append(
        {
            "captured_at_utc": _ts(),
            "measurement_mode": measurement_mode,
            "runtime_seconds": runtime_seconds,
            "command_sha256": command_sha256,
        }
    )
    if len(role_samples) > MAX_ROLE_SAMPLES:
        role_samples = role_samples[-MAX_ROLE_SAMPLES:]
    samples[role] = role_samples

    measured_samples = [s for s in role_samples if s.get("measurement_mode") == "MEASURED"]
    measured_runtime = [s.get("runtime_seconds", {}) for s in measured_samples]

    stats: dict[str, float] = {}
    for key in ("governance_suite", "branch_health_full_pytest", "checkpoint_ladder"):
        values: list[float] = []
        for entry in measured_runtime:
            value = entry.get(key)
            if isinstance(value, (int, float)):
                values.append(float(value))
        if values:
            mean = sum(values) / len(values)
            stats[f"{key}_mean"] = round(mean, 3)
            max_dev = max(abs(v - mean) for v in values)
            stats[f"{key}_max_abs_deviation"] = round(max_dev, 3)

    payload["captured_at_utc"] = _ts()
    history_path.parent.mkdir(parents=True, exist_ok=True)
    history_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return len(measured_samples), stats
