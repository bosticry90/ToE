from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Literal


LaneKind = Literal["canonical_disabled_default", "override_enabled", "mixed"]


@dataclass(frozen=True)
class OVDRBR01LaneProfile:
    lane_kind: LaneKind
    is_override: bool
    manifest_path: str
    gate_enablement: dict[str, bool]


def _read_manifest(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def ovdrbr01_lane_profile_from_manifest(
    manifest_path: str | Path,
    *,
    required_gate_ids: list[str] | tuple[str, ...] = ("CT01", "SYM01", "CAUS01"),
) -> OVDRBR01LaneProfile:
    path = Path(manifest_path)
    manifest = _read_manifest(path)
    gates = dict(manifest.get("gates") or {})

    gate_enablement = {
        str(gid): bool((gates.get(str(gid)) or {}).get("enabled", False))
        for gid in required_gate_ids
    }

    vals = list(gate_enablement.values())
    if vals and all(v is False for v in vals):
        kind: LaneKind = "canonical_disabled_default"
    elif vals and all(v is True for v in vals):
        kind = "override_enabled"
    else:
        kind = "mixed"

    return OVDRBR01LaneProfile(
        lane_kind=kind,
        is_override=(kind == "override_enabled"),
        manifest_path=str(path),
        gate_enablement=gate_enablement,
    )
