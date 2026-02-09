from __future__ import annotations

"""Toy topological invariants front door (quarantine-safe).

Goal
- Deterministic report for a toy topological invariant proxy.
- Bookkeeping only: consequences from structure, no physics claim.

Report schema (v1)
{
  "schema": "TOY/topological_invariants_report/v1",
  "tool_version": "v1",
  "candidate_id": "G1_sign_change",
  "inputs": {...},
  "input_fingerprint": "...",
  "params": {...},
  "output": {...},
  "scope_limits": [...],
  "fingerprint": "..."
}
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
from dataclasses import dataclass
import hashlib
import json
from math import isfinite
from pathlib import Path
from typing import Any, Dict, Optional


SCHEMA_ID = "TOY/topological_invariants_report/v1"
TOOL_VERSION = "v1"
CANDIDATE_IDS = ("G1_sign_change",)
DETECTOR_IDS = ("sign_change", "threshold_count")


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _canonical_json(payload: object) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _sha256_json(payload: object) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _q(x: float, *, sig: int = 12) -> float:
    """Quantize floats for stable JSON across platforms."""

    return float(f"{float(x):.{int(sig)}g}")


@dataclass(frozen=True)
class TopologicalStateInput:
    grid: list[float]

    def __post_init__(self) -> None:
        if not isinstance(self.grid, list):
            raise ValueError("TopologicalStateInput.grid must be a list of floats")
        if len(self.grid) < 2:
            raise ValueError("TopologicalStateInput.grid must have length >= 2")
        for val in self.grid:
            if not isfinite(float(val)):
                raise ValueError("TopologicalStateInput.grid entries must be finite")


@dataclass(frozen=True)
class ToyGParams:
    step_size: float = 0.1
    detector_id: str = "sign_change"
    threshold: float = 0.0

    def __post_init__(self) -> None:
        if not isfinite(float(self.step_size)):
            raise ValueError("ToyGParams.step_size must be finite")
        if self.detector_id not in DETECTOR_IDS:
            raise ValueError(f"detector_id must be one of {DETECTOR_IDS}")
        if not isfinite(float(self.threshold)):
            raise ValueError("ToyGParams.threshold must be finite")


@dataclass(frozen=True)
class ToyGInput:
    state: TopologicalStateInput
    params: ToyGParams
    candidate_id: str = "G1_sign_change"

    def __post_init__(self) -> None:
        if self.candidate_id not in CANDIDATE_IDS:
            raise ValueError(f"candidate_id must be one of {CANDIDATE_IDS}")


def _sign(x: float) -> int:
    if x > 0.0:
        return 1
    if x < 0.0:
        return -1
    return 0


def _defects_sign_change(grid: list[float]) -> dict:
    signs = [_sign(float(x)) for x in grid]
    locations: list[int] = []
    for i in range(len(signs) - 1):
        a = signs[i]
        b = signs[i + 1]
        if a == 0 or b == 0:
            continue
        if a != b:
            locations.append(i + 1)
    return {
        "count": int(len(locations)),
        "locations": locations,
    }


def _defects_threshold_count(grid: list[float], threshold: float) -> dict:
    locations = [i for i, x in enumerate(grid) if float(x) > float(threshold)]
    return {
        "count": int(len(locations)),
        "locations": locations,
    }


def _apply_step(grid: list[float], step_size: float) -> list[float]:
    factor = 1.0 - float(step_size)
    return [float(x) * factor for x in grid]


def _detect(defector: str, grid: list[float], threshold: float) -> dict:
    if defector == "sign_change":
        return _defects_sign_change(grid)
    if defector == "threshold_count":
        return _defects_threshold_count(grid, threshold)
    raise ValueError(f"Unsupported detector_id: {defector}")


def build_toy_topological_invariants_report(inp: ToyGInput) -> Dict[str, Any]:
    state_payload = {"grid": [_q(float(x)) for x in inp.state.grid]}
    params_payload = {
        "step_size": _q(float(inp.params.step_size)),
        "detector_id": str(inp.params.detector_id),
        "threshold": _q(float(inp.params.threshold)),
    }

    inputs_payload = {
        "candidate_id": str(inp.candidate_id),
        "state": state_payload,
        "params": params_payload,
        "fingerprints": {
            "state": _sha256_json(state_payload),
            "params": _sha256_json(params_payload),
        },
    }

    grid_before = [float(x) for x in inp.state.grid]
    grid_after = _apply_step(grid_before, float(inp.params.step_size))

    defects_before = _detect(inp.params.detector_id, grid_before, float(inp.params.threshold))
    defects_after = _detect(inp.params.detector_id, grid_after, float(inp.params.threshold))

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "input_fingerprint": _sha256_json(inputs_payload),
        "params": dict(params_payload),
        "output": {
            "state_before": [_q(x) for x in grid_before],
            "state_after": [_q(x) for x in grid_after],
            "defects_before": {
                "detector_id": str(inp.params.detector_id),
                "count": int(defects_before["count"]),
                "locations": list(defects_before["locations"]),
            },
            "defects_after": {
                "detector_id": str(inp.params.detector_id),
                "count": int(defects_after["count"]),
                "locations": list(defects_after["locations"]),
            },
        },
        "scope_limits": [
            "structure_only; no physics claim",
            "bounded evidence only; consequence engine",
        ],
    }

    fingerprint_payload = {
        "schema": SCHEMA_ID,
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "params": params_payload,
    }
    payload["fingerprint"] = _sha256_json(fingerprint_payload)
    return payload


def dumps_toy_topological_invariants_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> ToyGInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        state = TopologicalStateInput(grid=list(raw["state"]["grid"]))
        params_raw = raw.get("params", {})
        params = ToyGParams(
            step_size=float(params_raw.get("step_size", ToyGParams().step_size)),
            detector_id=str(params_raw.get("detector_id", ToyGParams().detector_id)),
            threshold=float(params_raw.get("threshold", ToyGParams().threshold)),
        )
        candidate_id = str(raw.get("candidate_id", "G1_sign_change"))
        return ToyGInput(state=state, params=params, candidate_id=candidate_id)

    if args.state_grid_json is None:
        raise SystemExit("Missing required arg: --state-grid-json")

    state = TopologicalStateInput(grid=json.loads(args.state_grid_json))
    params = ToyGParams(
        step_size=float(args.step_size),
        detector_id=str(args.detector_id),
        threshold=float(args.threshold),
    )

    return ToyGInput(state=state, params=params, candidate_id=str(args.candidate_id))


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy topological-invariants report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--state-grid-json", help="Inline JSON list for substrate grid (length >= 2)")
    p.add_argument("--candidate-id", choices=list(CANDIDATE_IDS), default="G1_sign_change")
    p.add_argument("--step-size", type=float, default=ToyGParams().step_size)
    p.add_argument("--detector-id", choices=list(DETECTOR_IDS), default=ToyGParams().detector_id)
    p.add_argument("--threshold", type=float, default=ToyGParams().threshold)
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (write only when provided)",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_topological_invariants_report(inp)
    out_text = dumps_toy_topological_invariants_report(payload)

    if args.out:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
