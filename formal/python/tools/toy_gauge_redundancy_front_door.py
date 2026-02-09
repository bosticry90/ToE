from __future__ import annotations

"""Toy gauge redundancy front door (quarantine-safe).

Goal
- Deterministic report for a toy gauge redundancy scaffold.
- Bookkeeping only: consequences from structure, no physics claim.

Report schema (v1)
{
  "schema": "TOY/gauge_redundancy_report/v1",
  "tool_version": "v1",
  "candidate_id": "H1_phase_gauge",
  "inputs": {...},
  "input_fingerprint": "...",
  "params": {...},
  "output": {...},
  "diagnostics": {...},
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
from math import cos, isfinite, sin, sqrt
from pathlib import Path
from typing import Any, Dict, Optional


SCHEMA_ID = "TOY/gauge_redundancy_report/v1"
TOOL_VERSION = "v1"
CANDIDATE_IDS = ("H1_phase_gauge", "H2_local_phase_gauge")
GAUGE_KINDS = ("phase_rotate", "local_phase_rotate")


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
class GaugeStateInput:
    grid: list[list[float]]

    def __post_init__(self) -> None:
        if not isinstance(self.grid, list) or len(self.grid) < 1:
            raise ValueError("GaugeStateInput.grid must be a non-empty list")
        for vec in self.grid:
            if not isinstance(vec, list) or len(vec) != 2:
                raise ValueError("Each grid entry must be a length-2 list")
            for val in vec:
                if not isfinite(float(val)):
                    raise ValueError("GaugeStateInput.grid entries must be finite")


@dataclass(frozen=True)
class ToyHParams:
    dt: float = 0.1
    steps: int = 1
    theta: float = 0.3
    theta_step: float = 0.0
    epsilon: float = 1e-9
    gauge_kind: str = "phase_rotate"

    def __post_init__(self) -> None:
        if not isfinite(float(self.dt)):
            raise ValueError("ToyHParams.dt must be finite")
        if not isinstance(self.steps, int) or self.steps < 1:
            raise ValueError("ToyHParams.steps must be a positive integer")
        if not isfinite(float(self.theta)):
            raise ValueError("ToyHParams.theta must be finite")
        if not isfinite(float(self.theta_step)):
            raise ValueError("ToyHParams.theta_step must be finite")
        if not isfinite(float(self.epsilon)):
            raise ValueError("ToyHParams.epsilon must be finite")
        if float(self.epsilon) <= 0.0:
            raise ValueError("ToyHParams.epsilon must be > 0")
        if self.gauge_kind not in GAUGE_KINDS:
            raise ValueError(f"gauge_kind must be one of {GAUGE_KINDS}")


@dataclass(frozen=True)
class ToyHInput:
    state: GaugeStateInput
    params: ToyHParams
    candidate_id: str = "H1_phase_gauge"

    def __post_init__(self) -> None:
        if self.candidate_id not in CANDIDATE_IDS:
            raise ValueError(f"candidate_id must be one of {CANDIDATE_IDS}")
        if self.candidate_id == "H1_phase_gauge" and self.params.gauge_kind != "phase_rotate":
            raise ValueError("H1_phase_gauge requires gauge_kind='phase_rotate'")
        if self.candidate_id == "H2_local_phase_gauge" and self.params.gauge_kind != "local_phase_rotate":
            raise ValueError("H2_local_phase_gauge requires gauge_kind='local_phase_rotate'")


def _rotate(vec: list[float], theta: float) -> list[float]:
    x, y = float(vec[0]), float(vec[1])
    c = cos(theta)
    s = sin(theta)
    return [x * c - y * s, x * s + y * c]

def _rotate_local(grid: list[list[float]], theta: float, theta_step: float) -> list[list[float]]:
    return [_rotate(vec, float(theta) + float(theta_step) * float(i)) for i, vec in enumerate(grid)]


def _apply_steps(grid: list[list[float]], dt: float, steps: int) -> list[list[float]]:
    factor = (1.0 - float(dt)) ** int(steps)
    return [[float(x) * factor, float(y) * factor] for x, y in grid]


def _magnitudes(grid: list[list[float]]) -> list[float]:
    return [sqrt(float(x) * float(x) + float(y) * float(y)) for x, y in grid]


def build_toy_gauge_redundancy_report(inp: ToyHInput) -> Dict[str, Any]:
    state_payload = {"grid": [[_q(float(x)), _q(float(y))] for x, y in inp.state.grid]}
    params_payload = {
        "dt": _q(float(inp.params.dt)),
        "steps": int(inp.params.steps),
        "theta": _q(float(inp.params.theta)),
        "theta_step": _q(float(inp.params.theta_step)),
        "epsilon": _q(float(inp.params.epsilon)),
        "gauge_kind": str(inp.params.gauge_kind),
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

    grid_before = [[float(x), float(y)] for x, y in inp.state.grid]
    grid_after = _apply_steps(grid_before, float(inp.params.dt), int(inp.params.steps))
    if inp.params.gauge_kind == "phase_rotate":
        grid_gauge_after = [_rotate(vec, float(inp.params.theta)) for vec in grid_after]
    else:
        grid_gauge_after = _rotate_local(grid_after, float(inp.params.theta), float(inp.params.theta_step))

    mags_after = _magnitudes(grid_after)
    mags_gauge = _magnitudes(grid_gauge_after)
    delta_mags = [abs(a - b) for a, b in zip(mags_after, mags_gauge)]

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "input_fingerprint": _sha256_json(inputs_payload),
        "params": dict(params_payload),
        "output": {
            "state_before": [[_q(x), _q(y)] for x, y in grid_before],
            "state_after": [[_q(x), _q(y)] for x, y in grid_after],
            "state_gauge_after": [[_q(x), _q(y)] for x, y in grid_gauge_after],
            "observables": {
                "magnitudes_after": [_q(x) for x in mags_after],
                "magnitudes_gauge_after": [_q(x) for x in mags_gauge],
                "sum_magnitude_after": _q(sum(mags_after)),
                "sum_magnitude_gauge_after": _q(sum(mags_gauge)),
                "delta_sum_magnitude": _q(sum(mags_gauge) - sum(mags_after)),
                "delta_magnitudes": [_q(x) for x in delta_mags],
            },
        },
        "diagnostics": {
            "gauge_transform_kind": str(inp.params.gauge_kind),
            "theta": _q(float(inp.params.theta)),
            "theta_step": _q(float(inp.params.theta_step)),
            "epsilon": _q(float(inp.params.epsilon)),
            "max_delta_magnitude": _q(max(delta_mags) if delta_mags else 0.0),
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


def dumps_toy_gauge_redundancy_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> ToyHInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        state = GaugeStateInput(grid=list(raw["state"]["grid"]))
        params_raw = raw.get("params", {})
        params = ToyHParams(
            dt=float(params_raw.get("dt", ToyHParams().dt)),
            steps=int(params_raw.get("steps", ToyHParams().steps)),
            theta=float(params_raw.get("theta", ToyHParams().theta)),
            theta_step=float(params_raw.get("theta_step", ToyHParams().theta_step)),
            epsilon=float(params_raw.get("epsilon", ToyHParams().epsilon)),
            gauge_kind=str(params_raw.get("gauge_kind", ToyHParams().gauge_kind)),
        )
        candidate_id = str(raw.get("candidate_id", "H1_phase_gauge"))
        return ToyHInput(state=state, params=params, candidate_id=candidate_id)

    if args.state_grid_json is None:
        raise SystemExit("Missing required arg: --state-grid-json")

    state = GaugeStateInput(grid=json.loads(args.state_grid_json))
    params = ToyHParams(
        dt=float(args.dt),
        steps=int(args.steps),
        theta=float(args.theta),
        theta_step=float(args.theta_step),
        epsilon=float(args.epsilon),
        gauge_kind=str(args.gauge_kind),
    )

    return ToyHInput(state=state, params=params, candidate_id=str(args.candidate_id))


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy gauge-redundancy report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--state-grid-json", help="Inline JSON list for state grid (list of [x,y])")
    p.add_argument("--candidate-id", choices=list(CANDIDATE_IDS), default="H1_phase_gauge")
    p.add_argument("--dt", type=float, default=ToyHParams().dt)
    p.add_argument("--steps", type=int, default=ToyHParams().steps)
    p.add_argument("--theta", type=float, default=ToyHParams().theta)
    p.add_argument("--theta-step", type=float, default=ToyHParams().theta_step)
    p.add_argument("--epsilon", type=float, default=ToyHParams().epsilon)
    p.add_argument("--gauge-kind", choices=list(GAUGE_KINDS), default=ToyHParams().gauge_kind)
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (write only when provided)",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_gauge_redundancy_report(inp)
    out_text = dumps_toy_gauge_redundancy_report(payload)

    if args.out:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
