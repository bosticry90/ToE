from __future__ import annotations

"""Toy metric-closure front door (quarantine-safe).

Goal
- Deterministic report for a toy metric-like summary.
- Bookkeeping only: consequences from structure, no physics claim.
Admissibility is evaluated by bounded tests (see TOY_LAW_LEDGER evidence nodes).

Report schema (v1)
{
  "schema": "TOY/metric_closure_report/v1",
  "candidate_id": "C1_metric_signature",
  "inputs": {...},
  "input_fingerprint": "...",
  "params": {...},
  "derived": {...},
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
from math import isfinite, sqrt
from pathlib import Path
from typing import Any, Dict, Optional


SCHEMA_ID = "TOY/metric_closure_report/v1"
CANDIDATE_IDS = ("C1_signature", "C2_curvature_proxy")


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
class MetricStateInput:
    grid: list[float]

    def __post_init__(self) -> None:
        if not isinstance(self.grid, list):
            raise ValueError("MetricStateInput.grid must be a list of floats")
        if len(self.grid) < 2:
            raise ValueError("MetricStateInput.grid must have length >= 2")
        for val in self.grid:
            if not isfinite(float(val)):
                raise ValueError("MetricStateInput.grid entries must be finite")


@dataclass(frozen=True)
class ToyCParams:
    scale: float = 1.0
    bias: float = 0.0
    max_coupling: float = 0.9
    min_floor: float = 0.0
    max_proxy: float = 2.0

    def __post_init__(self) -> None:
        if not isfinite(float(self.scale)):
            raise ValueError("ToyCParams.scale must be finite")
        if not isfinite(float(self.bias)):
            raise ValueError("ToyCParams.bias must be finite")
        if not isfinite(float(self.max_coupling)):
            raise ValueError("ToyCParams.max_coupling must be finite")
        if not isfinite(float(self.min_floor)):
            raise ValueError("ToyCParams.min_floor must be finite")
        if not isfinite(float(self.max_proxy)):
            raise ValueError("ToyCParams.max_proxy must be finite")


@dataclass(frozen=True)
class ToyCInput:
    state: MetricStateInput
    params: ToyCParams
    candidate_id: str = "C1_signature"

    def __post_init__(self) -> None:
        if self.candidate_id not in CANDIDATE_IDS:
            raise ValueError(f"candidate_id must be one of {CANDIDATE_IDS}")
        if self.candidate_id == "C2_curvature_proxy" and len(self.state.grid) < 3:
            raise ValueError("C2_curvature_proxy requires state.grid length >= 3")


def _metric_summary(*, grid: list[float], params: ToyCParams) -> dict:
    first = abs(float(grid[0])) + float(params.bias)
    last = abs(float(grid[-1])) + float(params.bias)
    mean = sum(float(x) for x in grid) / float(len(grid))

    g_tt = -first
    g_tx = float(params.scale) * mean
    g_xx = last

    det = g_tt * g_xx - g_tx * g_tx
    denom = abs(g_tt * g_xx)
    coupling_ratio = float("inf") if denom == 0.0 else abs(g_tx) / sqrt(denom)

    signature_ok = (g_tt < 0.0) and (g_xx > 0.0) and (coupling_ratio <= float(params.max_coupling))

    return {
        "g_tt": g_tt,
        "g_tx": g_tx,
        "g_xx": g_xx,
        "det": det,
        "coupling_ratio": coupling_ratio,
        "signature_ok": signature_ok,
    }


def _curvature_proxy(*, grid: list[float], params: ToyCParams) -> dict:
    d2: list[float] = []
    for i in range(1, len(grid) - 1):
        d2.append(float(grid[i + 1]) - 2.0 * float(grid[i]) + float(grid[i - 1]))

    mean_d2 = sum(d2) / float(len(d2))
    proxy_mean = float(params.scale) * mean_d2
    proxy_abs_max = max(abs(x) for x in d2)
    min_value = min(float(x) for x in grid) + float(params.bias)

    return {
        "proxy_mean": proxy_mean,
        "proxy_abs_max": proxy_abs_max,
        "min_value": min_value,
    }


def build_toy_metric_closure_report(inp: ToyCInput) -> Dict[str, Any]:
    state_payload = {"grid": [_q(float(x)) for x in inp.state.grid]}
    params_payload = {
        "scale": _q(float(inp.params.scale)),
        "bias": _q(float(inp.params.bias)),
        "max_coupling": _q(float(inp.params.max_coupling)),
        "min_floor": _q(float(inp.params.min_floor)),
        "max_proxy": _q(float(inp.params.max_proxy)),
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

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "input_fingerprint": _sha256_json(inputs_payload),
        "params": dict(params_payload),
        "derived": {},
        "output": {},
        "scope_limits": [
            "structure_only; no physics claim",
            "bounded evidence only; consequence engine",
        ],
    }

    if inp.candidate_id == "C1_signature":
        summary = _metric_summary(grid=list(inp.state.grid), params=inp.params)
        payload["derived"] = {
            "det": _q(summary["det"]),
            "coupling_ratio": _q(summary["coupling_ratio"]),
            "signature_ok": bool(summary["signature_ok"]),
        }
        payload["output"] = {
            "proxy_kind": "signature",
            "g_tt": _q(summary["g_tt"]),
            "g_tx": _q(summary["g_tx"]),
            "g_xx": _q(summary["g_xx"]),
            "grid": [_q(float(x)) for x in inp.state.grid],
        }
    else:
        summary = _curvature_proxy(grid=list(inp.state.grid), params=inp.params)
        payload["derived"] = {
            "proxy_mean": _q(summary["proxy_mean"]),
            "proxy_abs_max": _q(summary["proxy_abs_max"]),
            "min_value": _q(summary["min_value"]),
        }
        payload["output"] = {
            "proxy_kind": "curvature_proxy",
            "proxy_mean": _q(summary["proxy_mean"]),
            "proxy_abs_max": _q(summary["proxy_abs_max"]),
            "min_value": _q(summary["min_value"]),
            "grid": [_q(float(x)) for x in inp.state.grid],
        }

    payload["fingerprint"] = _sha256_json(payload)
    return payload


def dumps_toy_metric_closure_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> ToyCInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        state = MetricStateInput(grid=list(raw["state"]["grid"]))
        params_raw = raw.get("params", {})
        params = ToyCParams(
            scale=float(params_raw.get("scale", ToyCParams().scale)),
            bias=float(params_raw.get("bias", ToyCParams().bias)),
            max_coupling=float(params_raw.get("max_coupling", ToyCParams().max_coupling)),
            min_floor=float(params_raw.get("min_floor", ToyCParams().min_floor)),
            max_proxy=float(params_raw.get("max_proxy", ToyCParams().max_proxy)),
        )
        candidate_id = str(raw.get("candidate_id", "C1_signature"))
        return ToyCInput(state=state, params=params, candidate_id=candidate_id)

    if args.state_grid_json is None:
        raise SystemExit("Missing required arg: --state-grid-json")

    state = MetricStateInput(grid=json.loads(args.state_grid_json))
    params = ToyCParams(
        scale=float(args.scale),
        bias=float(args.bias),
        max_coupling=float(args.max_coupling),
        min_floor=float(args.min_floor),
        max_proxy=float(args.max_proxy),
    )

    return ToyCInput(state=state, params=params, candidate_id=str(args.candidate_id))


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy metric-closure report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--state-grid-json", help="Inline JSON list for substrate grid (length >= 2)")
    p.add_argument("--candidate-id", choices=list(CANDIDATE_IDS), default="C1_signature")
    p.add_argument("--scale", type=float, default=ToyCParams().scale)
    p.add_argument("--bias", type=float, default=ToyCParams().bias)
    p.add_argument("--max-coupling", type=float, default=ToyCParams().max_coupling)
    p.add_argument("--min-floor", type=float, default=ToyCParams().min_floor)
    p.add_argument("--max-proxy", type=float, default=ToyCParams().max_proxy)
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (write only when provided)",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_metric_closure_report(inp)
    out_text = dumps_toy_metric_closure_report(payload)

    if args.out:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
