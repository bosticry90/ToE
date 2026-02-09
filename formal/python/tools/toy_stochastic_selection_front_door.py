from __future__ import annotations

"""Toy stochastic-selection front door (quarantine-safe).

Goal
- Deterministic report for a toy stochastic selection step.
- Bookkeeping only: consequences from structure, no physics claim.

Report schema (v1)
{
  "schema": "TOY/stochastic_selection_report/v1",
  "schema_version": "v1",
  "tool_version": "v1",
  "candidate_id": "F1_noise_plus_pullback",
  "inputs": {...},
  "input_fingerprint": "...",
  "params": {...},
  "output": {...},
  "diagnostics": {...},
  "admissibility": {...},
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


SCHEMA_ID = "TOY/stochastic_selection_report/v1"
SCHEMA_VERSION = "v1"
TOOL_VERSION = "v1"
CANDIDATE_IDS = ("F1_noise_plus_pullback",)
DEFAULT_PULLBACK_STRENGTH = 0.5
DEFAULT_TARGET = 0.0
DEFAULT_SIGMA = 0.3
DEFAULT_ABS_BOUND = 1.0


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


def _noise_value(seed: int, step: int) -> float:
    text = f"{int(seed)}:{int(step)}"
    digest = hashlib.sha256(text.encode("utf-8")).digest()
    u = int.from_bytes(digest[:8], "big") / float(2**64)
    return 2.0 * u - 1.0


@dataclass(frozen=True)
class StochasticSelectionInput:
    seed: int
    steps: int
    dt: float
    initial_state: float
    pullback_strength: float = DEFAULT_PULLBACK_STRENGTH
    target: float = DEFAULT_TARGET
    sigma: float = DEFAULT_SIGMA
    abs_bound: float = DEFAULT_ABS_BOUND
    candidate_id: str = "F1_noise_plus_pullback"

    def __post_init__(self) -> None:
        if self.candidate_id not in CANDIDATE_IDS:
            raise ValueError(f"candidate_id must be one of {CANDIDATE_IDS}")
        if not isinstance(self.seed, int):
            raise ValueError("seed must be an integer")
        if not isinstance(self.steps, int) or self.steps < 1:
            raise ValueError("steps must be a positive integer")
        if not isfinite(float(self.dt)):
            raise ValueError("dt must be finite")
        if float(self.dt) <= 0.0:
            raise ValueError("dt must be > 0")
        if not isfinite(float(self.initial_state)):
            raise ValueError("initial_state must be finite")
        if not isfinite(float(self.pullback_strength)):
            raise ValueError("pullback_strength must be finite")
        if not isfinite(float(self.target)):
            raise ValueError("target must be finite")
        if not isfinite(float(self.sigma)):
            raise ValueError("sigma must be finite")
        if not isfinite(float(self.abs_bound)):
            raise ValueError("abs_bound must be finite")
        if float(self.abs_bound) <= 0.0:
            raise ValueError("abs_bound must be > 0")


def _step_state(
    *, state: float, dt: float, pullback_strength: float, target: float, sigma: float, noise: float
) -> float:
    pullback = float(dt) * float(pullback_strength) * (float(target) - float(state))
    return float(state) + pullback + float(sigma) * float(noise)


def build_toy_stochastic_selection_report(inp: StochasticSelectionInput) -> Dict[str, Any]:
    inputs_payload = {
        "seed": int(inp.seed),
        "steps": int(inp.steps),
        "dt": _q(float(inp.dt)),
        "initial_state": _q(float(inp.initial_state)),
        "initial_state_fingerprint": _sha256_json({"initial_state": _q(float(inp.initial_state))}),
    }

    params_payload = {
        "pullback_strength": _q(float(inp.pullback_strength)),
        "target": _q(float(inp.target)),
        "sigma": _q(float(inp.sigma)),
        "abs_bound": _q(float(inp.abs_bound)),
    }

    bound = float(inp.abs_bound)
    state = float(inp.initial_state)
    state_sequence = [state]
    noise_sequence: list[float] = []
    admissible_sequence: list[bool] = []
    violations: list[dict[str, Any]] = []

    def _record_state(step_idx: int, value: float) -> None:
        ok = abs(float(value)) <= bound
        admissible_sequence.append(bool(ok))
        if not ok:
            violations.append({"step": int(step_idx), "value": _q(float(value))})

    _record_state(0, state)
    for step in range(int(inp.steps)):
        noise = _noise_value(int(inp.seed), int(step))
        noise_sequence.append(noise)
        state = _step_state(
            state=state,
            dt=float(inp.dt),
            pullback_strength=float(inp.pullback_strength),
            target=float(inp.target),
            sigma=float(inp.sigma),
            noise=noise,
        )
        state_sequence.append(state)
        _record_state(step + 1, state)

    admissible = len(violations) == 0
    reasons = [] if admissible else ["BOUND_EXCEEDED"]
    first_violation_step = violations[0]["step"] if violations else None

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "schema_version": SCHEMA_VERSION,
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "input_fingerprint": _sha256_json(inputs_payload),
        "params": params_payload,
        "output": {
            "state_sequence": [_q(x) for x in state_sequence],
            "noise_sequence": [_q(x) for x in noise_sequence],
            "admissible_sequence": list(admissible_sequence),
        },
        "diagnostics": {
            "first_violation_step": first_violation_step,
            "reason_code": "OK" if admissible else "BOUND_EXCEEDED",
            "violation_count": int(len(violations)),
        },
        "admissibility": {
            "admissible": bool(admissible),
            "reasons": list(reasons),
            "violations": list(violations),
            "bound_abs": _q(bound),
        },
        "scope_limits": [
            "structure_only; no physics claim",
            "bounded evidence only; consequence engine",
        ],
    }

    fingerprint_payload = {
        "schema": SCHEMA_ID,
        "schema_version": SCHEMA_VERSION,
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "params": params_payload,
    }
    payload["fingerprint"] = _sha256_json(fingerprint_payload)
    return payload


def dumps_toy_stochastic_selection_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> StochasticSelectionInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        params = raw.get("params", {})
        return StochasticSelectionInput(
            seed=int(raw["seed"]),
            steps=int(raw["steps"]),
            dt=float(raw["dt"]),
            initial_state=float(raw["initial_state"]),
            pullback_strength=float(params.get("pullback_strength", DEFAULT_PULLBACK_STRENGTH)),
            target=float(params.get("target", DEFAULT_TARGET)),
            sigma=float(params.get("sigma", DEFAULT_SIGMA)),
            abs_bound=float(params.get("abs_bound", DEFAULT_ABS_BOUND)),
            candidate_id=str(raw.get("candidate_id", "F1_noise_plus_pullback")),
        )

    missing = [name for name in ["seed", "steps", "dt", "initial_state"] if getattr(args, name) is None]
    if missing:
        raise SystemExit(f"Missing required args: {', '.join(missing)}")

    return StochasticSelectionInput(
        seed=int(args.seed),
        steps=int(args.steps),
        dt=float(args.dt),
        initial_state=float(args.initial_state),
        pullback_strength=float(args.pullback_strength),
        target=float(args.target),
        sigma=float(args.sigma),
        abs_bound=float(args.abs_bound),
        candidate_id=str(args.candidate_id),
    )


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy stochastic-selection report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--seed", type=int)
    p.add_argument("--steps", type=int)
    p.add_argument("--dt", type=float)
    p.add_argument("--initial-state", type=float)
    p.add_argument("--pullback-strength", type=float, default=DEFAULT_PULLBACK_STRENGTH)
    p.add_argument("--target", type=float, default=DEFAULT_TARGET)
    p.add_argument("--sigma", type=float, default=DEFAULT_SIGMA)
    p.add_argument("--abs-bound", type=float, default=DEFAULT_ABS_BOUND)
    p.add_argument("--candidate-id", choices=list(CANDIDATE_IDS), default="F1_noise_plus_pullback")
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (write only when provided)",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_stochastic_selection_report(inp)
    out_text = dumps_toy_stochastic_selection_report(payload)

    if args.out:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
