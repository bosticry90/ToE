from __future__ import annotations

"""Toy regime switching front door (quarantine-safe).

Goal
- Deterministic report for a toy regime-switching scaffold.
- Bookkeeping only: consequences from structure, no physics claim.

Report schema (v1)
{
  "schema": "TOY/regime_switching_report/v1",
  "tool_version": "v1",
  "candidate_id": "D1_threshold_switch",
  "inputs": {...},
  "input_fingerprint": "...",
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


SCHEMA_ID = "TOY/regime_switching_report/v1"
TOOL_VERSION = "v1"
CANDIDATE_IDS = ("D1_threshold_switch",)
MU_DEF_IDS = ("mu_state",)


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
class RegimeSwitchingInput:
    mu_def_id: str
    mu_c: float
    initial_state: float
    steps: int
    dt: float
    candidate_id: str = "D1_threshold_switch"

    def __post_init__(self) -> None:
        if self.candidate_id not in CANDIDATE_IDS:
            raise ValueError(f"candidate_id must be one of {CANDIDATE_IDS}")
        if self.mu_def_id not in MU_DEF_IDS:
            raise ValueError(f"mu_def_id must be one of {MU_DEF_IDS}")
        if not isfinite(float(self.mu_c)):
            raise ValueError("mu_c must be finite")
        if not isfinite(float(self.initial_state)):
            raise ValueError("initial_state must be finite")
        if not isinstance(self.steps, int) or self.steps < 1:
            raise ValueError("steps must be a positive integer")
        if not isfinite(float(self.dt)):
            raise ValueError("dt must be finite")
        if float(self.dt) <= 0.0:
            raise ValueError("dt must be > 0")


def _mu_value(*, mu_def_id: str, state: float) -> float:
    if mu_def_id == "mu_state":
        return float(state)
    raise ValueError(f"Unsupported mu_def_id: {mu_def_id}")


def _step_state(*, state: float, dt: float) -> float:
    # Deterministic monotone update toward 1.0 (structure-only scaffold).
    return float(state) + float(dt) * (1.0 - float(state))


def build_toy_regime_switching_report(inp: RegimeSwitchingInput) -> Dict[str, Any]:
    inputs_payload = {
        "mu_def_id": str(inp.mu_def_id),
        "mu_c": _q(float(inp.mu_c)),
        "initial_state": _q(float(inp.initial_state)),
        "steps": int(inp.steps),
        "dt": _q(float(inp.dt)),
    }

    mu_sequence: list[float] = []
    regime_sequence: list[str] = []

    state = float(inp.initial_state)
    for step in range(int(inp.steps) + 1):
        mu = _mu_value(mu_def_id=inp.mu_def_id, state=state)
        mu_sequence.append(mu)
        regime_sequence.append("coherent" if mu > float(inp.mu_c) else "incoherent")
        if step < int(inp.steps):
            state = _step_state(state=state, dt=float(inp.dt))

    switch_events: list[int] = []
    for idx in range(1, len(regime_sequence)):
        if regime_sequence[idx] != regime_sequence[idx - 1]:
            switch_events.append(idx)

    summary = {
        "coherent_steps": int(sum(1 for r in regime_sequence if r == "coherent")),
        "incoherent_steps": int(sum(1 for r in regime_sequence if r == "incoherent")),
        "flip_count": int(len(switch_events)),
    }

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "input_fingerprint": _sha256_json(inputs_payload),
        "output": {
            "mu_sequence": [_q(x) for x in mu_sequence],
            "regime_sequence": list(regime_sequence),
            "switch_events": list(switch_events),
            "summary": summary,
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
    }
    payload["fingerprint"] = _sha256_json(fingerprint_payload)
    return payload


def dumps_toy_regime_switching_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> RegimeSwitchingInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        return RegimeSwitchingInput(
            mu_def_id=str(raw["mu_def_id"]),
            mu_c=float(raw["mu_c"]),
            initial_state=float(raw["initial_state"]),
            steps=int(raw["steps"]),
            dt=float(raw["dt"]),
            candidate_id=str(raw.get("candidate_id", "D1_threshold_switch")),
        )

    missing = [name for name in ["mu_def_id", "mu_c", "initial_state", "steps", "dt"] if getattr(args, name) is None]
    if missing:
        raise SystemExit(f"Missing required args: {', '.join(missing)}")

    return RegimeSwitchingInput(
        mu_def_id=str(args.mu_def_id),
        mu_c=float(args.mu_c),
        initial_state=float(args.initial_state),
        steps=int(args.steps),
        dt=float(args.dt),
        candidate_id=str(args.candidate_id),
    )


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy regime switching report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--mu-def-id", choices=list(MU_DEF_IDS))
    p.add_argument("--mu-c", type=float)
    p.add_argument("--initial-state", type=float)
    p.add_argument("--steps", type=int)
    p.add_argument("--dt", type=float)
    p.add_argument("--candidate-id", choices=list(CANDIDATE_IDS), default="D1_threshold_switch")
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (write only when provided)",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_regime_switching_report(inp)
    out_text = dumps_toy_regime_switching_report(payload)

    if args.out:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
