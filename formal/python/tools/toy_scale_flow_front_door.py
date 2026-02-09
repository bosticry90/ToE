from __future__ import annotations

"""Toy scale-flow front door (quarantine-safe).

Goal
- Deterministic report for a toy scale-flow step.
- Bookkeeping only: consequences from structure, no physics claim.

Report schema (v1)
{
  "schema": "TOY/scale_flow_report/v1",
  "tool_version": "v1",
  "candidate_id": "E1_euler_linear",
  "inputs": {...},
  "input_fingerprint": "...",
  "params": {...},
  "output": {...},
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
from math import isfinite, sqrt
from pathlib import Path
from typing import Any, Dict, Optional


SCHEMA_ID = "TOY/scale_flow_report/v1"
TOOL_VERSION = "v1"
CANDIDATE_IDS = ("E1_euler_linear",)
BETA_KINDS = ("linear_diag",)
ADMISSIBILITY_BOUND = 2.0


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
class ScaleFlowInput:
    couplings_init: list[float]
    delta: float
    n_steps: int
    scale_init: float = 0.0
    candidate_id: str = "E1_euler_linear"
    beta_kind: str = "linear_diag"
    beta_diag: Optional[list[float]] = None

    def __post_init__(self) -> None:
        if self.candidate_id not in CANDIDATE_IDS:
            raise ValueError(f"candidate_id must be one of {CANDIDATE_IDS}")
        if self.beta_kind not in BETA_KINDS:
            raise ValueError(f"beta_kind must be one of {BETA_KINDS}")
        if not isinstance(self.couplings_init, list) or len(self.couplings_init) < 1:
            raise ValueError("couplings_init must be a non-empty list")
        for val in self.couplings_init:
            if not isfinite(float(val)):
                raise ValueError("couplings_init entries must be finite")
        if not isfinite(float(self.delta)):
            raise ValueError("delta must be finite")
        if float(self.delta) <= 0.0:
            raise ValueError("delta must be > 0")
        if not isinstance(self.n_steps, int) or self.n_steps < 1:
            raise ValueError("n_steps must be a positive integer")
        if not isfinite(float(self.scale_init)):
            raise ValueError("scale_init must be finite")
        if self.beta_kind == "linear_diag":
            if self.beta_diag is None:
                raise ValueError("beta_diag is required for beta_kind='linear_diag'")
            if len(self.beta_diag) != len(self.couplings_init):
                raise ValueError("beta_diag length must match couplings_init length")
            for val in self.beta_diag:
                if not isfinite(float(val)):
                    raise ValueError("beta_diag entries must be finite")


def _beta_linear_diag(g: list[float], diag: list[float]) -> list[float]:
    return [float(d) * float(x) for x, d in zip(g, diag)]


def _step_euler(g: list[float], delta: float, diag: list[float]) -> list[float]:
    beta = _beta_linear_diag(g, diag)
    return [float(x) + float(delta) * float(b) for x, b in zip(g, beta)]


def _l2_norm(g: list[float]) -> float:
    return sqrt(sum(float(x) * float(x) for x in g))


def build_toy_scale_flow_report(inp: ScaleFlowInput) -> Dict[str, Any]:
    couplings_init = [float(x) for x in inp.couplings_init]
    beta_diag = [float(x) for x in (inp.beta_diag or [])]

    inputs_payload = {
        "couplings_init": [_q(x) for x in couplings_init],
        "delta": _q(float(inp.delta)),
        "n_steps": int(inp.n_steps),
        "scale_init": _q(float(inp.scale_init)),
    }

    params_payload = {
        "beta_kind": str(inp.beta_kind),
        "beta_diag": [_q(x) for x in beta_diag],
    }

    trajectory: list[list[float]] = [list(couplings_init)]
    for _ in range(int(inp.n_steps)):
        next_g = _step_euler(trajectory[-1], float(inp.delta), beta_diag)
        trajectory.append(next_g)

    norms = [_l2_norm(g) for g in trajectory]
    monotone_nonincreasing = all(norms[i + 1] <= norms[i] + 1e-12 for i in range(len(norms) - 1))
    monotone_nondecreasing = all(norms[i + 1] >= norms[i] - 1e-12 for i in range(len(norms) - 1))

    violations: list[dict] = []
    bound = float(ADMISSIBILITY_BOUND)
    for step_idx, g in enumerate(trajectory):
        for i, val in enumerate(g):
            if abs(float(val)) > bound:
                violations.append({"step": int(step_idx), "index": int(i), "value": _q(float(val))})

    admissible = len(violations) == 0
    reasons = [] if admissible else ["BOUND_EXCEEDED"]

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "input_fingerprint": _sha256_json(inputs_payload),
        "params": params_payload,
        "output": {
            "trajectory": {
                "couplings": [[_q(x) for x in g] for g in trajectory],
            },
            "diagnostics": {
                "norms": [_q(x) for x in norms],
                "monotone_flags": {
                    "l2_nonincreasing": bool(monotone_nonincreasing),
                    "l2_nondecreasing": bool(monotone_nondecreasing),
                },
            },
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
        "tool_version": TOOL_VERSION,
        "candidate_id": str(inp.candidate_id),
        "inputs": inputs_payload,
        "params": params_payload,
    }
    payload["fingerprint"] = _sha256_json(fingerprint_payload)
    return payload


def dumps_toy_scale_flow_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> ScaleFlowInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        return ScaleFlowInput(
            couplings_init=list(raw["couplings_init"]),
            delta=float(raw["delta"]),
            n_steps=int(raw["n_steps"]),
            scale_init=float(raw.get("scale_init", 0.0)),
            candidate_id=str(raw.get("candidate_id", "E1_euler_linear")),
            beta_kind=str(raw.get("beta_kind", "linear_diag")),
            beta_diag=list(raw.get("beta_diag", [])),
        )

    missing = [name for name in ["couplings_init", "delta", "n_steps"] if getattr(args, name) is None]
    if missing:
        raise SystemExit(f"Missing required args: {', '.join(missing)}")

    couplings_init = json.loads(args.couplings_init)
    beta_diag = json.loads(args.beta_diag)

    return ScaleFlowInput(
        couplings_init=list(couplings_init),
        delta=float(args.delta),
        n_steps=int(args.n_steps),
        scale_init=float(args.scale_init),
        candidate_id=str(args.candidate_id),
        beta_kind=str(args.beta_kind),
        beta_diag=list(beta_diag),
    )


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy scale-flow report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--couplings-init", help="Inline JSON list for couplings")
    p.add_argument("--delta", type=float)
    p.add_argument("--n-steps", type=int)
    p.add_argument("--scale-init", type=float, default=0.0)
    p.add_argument("--candidate-id", choices=list(CANDIDATE_IDS), default="E1_euler_linear")
    p.add_argument("--beta-kind", choices=list(BETA_KINDS), default="linear_diag")
    p.add_argument("--beta-diag", help="Inline JSON list for beta diagonal")
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (write only when provided)",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_scale_flow_report(inp)
    out_text = dumps_toy_scale_flow_report(payload)

    if args.out:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
