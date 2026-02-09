from __future__ import annotations

"""Toy viability gradient-step front door (quarantine-safe).

Goal
- Deterministic report for a parameterized toy viability step.
- Bookkeeping only: consequences from structure, no physics claim.

Report schema (v1)
{
  "schema": "TOY/viability_gradient_step_report/v1",
  "inputs": {...},
  "input_fingerprint": "...",
  "derived": {...},
  "output": {...},
  "determinism": {...},
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
from dataclasses import asdict
from dataclasses import dataclass
import hashlib
import json
from math import isfinite
from pathlib import Path
from typing import Any, Dict, Optional

import numpy as np

SCHEMA_ID = "TOY/viability_gradient_step_report/v1"


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
class SubstrateToyInput:
    """Typed input for the toy viability gradient-step report."""

    state_dim: int
    state_seed: int
    eta: float
    grad_kind: str
    grad_params: Optional[Dict[str, Any]] = None

    def __post_init__(self) -> None:
        if not isinstance(self.state_dim, int) or self.state_dim <= 0:
            raise ValueError("state_dim must be a positive integer")
        if not isinstance(self.state_seed, int):
            raise ValueError("state_seed must be an integer")
        if not isfinite(float(self.eta)):
            raise ValueError("eta must be a finite float")
        if self.grad_kind not in {"identity", "linear_diag"}:
            raise ValueError("grad_kind must be 'identity' or 'linear_diag'")
        if self.grad_params is not None and not isinstance(self.grad_params, dict):
            raise ValueError("grad_params must be a dict or None")

        if self.grad_kind == "identity":
            if self.grad_params:
                raise ValueError("grad_params must be empty for grad_kind='identity'")
        else:
            params = self.grad_params or {}
            allowed = {"diag", "diag_seed"}
            extra = set(params.keys()) - allowed
            if extra:
                raise ValueError(f"Unexpected grad_params keys: {sorted(extra)}")
            if "diag" in params and "diag_seed" in params:
                raise ValueError("Provide either 'diag' or 'diag_seed', not both")


def _state_from_seed(*, state_dim: int, state_seed: int) -> np.ndarray:
    rng = np.random.default_rng(int(state_seed))
    state = rng.standard_normal(int(state_dim))
    return np.asarray(state, dtype=float)


def _resolve_grad_params(
    *,
    state_dim: int,
    state_seed: int,
    grad_kind: str,
    grad_params: Optional[Dict[str, Any]],
) -> tuple[Dict[str, Any], Optional[np.ndarray]]:
    if grad_kind == "identity":
        return {"kind": "identity"}, None

    params = grad_params or {}
    if "diag" in params:
        diag_list = list(params["diag"])
        if len(diag_list) != int(state_dim):
            raise ValueError("grad_params.diag length must match state_dim")
        diag = np.asarray(diag_list, dtype=float)
        resolved = {
            "kind": "linear_diag",
            "diag_source": "explicit",
            "diag": [_q(x) for x in diag.tolist()],
        }
        return resolved, diag

    diag_seed = int(params.get("diag_seed", int(state_seed) + 1))
    rng = np.random.default_rng(diag_seed)
    diag = rng.standard_normal(int(state_dim))
    diag = np.asarray(diag, dtype=float)
    resolved = {
        "kind": "linear_diag",
        "diag_source": "seed",
        "diag_seed": diag_seed,
        "diag": [_q(x) for x in diag.tolist()],
    }
    return resolved, diag


def _grad_value(*, state: np.ndarray, grad_kind: str, diag: Optional[np.ndarray]) -> np.ndarray:
    if grad_kind == "identity":
        return np.asarray(state, dtype=float)
    if diag is None:
        raise ValueError("diag is required for grad_kind='linear_diag'")
    return np.asarray(diag, dtype=float) * np.asarray(state, dtype=float)


def apply_viability_step(
    *,
    state: np.ndarray,
    eta: float,
    grad_kind: str,
    diag: Optional[np.ndarray],
) -> np.ndarray:
    grad = _grad_value(state=state, grad_kind=grad_kind, diag=diag)
    return np.asarray(state, dtype=float) - float(eta) * np.asarray(grad, dtype=float)


def apply_viability_step_n(
    *,
    state: np.ndarray,
    eta: float,
    grad_kind: str,
    diag: Optional[np.ndarray],
    steps: int,
) -> np.ndarray:
    if int(steps) <= 0:
        raise ValueError("steps must be a positive integer")
    step_eta = float(eta) / float(steps)
    current = np.asarray(state, dtype=float)
    for _ in range(int(steps)):
        current = apply_viability_step(state=current, eta=step_eta, grad_kind=grad_kind, diag=diag)
    return current


def build_toy_viability_report(inp: SubstrateToyInput) -> Dict[str, Any]:
    inputs = asdict(inp)
    input_fingerprint = _sha256_json(inputs)

    state = _state_from_seed(state_dim=inp.state_dim, state_seed=inp.state_seed)
    grad_resolved, diag = _resolve_grad_params(
        state_dim=inp.state_dim,
        state_seed=inp.state_seed,
        grad_kind=inp.grad_kind,
        grad_params=inp.grad_params,
    )

    grad = _grad_value(state=state, grad_kind=inp.grad_kind, diag=diag)
    state_next = apply_viability_step(state=state, eta=inp.eta, grad_kind=inp.grad_kind, diag=diag)

    norm_before = float(np.linalg.norm(state))
    norm_after = float(np.linalg.norm(state_next))
    grad_norm = float(np.linalg.norm(grad))

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "inputs": inputs,
        "input_fingerprint": input_fingerprint,
        "derived": {
            "grad_params_resolved": grad_resolved,
        },
        "output": {
            "state_before": [_q(x) for x in state.tolist()],
            "state_after": [_q(x) for x in state_next.tolist()],
            "norm_before": _q(norm_before),
            "norm_after": _q(norm_after),
            "grad_norm": _q(grad_norm),
        },
        "determinism": {
            "rng": "numpy.default_rng",
            "state_seed": int(inp.state_seed),
            "dtype": "float64",
            "json": "sort_keys,separators=(',',':'),ensure_ascii=True",
        },
    }

    payload["fingerprint"] = _sha256_json(payload)
    return payload


def dumps_toy_viability_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> SubstrateToyInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        return SubstrateToyInput(
            state_dim=int(raw["state_dim"]),
            state_seed=int(raw["state_seed"]),
            eta=float(raw["eta"]),
            grad_kind=str(raw["grad_kind"]),
            grad_params=raw.get("grad_params"),
        )

    missing = [name for name in ["state_dim", "state_seed", "eta", "grad_kind"] if getattr(args, name) is None]
    if missing:
        raise SystemExit(f"Missing required args: {', '.join(missing)}")

    grad_params = None
    if args.grad_params_json:
        grad_params = json.loads(args.grad_params_json)

    return SubstrateToyInput(
        state_dim=int(args.state_dim),
        state_seed=int(args.state_seed),
        eta=float(args.eta),
        grad_kind=str(args.grad_kind),
        grad_params=grad_params,
    )


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy viability gradient-step report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--state-dim", type=int)
    p.add_argument("--state-seed", type=int)
    p.add_argument("--eta", type=float)
    p.add_argument("--grad-kind", choices=["identity", "linear_diag"])
    p.add_argument(
        "--grad-params-json",
        help='Inline JSON string for grad_params (e.g., \'{"diag_seed": 5}\')',
    )
    p.add_argument(
        "--out",
        default="formal/output/toy_viability_gradient_step_report.json",
        help="Repo-relative output JSON path",
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the output file")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_viability_report(inp)
    out_text = dumps_toy_viability_report(payload)

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
