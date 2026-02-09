from __future__ import annotations

"""Toy coherence transport front door (quarantine-safe).

Goal
- Deterministic report for a toy coherence transport step.
- Bookkeeping only: consequences from structure, no physics claim.

Report schema (v1)
{
  "schema": "TOY/coherence_transport_report/v1",
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
from math import isfinite
from pathlib import Path
from typing import Any, Dict, Optional


SCHEMA_ID = "TOY/coherence_transport_report/v1"
CANDIDATE_IDS = ("B1_budget", "B2_transport_proxy")


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
class SubstrateInput:
    value: float

    def __post_init__(self) -> None:
        if not isfinite(float(self.value)):
            raise ValueError("SubstrateInput.value must be finite")


@dataclass(frozen=True)
class CoherenceInput:
    value: float
    grid: Optional[list[float]] = None

    def __post_init__(self) -> None:
        if not isfinite(float(self.value)):
            raise ValueError("CoherenceInput.value must be finite")
        if self.grid is not None:
            if not isinstance(self.grid, list):
                raise ValueError("CoherenceInput.grid must be a list of floats or None")
            if len(self.grid) < 2:
                raise ValueError("CoherenceInput.grid must have length >= 2")
            for val in self.grid:
                if not isfinite(float(val)):
                    raise ValueError("CoherenceInput.grid entries must be finite")


@dataclass(frozen=True)
class ToyBParams:
    dt: float = 0.05
    alpha: float = 0.0
    beta: float = 1.0
    source_bias: float = 0.0
    transport: float = 0.0

    def __post_init__(self) -> None:
        if not isfinite(float(self.dt)):
            raise ValueError("ToyBParams.dt must be finite")
        if not isfinite(float(self.alpha)):
            raise ValueError("ToyBParams.alpha must be finite")
        if not isfinite(float(self.beta)):
            raise ValueError("ToyBParams.beta must be finite")
        if not isfinite(float(self.source_bias)):
            raise ValueError("ToyBParams.source_bias must be finite")
        if not isfinite(float(self.transport)):
            raise ValueError("ToyBParams.transport must be finite")


@dataclass(frozen=True)
class ToyBInput:
    substrate: SubstrateInput
    coherence: CoherenceInput
    params: ToyBParams
    candidate_id: str = "B1_budget"

    def __post_init__(self) -> None:
        if self.candidate_id not in CANDIDATE_IDS:
            raise ValueError(f"candidate_id must be one of {CANDIDATE_IDS}")
        if self.candidate_id == "B1_budget" and self.coherence.grid is not None:
            raise ValueError("B1_budget expects coherence.grid to be None")
        if self.candidate_id == "B2_transport_proxy" and self.coherence.grid is None:
            raise ValueError("B2_transport_proxy requires coherence.grid to be provided")


def _coherence_step_budget(*, substrate: float, coherence: float, params: ToyBParams) -> dict:
    source = float(params.alpha) * float(substrate) + float(params.source_bias)
    decay = float(params.beta) * float(coherence)
    delta = float(params.dt) * (source - decay)
    coherence_next = float(coherence) + delta
    return {
        "source": source,
        "decay": decay,
        "delta": delta,
        "coherence_next": coherence_next,
    }


def _coherence_step_transport_proxy(
    *, substrate: float, coherence_grid: list[float], params: ToyBParams
) -> dict:
    source = float(params.alpha) * float(substrate) + float(params.source_bias)
    u = float(params.transport) * float(substrate)
    dt = float(params.dt)
    beta = float(params.beta)

    n = len(coherence_grid)
    transport_terms: list[float] = []
    next_grid: list[float] = []
    for i in range(n):
        prev_val = float(coherence_grid[i - 1])
        cur_val = float(coherence_grid[i])
        term = u * (prev_val - cur_val)
        transport_terms.append(term)
        next_grid.append(cur_val + dt * (term + source - beta * cur_val))

    return {
        "source": source,
        "transport_u": u,
        "transport_terms": transport_terms,
        "coherence_next_grid": next_grid,
    }


def build_toy_coherence_report(inp: ToyBInput) -> Dict[str, Any]:
    substrate_payload = {"value": _q(float(inp.substrate.value))}
    coherence_payload: Dict[str, Any] = {"value": _q(float(inp.coherence.value))}
    if inp.coherence.grid is not None:
        coherence_payload["grid"] = [_q(float(x)) for x in inp.coherence.grid]
    params_payload = {
        "dt": _q(float(inp.params.dt)),
        "alpha": _q(float(inp.params.alpha)),
        "beta": _q(float(inp.params.beta)),
        "source_bias": _q(float(inp.params.source_bias)),
        "transport": _q(float(inp.params.transport)),
    }

    inputs_payload = {
        "candidate_id": str(inp.candidate_id),
        "substrate": substrate_payload,
        "coherence": coherence_payload,
        "params": params_payload,
        "fingerprints": {
            "substrate": _sha256_json(substrate_payload),
            "coherence": _sha256_json(coherence_payload),
            "params": _sha256_json(params_payload),
        },
    }

    candidate_id = str(inp.candidate_id)
    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "candidate_id": candidate_id,
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

    if candidate_id == "B1_budget":
        step = _coherence_step_budget(
            substrate=float(inp.substrate.value),
            coherence=float(inp.coherence.value),
            params=inp.params,
        )
        payload["derived"] = {
            "source": _q(step["source"]),
            "decay": _q(step["decay"]),
            "delta": _q(step["delta"]),
        }
        payload["output"] = {
            "substrate": _q(float(inp.substrate.value)),
            "coherence_before": _q(float(inp.coherence.value)),
            "coherence_after": _q(step["coherence_next"]),
        }
    else:
        coherence_grid = [float(x) for x in (inp.coherence.grid or [])]
        step = _coherence_step_transport_proxy(
            substrate=float(inp.substrate.value),
            coherence_grid=coherence_grid,
            params=inp.params,
        )
        next_grid = [float(x) for x in step["coherence_next_grid"]]
        mean_before = sum(coherence_grid) / float(len(coherence_grid))
        mean_after = sum(next_grid) / float(len(next_grid))
        max_before = max(abs(x) for x in coherence_grid)
        max_after = max(abs(x) for x in next_grid)
        transport_l1 = sum(abs(x) for x in step["transport_terms"])

        payload["derived"] = {
            "source": _q(step["source"]),
            "transport_u": _q(step["transport_u"]),
            "transport_l1": _q(transport_l1),
        }
        payload["output"] = {
            "substrate": _q(float(inp.substrate.value)),
            "coherence_before": _q(mean_before),
            "coherence_after": _q(mean_after),
            "coherence_grid_before": [_q(x) for x in coherence_grid],
            "coherence_grid_after": [_q(x) for x in next_grid],
            "coherence_max_abs_before": _q(max_before),
            "coherence_max_abs_after": _q(max_after),
        }

    payload["fingerprint"] = _sha256_json(payload)
    return payload


def dumps_toy_coherence_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace) -> ToyBInput:
    if args.input_json:
        raw = _load_input_json(args.input_json)
        candidate_id = str(raw.get("candidate_id", "B1_budget"))
        substrate = SubstrateInput(value=float(raw["substrate"]["value"]))
        coherence = CoherenceInput(
            value=float(raw["coherence"]["value"]),
            grid=raw["coherence"].get("grid"),
        )
        params_raw = raw.get("params", {})
        params = ToyBParams(
            dt=float(params_raw.get("dt", ToyBParams().dt)),
            alpha=float(params_raw.get("alpha", ToyBParams().alpha)),
            beta=float(params_raw.get("beta", ToyBParams().beta)),
            source_bias=float(params_raw.get("source_bias", ToyBParams().source_bias)),
            transport=float(params_raw.get("transport", ToyBParams().transport)),
        )
        return ToyBInput(substrate=substrate, coherence=coherence, params=params, candidate_id=candidate_id)

    missing = [name for name in ["substrate", "coherence"] if getattr(args, name) is None]
    if missing:
        raise SystemExit(f"Missing required args: {', '.join(missing)}")

    coherence_grid = None
    if args.coherence_grid_json:
        coherence_grid = json.loads(args.coherence_grid_json)

    params = ToyBParams(
        dt=float(args.dt),
        alpha=float(args.alpha),
        beta=float(args.beta),
        source_bias=float(args.source_bias),
        transport=float(args.transport),
    )

    return ToyBInput(
        substrate=SubstrateInput(value=float(args.substrate)),
        coherence=CoherenceInput(value=float(args.coherence), grid=coherence_grid),
        params=params,
        candidate_id=str(args.candidate_id),
    )


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate toy coherence transport report JSON (schema v1).")
    p.add_argument("--input-json", help="JSON file path (or raw JSON string) with input fields")
    p.add_argument("--substrate", type=float, help="Substrate scalar value")
    p.add_argument("--coherence", type=float, help="Coherence scalar value")
    p.add_argument("--coherence-grid-json", help="Inline JSON list for coherence grid (B2 only)")
    p.add_argument("--candidate-id", choices=list(CANDIDATE_IDS), default="B1_budget")
    p.add_argument("--dt", type=float, default=ToyBParams().dt)
    p.add_argument("--alpha", type=float, default=ToyBParams().alpha)
    p.add_argument("--beta", type=float, default=ToyBParams().beta)
    p.add_argument("--source-bias", type=float, default=ToyBParams().source_bias)
    p.add_argument("--transport", type=float, default=ToyBParams().transport)
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (write only when provided)",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args)
    payload = build_toy_coherence_report(inp)
    out_text = dumps_toy_coherence_report(payload)

    if args.out:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
