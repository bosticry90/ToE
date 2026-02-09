from __future__ import annotations

"""Physics Target Contract: NLSE-like v1 front door (quarantine-safe).

Goal
- Deterministic report for a pinned NLSE-like PDE surface.
- Provides a single executable entry point for physics instantiation v1.
- Bookkeeping only; no epistemic status upgrade.

Report schema (v1)
{
  "schema": "PTC/NLSE_v1_report/v1",
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
from dataclasses import dataclass
import hashlib
import json
from math import isfinite
from pathlib import Path
from typing import Any, Dict, Optional

import numpy as np

SCHEMA_ID = "PTC/NLSE_v1_report/v1"
HOOKS_SCHEMA_ID = "PTC/NLSE_v1_hooks/v1"
MANIFEST_SCHEMA = "PTC/NLSE_v1_manifest/v1"


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
    return float(f"{float(x):.{int(sig)}g}")


def _default_manifest_path(repo_root: Path) -> Path:
    return repo_root / "formal" / "quarantine" / "physics_target" / "PTC_NLSE_V1_MANIFEST.json"


def _kgrid(L: float, N: int) -> np.ndarray:
    dx = float(L) / int(N)
    return 2.0 * np.pi * np.fft.fftfreq(int(N), d=dx)


def _periodic_dx(psi: np.ndarray, k: np.ndarray) -> np.ndarray:
    phat = np.fft.fft(psi)
    return np.fft.ifft(1j * k * phat)


def _energy(psi: np.ndarray, k: np.ndarray, *, g: float, Vx: np.ndarray, dx: float) -> float:
    grad = _periodic_dx(psi, k)
    return float(
        np.sum(0.5 * np.abs(grad) ** 2 + Vx * np.abs(psi) ** 2 + 0.5 * g * np.abs(psi) ** 4) * dx
    )


def _norm(psi: np.ndarray, dx: float) -> float:
    return float(np.sum(np.abs(psi) ** 2) * dx)


def _l2_residual(a: np.ndarray, b: np.ndarray, dx: float) -> float:
    return float(np.sqrt(np.sum(np.abs(a - b) ** 2) * dx))


def _sech(x: np.ndarray) -> np.ndarray:
    return 1.0 / np.cosh(x)


def _periodic_signed_distance(x: np.ndarray, *, center: float, L: float) -> np.ndarray:
    return (x - float(center) + 0.5 * float(L)) % float(L) - 0.5 * float(L)


def _second_moment(rho: np.ndarray, dist: np.ndarray, dx: float) -> float:
    mass = float(np.sum(rho) * dx)
    if mass == 0.0:
        return float("nan")
    return float(np.sum((dist**2) * rho) * dx / mass)


def _parity_1d(psi: np.ndarray) -> np.ndarray:
    return psi[::-1]


def _periodic_dxx_fd(psi: np.ndarray) -> np.ndarray:
    return np.roll(psi, -1) - 2.0 * psi + np.roll(psi, 1)


def _periodic_dx_fd(psi: np.ndarray) -> np.ndarray:
    return 0.5 * (np.roll(psi, -1) - np.roll(psi, 1))


def _dirichlet_dxx_fd(psi: np.ndarray) -> np.ndarray:
    n = int(psi.shape[0])
    padded = np.zeros(n + 2, dtype=psi.dtype)
    padded[1:-1] = psi
    return padded[2:] + padded[:-2] - 2.0 * padded[1:-1]


def _time_reversal_error(
    psi0: np.ndarray,
    *,
    k: np.ndarray,
    dt: float,
    g: float,
    V0: float,
    Vx: Optional[np.ndarray],
    gamma: float,
    dx: float,
) -> float:
    """
    Time-reversal diagnostic for one step.

    Compare:
    - forward evolution from conjugated initial data
    - conjugate of one backward step from original data
    """
    _, snaps_fwd = _split_step(
        np.conj(psi0),
        k=k,
        dt=float(dt),
        steps=1,
        sample_every=1,
        g=float(g),
        V0=float(V0),
        Vx=Vx,
        gamma=float(gamma),
    )
    _, snaps_back = _split_step(
        psi0,
        k=k,
        dt=-float(dt),
        steps=1,
        sample_every=1,
        g=float(g),
        V0=float(V0),
        Vx=Vx,
        gamma=float(gamma),
    )
    psi_fwd_from_conj = snaps_fwd[-1]
    psi_tr_from_back = np.conj(snaps_back[-1])
    return float(np.sqrt(np.sum(np.abs(psi_fwd_from_conj - psi_tr_from_back) ** 2) * dx))


def _split_step(
    psi0: np.ndarray,
    *,
    k: np.ndarray,
    dt: float,
    steps: int,
    sample_every: int,
    g: float,
    V0: float,
    Vx: Optional[np.ndarray] = None,
    gamma: float,
) -> tuple[np.ndarray, list[np.ndarray]]:
    psi = np.array(psi0, dtype=np.complex128, copy=True)
    linear_phase = np.exp((-1j * (0.5 * (k**2) + V0) - gamma) * dt)
    kinetic_phase = np.exp((-1j * (0.5 * (k**2))) * dt)
    local_static = None if Vx is None else ((-1j * Vx) - gamma)

    times: list[float] = []
    snaps: list[np.ndarray] = []

    def record(step: int) -> None:
        times.append(step * dt)
        snaps.append(psi.copy())

    record(0)
    for step in range(1, int(steps) + 1):
        if Vx is None:
            if g != 0.0:
                psi *= np.exp(-1j * g * np.abs(psi) ** 2 * (dt / 2.0))

            phat = np.fft.fft(psi)
            phat *= linear_phase
            psi = np.fft.ifft(phat)

            if g != 0.0:
                psi *= np.exp(-1j * g * np.abs(psi) ** 2 * (dt / 2.0))
        else:
            local_a = np.exp((local_static - 1j * g * np.abs(psi) ** 2) * (dt / 2.0))
            psi *= local_a

            phat = np.fft.fft(psi)
            phat *= kinetic_phase
            psi = np.fft.ifft(phat)

            local_b = np.exp((local_static - 1j * g * np.abs(psi) ** 2) * (dt / 2.0))
            psi *= local_b

        if step % int(sample_every) == 0:
            record(step)

    return np.asarray(times, dtype=float), snaps


def _estimate_omega(times: np.ndarray, amps: np.ndarray) -> float:
    phases = np.unwrap(np.angle(amps))
    slope, _ = np.polyfit(times, phases, deg=1)
    return float(-slope)


@dataclass(frozen=True)
class PTCNlseV1Input:
    regime: str
    dimension: str
    n: int
    L: float
    dt: float
    steps: int
    sample_every: int
    g: float
    V0: float
    gamma: float
    A_re: float
    A_im: float
    k: float
    phase: float = 0.0
    case_id: Optional[str] = None
    V_kind: str = "constant"
    V_trap_omega: float = 1.0
    V_center: float = 0.0

    def __post_init__(self) -> None:
        if self.regime not in {"conservative", "dissipative"}:
            raise ValueError("regime must be 'conservative' or 'dissipative'")
        if self.dimension != "1d":
            raise ValueError("dimension must be '1d' for v1")
        if int(self.n) <= 0:
            raise ValueError("n must be a positive integer")
        if not isfinite(float(self.L)) or self.L <= 0:
            raise ValueError("L must be positive")
        if not isfinite(float(self.dt)) or self.dt <= 0:
            raise ValueError("dt must be positive")
        if int(self.steps) <= 0:
            raise ValueError("steps must be positive")
        if int(self.sample_every) <= 0:
            raise ValueError("sample_every must be positive")
        for name in ["g", "V0", "V_trap_omega", "V_center", "gamma", "A_re", "A_im", "k", "phase"]:
            if not isfinite(float(getattr(self, name))):
                raise ValueError(f"{name} must be finite")
        if self.V_kind not in {"constant", "harmonic"}:
            raise ValueError("V_kind must be one of: constant, harmonic")
        if self.V_kind == "harmonic" and float(self.V_trap_omega) <= 0.0:
            raise ValueError("V_trap_omega must be positive for harmonic potential")
        if self.case_id and "trap" in str(self.case_id).lower() and self.V_kind != "harmonic":
            raise ValueError("trap case_id requires V_kind='harmonic'")


def _is_soliton_case(case_id: Optional[str]) -> bool:
    if not case_id:
        return False
    return "soliton" in str(case_id).lower()


def _is_trap_case(inp: PTCNlseV1Input) -> bool:
    if inp.V_kind == "harmonic":
        return True
    if inp.case_id:
        return "trap" in str(inp.case_id).lower()
    return False


def _input_payload(inp: PTCNlseV1Input) -> Dict[str, Any]:
    payload: Dict[str, Any] = {
        "regime": inp.regime,
        "dimension": inp.dimension,
        "n": int(inp.n),
        "L": float(inp.L),
        "dt": float(inp.dt),
        "steps": int(inp.steps),
        "sample_every": int(inp.sample_every),
        "g": float(inp.g),
        "V0": float(inp.V0),
        "gamma": float(inp.gamma),
        "A_re": float(inp.A_re),
        "A_im": float(inp.A_im),
        "k": float(inp.k),
        "phase": float(inp.phase),
    }
    if inp.case_id is not None:
        payload["case_id"] = inp.case_id
    if inp.V_kind != "constant":
        payload["V_kind"] = inp.V_kind
        payload["V_trap_omega"] = float(inp.V_trap_omega)
        payload["V_center"] = float(inp.V_center)
    return payload


def _build_potential_profile(inp: PTCNlseV1Input, x: np.ndarray) -> tuple[np.ndarray, Dict[str, Any]]:
    if inp.V_kind == "harmonic":
        dist = _periodic_signed_distance(x, center=float(inp.V_center), L=float(inp.L))
        Vx = float(inp.V0) + 0.5 * (float(inp.V_trap_omega) ** 2) * (dist**2)
        meta = {
            "kind": "harmonic",
            "V0": _q(float(inp.V0)),
            "V_trap_omega": _q(float(inp.V_trap_omega)),
            "V_center": _q(float(inp.V_center)),
        }
        return Vx.astype(np.float64, copy=False), meta

    Vx = np.full_like(x, float(inp.V0), dtype=np.float64)
    return Vx, {"kind": "constant", "V0": _q(float(inp.V0))}


def _build_initial_state(inp: PTCNlseV1Input, x: np.ndarray) -> np.ndarray:
    A = complex(inp.A_re, inp.A_im)
    if _is_soliton_case(inp.case_id):
        amp = abs(A)
        if amp == 0.0:
            raise ValueError("soliton case requires nonzero amplitude")
        g_abs = abs(float(inp.g)) or 1.0
        width = 1.0 / (amp * np.sqrt(g_abs))
        center = 0.5 * float(inp.L)
        envelope = _sech((x - center) / width)
        phase = float(inp.phase)
        return A * envelope * np.exp(1j * (float(inp.k) * (x - center) + phase))
    if _is_trap_case(inp):
        omega = float(inp.V_trap_omega)
        if omega <= 0.0:
            raise ValueError("trap case requires V_trap_omega > 0")
        center = float(inp.V_center)
        dist = _periodic_signed_distance(x, center=center, L=float(inp.L))
        envelope = np.exp(-0.5 * omega * (dist**2))
        phase = float(inp.phase)
        return A * envelope * np.exp(1j * (float(inp.k) * dist + phase))
    return A * np.exp(1j * (float(inp.k) * x + float(inp.phase)))


def input_from_dict(raw: Dict[str, Any]) -> PTCNlseV1Input:
    V_kind = str(raw.get("V_kind", "constant"))
    V_center_raw = raw.get("V_center")
    if V_center_raw is None:
        V_center_raw = 0.5 * float(raw["L"]) if V_kind == "harmonic" else 0.0
    return PTCNlseV1Input(
        regime=str(raw["regime"]),
        dimension=str(raw.get("dimension", "1d")),
        n=int(raw["n"]),
        L=float(raw["L"]),
        dt=float(raw["dt"]),
        steps=int(raw["steps"]),
        sample_every=int(raw["sample_every"]),
        g=float(raw["g"]),
        V0=float(raw.get("V0", 0.0)),
        V_kind=V_kind,
        V_trap_omega=float(raw.get("V_trap_omega", 1.0)),
        V_center=float(V_center_raw),
        gamma=float(raw.get("gamma", 0.0)),
        A_re=float(raw["A_re"]),
        A_im=float(raw["A_im"]),
        k=float(raw["k"]),
        phase=float(raw.get("phase", 0.0)),
        case_id=raw.get("case_id"),
    )


def load_manifest(*, repo_root: Path, manifest_path: Optional[Path] = None) -> Dict[str, Any]:
    path = manifest_path or _default_manifest_path(repo_root)
    if not path.exists():
        raise FileNotFoundError(f"Missing manifest: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def build_ptc_nlse_v1_report(inp: PTCNlseV1Input) -> Dict[str, Any]:
    inputs = _input_payload(inp)
    input_fingerprint = _sha256_json(inputs)

    n = int(inp.n)
    L = float(inp.L)
    dx = L / n
    x = np.linspace(0.0, L, n, endpoint=False)
    kgrid = _kgrid(L, n)
    Vx, potential_meta = _build_potential_profile(inp, x)

    A = complex(inp.A_re, inp.A_im)
    psi0 = _build_initial_state(inp, x)

    times, snaps = _split_step(
        psi0,
        k=kgrid,
        dt=float(inp.dt),
        steps=int(inp.steps),
        sample_every=int(inp.sample_every),
        g=float(inp.g),
        V0=float(inp.V0),
        Vx=Vx if inp.V_kind != "constant" else None,
        gamma=float(inp.gamma),
    )

    energies = [_energy(psi, kgrid, g=float(inp.g), Vx=Vx, dx=dx) for psi in snaps]
    norms = [_norm(psi, dx) for psi in snaps]

    # Dispersion estimate via projection onto the target mode.
    mode = np.exp(-1j * inp.k * x)
    amps = np.array([np.sum(psi * mode) / n for psi in snaps], dtype=np.complex128)
    omega_hat = _estimate_omega(times, amps)

    omega_expected = 0.5 * (float(inp.k) ** 2) + float(inp.g) * (abs(A) ** 2) + float(inp.V0)
    omega_error = omega_hat - omega_expected

    phase = np.exp(1j * 0.7)
    energy_phase = _energy(phase * psi0, kgrid, g=float(inp.g), Vx=Vx, dx=dx)
    phase_invariance_error = energy_phase - energies[0]
    time_reversal_error = _time_reversal_error(
        psi0,
        k=kgrid,
        dt=float(inp.dt),
        g=float(inp.g),
        V0=float(inp.V0),
        Vx=Vx if inp.V_kind != "constant" else None,
        gamma=float(inp.gamma),
        dx=dx,
    )

    shape_residual: Optional[float] = None
    shape_peak_delta: Optional[float] = None
    shape_peak_ratio: Optional[float] = None
    trap_shape_residual: Optional[float] = None
    trap_peak_ratio: Optional[float] = None
    trap_m2_delta: Optional[float] = None
    if _is_soliton_case(inp.case_id):
        abs0 = np.abs(psi0)
        absT = np.abs(snaps[-1])
        shape_residual = _l2_residual(absT, abs0, dx)
        peak0 = float(abs0.max())
        peakT = float(absT.max())
        shape_peak_delta = peakT - peak0
        shape_peak_ratio = peakT / peak0 if peak0 != 0.0 else float("nan")
    if _is_trap_case(inp):
        abs0 = np.abs(psi0)
        absT = np.abs(snaps[-1])
        trap_shape_residual = _l2_residual(absT, abs0, dx)
        peak0 = float(abs0.max())
        peakT = float(absT.max())
        trap_peak_ratio = peakT / peak0 if peak0 != 0.0 else float("nan")
        dist = _periodic_signed_distance(x, center=float(inp.V_center), L=L)
        rho0 = abs0**2
        rhoT = absT**2
        trap_m2_delta = _second_moment(rhoT, dist, dx) - _second_moment(rho0, dist, dx)

    payload: Dict[str, Any] = {
        "schema": SCHEMA_ID,
        "inputs": inputs,
        "input_fingerprint": input_fingerprint,
        "derived": {
            "grid": {"n": n, "L": _q(L), "dx": _q(dx)},
            "kgrid_sample": [_q(float(kgrid[0])), _q(float(kgrid[1])), _q(float(kgrid[2]))],
            "rac_energy_class": inp.regime,
        },
        "output": {
            "omega_hat": _q(omega_hat),
            "omega_expected": _q(omega_expected),
            "omega_error": _q(omega_error),
            "energy_trace": [_q(x) for x in energies],
            "norm_trace": [_q(x) for x in norms],
            "energy_delta": _q(energies[-1] - energies[0]),
            "norm_delta": _q(norms[-1] - norms[0]),
            "phase_invariance_error": _q(phase_invariance_error),
            "time_reversal_error": _q(time_reversal_error),
            "t_end": _q(float(times[-1])),
        },
        "determinism": {
            "rng": "none",
            "dtype": "complex128",
            "json": "sort_keys,separators=(',',':'),ensure_ascii=True",
        },
    }

    if shape_residual is not None:
        payload["derived"]["initial_condition"] = "sech_soliton"
        payload["output"]["shape_residual"] = _q(shape_residual)
        payload["output"]["shape_peak_delta"] = _q(shape_peak_delta)
        payload["output"]["shape_peak_ratio"] = _q(shape_peak_ratio)
    if trap_shape_residual is not None:
        payload["derived"]["initial_condition"] = "harmonic_ground_state_like"
        payload["derived"]["potential"] = potential_meta
        payload["output"]["trap_shape_residual"] = _q(trap_shape_residual)
        payload["output"]["trap_peak_ratio"] = _q(trap_peak_ratio)
        payload["output"]["trap_m2_delta"] = _q(trap_m2_delta)

    payload["fingerprint"] = _sha256_json(payload)
    return payload


def build_ptc_nlse_v1_hooks(inp: PTCNlseV1Input) -> Dict[str, Any]:
    """
    Deterministic hooks payload for structural falsifier lanes (SYM/PAR/BC).
    Keeps report schema stable by emitting a separate artifact.
    """
    inputs = _input_payload(inp)
    input_fingerprint = _sha256_json(inputs)

    n = int(inp.n)
    L = float(inp.L)
    dx = L / n
    x = np.linspace(0.0, L, n, endpoint=False)
    kgrid = _kgrid(L, n)
    Vx, _ = _build_potential_profile(inp, x)

    A = complex(inp.A_re, inp.A_im)
    psi0 = _build_initial_state(inp, x)

    _, snaps = _split_step(
        psi0,
        k=kgrid,
        dt=float(inp.dt),
        steps=int(inp.steps),
        sample_every=int(inp.sample_every),
        g=float(inp.g),
        V0=float(inp.V0),
        Vx=Vx if inp.V_kind != "constant" else None,
        gamma=float(inp.gamma),
    )
    psi_t = snaps[-1]

    # SYM01: phase-pass and conjugation-fail diagnostics on evolved state.
    theta = 0.7
    phase = np.exp(1j * theta)
    g = float(inp.g)
    p = lambda psi: g * (np.abs(psi) ** 2) * psi
    sym01_phase_residual = _l2_residual(p(phase * psi_t), phase * p(psi_t), dx)
    sym01_conjugation_residual = _l2_residual(np.conj(phase * psi_t), phase * np.conj(psi_t), dx)

    # PAR01: parity-preserving evolution residual and parity-breaking advection residual.
    _, snaps_par = _split_step(
        _parity_1d(psi0),
        k=kgrid,
        dt=float(inp.dt),
        steps=int(inp.steps),
        sample_every=int(inp.sample_every),
        g=float(inp.g),
        V0=float(inp.V0),
        Vx=Vx if inp.V_kind != "constant" else None,
        gamma=float(inp.gamma),
    )
    psi_t_from_parity_init = snaps_par[-1]
    par01_parity_residual = _l2_residual(psi_t_from_parity_init, _parity_1d(psi_t), dx)

    lhs_adv = _periodic_dx_fd(_parity_1d(psi_t))
    rhs_adv = _parity_1d(_periodic_dx_fd(psi_t))
    par01_advection_break_residual = _l2_residual(lhs_adv, rhs_adv, dx)

    # BC01: periodic/Dirichlet mismatch diagnostics.
    bc01_boundary_residual = _l2_residual(_periodic_dxx_fd(psi0), _dirichlet_dxx_fd(psi0), dx)

    ones = np.ones(n, dtype=np.float64)
    bc01_periodic_constant_residual = float(np.max(np.abs(_periodic_dxx_fd(ones))))
    bc01_dirichlet_constant_residual = float(np.max(np.abs(_dirichlet_dxx_fd(ones))))

    payload: Dict[str, Any] = {
        "schema": HOOKS_SCHEMA_ID,
        "inputs": inputs,
        "input_fingerprint": input_fingerprint,
        "hooks": {
            "sym01_phase_residual": _q(sym01_phase_residual),
            "sym01_conjugation_residual": _q(sym01_conjugation_residual),
            "par01_parity_residual": _q(par01_parity_residual),
            "par01_advection_break_residual": _q(par01_advection_break_residual),
            "bc01_boundary_residual": _q(bc01_boundary_residual),
            "bc01_periodic_constant_residual": _q(bc01_periodic_constant_residual),
            "bc01_dirichlet_constant_residual": _q(bc01_dirichlet_constant_residual),
        },
        "determinism": {
            "rng": "none",
            "dtype": "complex128",
            "json": "sort_keys,separators=(',',':'),ensure_ascii=True",
        },
    }
    payload["fingerprint"] = _sha256_json(payload)
    return payload


def dumps_report(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def dumps_hooks(payload: Dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _load_input_json(path_or_json: str) -> Dict[str, Any]:
    text = path_or_json
    if Path(path_or_json).exists():
        text = Path(path_or_json).read_text(encoding="utf-8")
    return json.loads(text)


def _build_input_from_args(args: argparse.Namespace, repo_root: Path) -> PTCNlseV1Input:
    if args.case:
        manifest = load_manifest(repo_root=repo_root, manifest_path=Path(args.manifest) if args.manifest else None)
        if manifest.get("schema") != MANIFEST_SCHEMA:
            raise ValueError("Unexpected manifest schema")
        cases = manifest.get("cases", {})
        if args.case not in cases:
            raise KeyError(f"Unknown case_id: {args.case}")
        raw = dict(cases[args.case])
        raw["case_id"] = args.case
        return input_from_dict(raw)

    if args.input_json:
        raw = _load_input_json(args.input_json)
        return input_from_dict(raw)

    missing = [
        name
        for name in [
            "regime",
            "n",
            "L",
            "dt",
            "steps",
            "sample_every",
            "g",
            "A_re",
            "A_im",
            "k",
        ]
        if getattr(args, name) is None
    ]
    if missing:
        raise SystemExit(f"Missing required args: {', '.join(missing)}")

    return PTCNlseV1Input(
        regime=str(args.regime),
        dimension="1d",
        n=int(args.n),
        L=float(args.L),
        dt=float(args.dt),
        steps=int(args.steps),
        sample_every=int(args.sample_every),
        g=float(args.g),
        V0=float(args.V0 or 0.0),
        V_kind=str(args.V_kind or "constant"),
        V_trap_omega=float(args.V_trap_omega or 1.0),
        V_center=float(args.V_center if args.V_center is not None else 0.0),
        gamma=float(args.gamma or 0.0),
        A_re=float(args.A_re),
        A_im=float(args.A_im),
        k=float(args.k),
        phase=float(args.phase or 0.0),
    )


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate PTC NLSE v1 report JSON (schema v1).")
    p.add_argument("--case", help="Case ID from manifest (preferred)")
    p.add_argument("--manifest", help="Override manifest path (repo-relative or absolute)")
    p.add_argument("--input-json", help="JSON file path (or raw JSON) with input fields")

    p.add_argument("--regime", choices=["conservative", "dissipative"])
    p.add_argument("--n", type=int)
    p.add_argument("--L", type=float)
    p.add_argument("--dt", type=float)
    p.add_argument("--steps", type=int)
    p.add_argument("--sample-every", type=int)
    p.add_argument("--g", type=float)
    p.add_argument("--V0", type=float, default=0.0)
    p.add_argument("--V-kind", choices=["constant", "harmonic"], default="constant")
    p.add_argument("--V-trap-omega", type=float, default=1.0)
    p.add_argument("--V-center", type=float, default=0.0)
    p.add_argument("--gamma", type=float, default=0.0)
    p.add_argument("--A-re", type=float)
    p.add_argument("--A-im", type=float)
    p.add_argument("--k", type=float)
    p.add_argument("--phase", type=float, default=0.0)
    p.add_argument(
        "--out",
        default="formal/output/PTC_NLSE_V1_REPORT.json",
        help="Repo-relative output JSON path",
    )
    p.add_argument(
        "--hooks-out",
        default=None,
        help="Optional repo-relative hooks JSON path (B1 diagnostics artifact)",
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the output file")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    inp = _build_input_from_args(args, repo_root)
    payload = build_ptc_nlse_v1_report(inp)
    out_text = dumps_report(payload)
    hooks_payload = build_ptc_nlse_v1_hooks(inp)
    hooks_text = dumps_hooks(hooks_payload)

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")
        if args.hooks_out:
            hooks_path = repo_root / str(args.hooks_out)
            hooks_path.parent.mkdir(parents=True, exist_ok=True)
            hooks_path.write_text(hooks_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
