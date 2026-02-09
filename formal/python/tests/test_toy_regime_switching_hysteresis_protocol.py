from __future__ import annotations

from math import isclose


def _ramp(u_min: float, u_max: float, n: int, *, descending: bool = False) -> list[float]:
    if n < 2:
        raise ValueError("n must be >= 2")
    step = (u_max - u_min) / float(n - 1)
    if descending:
        return [u_max - i * step for i in range(n)]
    return [u_min + i * step for i in range(n)]


def _protocol(u_min: float, u_max: float, n_up: int, n_down: int) -> tuple[list[float], list[float], list[float]]:
    up = _ramp(u_min, u_max, n_up, descending=False)
    down = _ramp(u_min, u_max, n_down, descending=True)
    useq = up + down[1:]
    return useq, up, down


def _simulate(mu0: float, a: float, mu_on: float, mu_off: float, useq: list[float]) -> dict:
    mu = float(mu0)
    reg = "incoherent"
    mu_seq: list[float] = []
    reg_seq: list[str] = []

    for u in useq:
        mu = mu + float(a) * (float(u) - mu)
        mu = max(0.0, min(1.0, mu))
        if reg == "incoherent" and mu >= float(mu_on):
            reg = "coherent"
        elif reg == "coherent" and mu <= float(mu_off):
            reg = "incoherent"
        mu_seq.append(mu)
        reg_seq.append(reg)

    flips = [i for i in range(1, len(reg_seq)) if reg_seq[i] != reg_seq[i - 1]]
    return {"mu_seq": mu_seq, "reg_seq": reg_seq, "flips": flips}


def _index_of(value: float, grid: list[float]) -> int:
    for idx, val in enumerate(grid):
        if isclose(float(val), float(value), rel_tol=0.0, abs_tol=1e-12):
            return idx
    raise ValueError(f"value {value} not found in grid")


def _admissible_hysteresis(
    *,
    sim: dict,
    mu_on: float,
    mu_off: float,
    up: list[float],
    down: list[float],
    u_star: float,
) -> bool:
    if float(mu_on) <= float(mu_off):
        return False

    flips = list(sim["flips"])
    if len(flips) != 2:
        return False

    up_idx = _index_of(u_star, up)
    down_idx = len(up) + _index_of(u_star, down[1:])
    reg_up = sim["reg_seq"][up_idx]
    reg_down = sim["reg_seq"][down_idx]
    if reg_up == reg_down:
        return False

    # Localization: first flip crosses mu_on upward; second flip crosses mu_off downward.
    mu_seq = sim["mu_seq"]
    idx_up, idx_down = flips
    prev_up = mu_seq[idx_up - 1]
    cur_up = mu_seq[idx_up]
    if not (prev_up < float(mu_on) <= cur_up):
        return False

    prev_down = mu_seq[idx_down - 1]
    cur_down = mu_seq[idx_down]
    if not (prev_down > float(mu_off) >= cur_down):
        return False

    return True


def test_toy_regime_switching_hysteresis_protocol() -> None:
    u_min = 0.0
    u_max = 1.0
    n_up = 9
    n_down = 9
    mu_on = 0.62
    mu_off = 0.38
    a = 0.35
    mu0 = 0.10
    u_star = 0.5

    useq, up, down = _protocol(u_min, u_max, n_up, n_down)
    sim = _simulate(mu0, a, mu_on, mu_off, useq)

    assert _admissible_hysteresis(sim=sim, mu_on=mu_on, mu_off=mu_off, up=up, down=down, u_star=u_star)


def test_toy_regime_switching_hysteresis_negative_control_swapped_thresholds() -> None:
    u_min = 0.0
    u_max = 1.0
    n_up = 9
    n_down = 9
    mu_on = 0.38
    mu_off = 0.62
    a = 0.35
    mu0 = 0.10
    u_star = 0.5

    useq, up, down = _protocol(u_min, u_max, n_up, n_down)
    sim = _simulate(mu0, a, mu_on, mu_off, useq)

    assert not _admissible_hysteresis(sim=sim, mu_on=mu_on, mu_off=mu_off, up=up, down=down, u_star=u_star)


def test_toy_regime_switching_hysteresis_negative_control_no_gap() -> None:
    u_min = 0.0
    u_max = 1.0
    n_up = 9
    n_down = 9
    mu_on = 0.5
    mu_off = 0.5
    a = 0.35
    mu0 = 0.10
    u_star = 0.5

    useq, up, down = _protocol(u_min, u_max, n_up, n_down)
    sim = _simulate(mu0, a, mu_on, mu_off, useq)

    assert not _admissible_hysteresis(sim=sim, mu_on=mu_on, mu_off=mu_off, up=up, down=down, u_star=u_star)
