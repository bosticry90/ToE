from __future__ import annotations

import json

import numpy as np

from formal.python.toe.ucff.core_front_door import (
    UcffCoreInput,
    UcffCoreParams,
    dumps_ucff_core_report,
    loads_ucff_core_report,
    ucff_core_report,
    ucff_dispersion_omega2_numeric,
)


def test_ucff_core_front_door_baseline_matches_free_polynomial() -> None:
    k = np.array([0.0, 0.25, 0.5, 1.0], dtype=float)
    params = UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0)

    omega2 = ucff_dispersion_omega2_numeric(k=k, params=params)
    expected = (k**2 / 2.0) ** 2

    assert np.allclose(omega2, expected, atol=0.0, rtol=0.0)


def test_ucff_core_front_door_report_json_roundtrip_is_deterministic() -> None:
    inp = UcffCoreInput(
        k=[0.0, 0.25, 0.5, 1.0],
        params=UcffCoreParams(rho0=1.0, g=1.25, lam=0.1, beta=0.01),
        config_tag="pytest_ucff_core_front_door_v1",
    )

    rep = ucff_core_report(inp)
    s1 = dumps_ucff_core_report(rep)
    payload = loads_ucff_core_report(s1)
    s2 = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    assert s1 == s2
    assert payload["fingerprint"]
    assert payload["schema"] == "UCFF/core_front_door_report/v1"
    assert payload["config_tag"] == "pytest_ucff_core_front_door_v1"


def test_ucff_core_front_door_json_payload_roundtrip_recomputes_omega2() -> None:
    # Additional bounded roundtrip-family invariant:
    # JSON payload -> recomputed omega2 must match exactly for a representable input family.
    inp = UcffCoreInput(
        k=[0.0, 0.25, 0.5, 1.0, 2.0],
        params=UcffCoreParams(rho0=1.0, g=2.0, lam=0.25, beta=0.125),
        config_tag="pytest_ucff_core_front_door_roundtrip_semantic_v1",
    )

    rep = ucff_core_report(inp)
    payload = loads_ucff_core_report(dumps_ucff_core_report(rep))

    k = np.array(payload["k"], dtype=float)
    params = UcffCoreParams(
        rho0=float(payload["params"]["rho0"]),
        g=float(payload["params"]["g"]),
        lam=float(payload["params"]["lam"]),
        beta=float(payload["params"]["beta"]),
    )
    omega2_re = ucff_dispersion_omega2_numeric(k=k, params=params)
    omega2_payload = np.array(payload["omega2"], dtype=float)

    assert np.allclose(omega2_re, omega2_payload, atol=0.0, rtol=0.0)
