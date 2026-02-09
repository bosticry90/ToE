"""EMP-01 — single proxy falsifier test (Behavioral / Python).

This test is intentionally:
- synthetic (simulation-only)
- non-empirical
- non-confirmatory

It asserts exactly one falsifiability condition and does not write locks,
modify gates, or participate in pruning.
"""

from __future__ import annotations

import hashlib
import json

from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.empirical_probes.emp01_proxy_falsifiability import (
    emp01_proxy_falsifiability_probe,
)


def test_emp01_proxy_falsifiability_single_threshold() -> None:
    # Pinned frozen DR-01 fit artifact payload embedded as a constant.
    # This keeps EMP-01 at zero runtime I/O (Option A) while still tying the
    # probe to a real frozen artifact used elsewhere in the program.
    #
    # Source file (read-only provenance reference):
    #   formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json
    #
    # Guardrail: this embedding is not an empirical claim; it is a pinned input.
    DR01_FROZEN = {
        "u": 0.0,
        "c_s": 0.0021889420972527477,
        "tag": "DR02_Steinhauer_Fig3a_lowk_linearization_2026-01-17",
        "source_kind": "csv",
        "source_ref": (
            "Steinhauer PRL 88, 120407 (2002), Fig 3a; digitized from arXiv 0111438v1; "
            "formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv; "
            "low-k window k<= 3.2 um^-1; fit through origin; omega=2*pi*f; date 2026-01-17"
        ),
        "data_fingerprint": "80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af",
        "fit_method_tag": "low-k through-origin omega~=c_s*k on k<= 3.2 um^-1; u fixed to 0",
        # sample_kw omitted intentionally: EMP-01 depends only on DR-01→BR-01, not refitting.
    }

    # Tamper-evident embedded payload digest (integrity invariant; not a scientific criterion).
    # Canonical preimage: json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    EMBEDDED_DR01_PAYLOAD_SHA256 = "799b4fcc1d71a3e0a757044468f62d43c2148c619f568ac4cdca68d24914cd3e"
    canon = json.dumps(DR01_FROZEN, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    digest = hashlib.sha256(canon.encode("utf-8")).hexdigest()
    assert digest == EMBEDDED_DR01_PAYLOAD_SHA256

    dr01_fit = DR01Fit1D(
        u=float(DR01_FROZEN["u"]),
        c_s=float(DR01_FROZEN["c_s"]),
        tag=str(DR01_FROZEN["tag"]),
        source_kind=str(DR01_FROZEN["source_kind"]),
        source_ref=str(DR01_FROZEN["source_ref"]),
        data_fingerprint=str(DR01_FROZEN["data_fingerprint"]),
        fit_method_tag=str(DR01_FROZEN["fit_method_tag"]),
        sample_kw=None,
    )

    # Fixed k-grid including +/- to cover abs(k) branch.
    k_grid = (-3.0, -1.0, -0.25, 0.0, 0.25, 1.0, 3.0)

    # Single falsifier threshold.
    tol = 1.0e-12

    rep1 = emp01_proxy_falsifiability_probe(dr01_fit, k_grid=k_grid, tol=tol)
    rep2 = emp01_proxy_falsifiability_probe(dr01_fit, k_grid=k_grid, tol=tol)

    # Determinism invariant (not an additional scientific falsifier).
    assert rep1.max_abs_omega_residual == rep2.max_abs_omega_residual
    assert rep1.passed == rep2.passed

    # Single falsifier assertion.
    assert rep1.passed, (
        "EMP-01 proxy falsifier triggered. "
        "This is not a program-wide refutation; it only indicates the DR-01→BR-01 omega(k) "
        "consistency proxy failed under a synthetic pinned scenario. "
        f"max_abs_omega_residual={rep1.max_abs_omega_residual} tol={rep1.tol}"
    )
