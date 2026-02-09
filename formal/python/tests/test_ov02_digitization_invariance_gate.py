from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.observables.ov02_digitization_invariance import ov02_digitization_invariance_gate


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_sample_kw_from_fit_json(path: Path) -> tuple[tuple[float, float], ...]:
    d = _load_json(path)
    if d.get("sample_kw") is None:
        raise AssertionError(f"Missing sample_kw in {path}")
    return tuple((float(k), float(w)) for (k, w) in d["sample_kw"])


def test_ov02_digitization_invariance_gate_v1_does_not_flip_ov01g_preference_under_small_perturbations():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    # Use the same 4-window set used by OV-01g mainline (DR-02a/03a/04d/05a).
    # Pull sample_kw from the already-frozen fit artifacts.
    s02 = _load_sample_kw_from_fit_json(base / "dr01_fit_artifact.json")
    s03 = _load_sample_kw_from_fit_json(base / "dr03_fit_artifact.json")
    s04d = _load_sample_kw_from_fit_json(base / "dr04d_fit_artifact.json")
    s05 = _load_sample_kw_from_fit_json(base / "dr05_fit_artifact.json")

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep = ov02_digitization_invariance_gate(
        fn,
        windows_sample_kw=[s02, s03, s04d, s05],
        rel_eps=0.01,
        patterns=("baseline", "alt_pm", "ramp"),
        adequacy_policy="DQ-01_v1",
    )

    # Determinism
    assert rep.fingerprint() == ov02_digitization_invariance_gate(
        fn,
        windows_sample_kw=[s02, s03, s04d, s05],
        rel_eps=0.01,
        patterns=("baseline", "alt_pm", "ramp"),
        adequacy_policy="DQ-01_v1",
    ).fingerprint()

    # Invariance pass (metamorphic): baseline preference must not flip.
    assert rep.baseline_prefer_curved is True
    assert rep.all_scenarios_match_baseline is True
    assert rep.robustness_failed is False

    # Sanity: each scenario must remain decided (no silent undecided allowed).
    for sc in rep.scenarios:
        assert sc.ov01g_prefer_curved is True
        assert sc.ov01g_robustness_failed is False
        assert sc.ov01g_curved_adequacy_passes is True
