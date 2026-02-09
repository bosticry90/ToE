from __future__ import annotations

from pathlib import Path


def _read_text(repo_root: Path, relpath: str) -> str:
    return (repo_root / relpath).read_text(encoding="utf-8")


def test_ov_sw01_schema_doc_has_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]

    schema_doc_relpath = "formal/docs/lanes/OV-SW-01_shallow_water_lowk_slope_schema.md"
    text = _read_text(repo_root, schema_doc_relpath)

    # Pinned schema identity
    assert "OV-SW-01_shallow_water_lowk_slope/v1" in text

    # Pinned unit-identity export (dimensional only)
    assert "1 (s^-1)/(m^-1) = 1 (m/s)" in text

    # Pinned unit strings (canonical)
    assert "`k`: `m^-1`" in text
    assert "`f = ω/(2π)`: `s^-1`" in text
    assert "derived `c`: `m/s`" in text

    # Explicit non-claims must be present.
    for required in [
        "not_asserting_physical_model_validity",
        "not_asserting_cross_lane_equivalence",
        "not_asserting_pairing_exists",
        "not_asserting_gate_sufficiency_or_enablement",
    ]:
        assert required in text
