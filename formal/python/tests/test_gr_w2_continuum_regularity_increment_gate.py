from __future__ import annotations

import json
import math
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_w2_continuum_regularity_increment_20260325_v0.json"
PREV_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_continuum_science_increment_20260325_v0.json"
CONTINUUM_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md"
REGULARITY_SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0.md"
ROUTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _artifact() -> dict:
    return json.loads(_read(ARTIFACT_PATH))


def test_gr_w2_continuation_increment_artifacts_exist() -> None:
    assert ARTIFACT_PATH.exists(), "Missing W2 continuation artifact."
    assert PREV_ARTIFACT_PATH.exists(), "Missing predecessor GR continuum increment artifact."


def test_gr_w2_continuation_increment_tokens_are_pinned_on_gr_surfaces() -> None:
    continuum_text = _read(CONTINUUM_TARGET_PATH)
    regularity_text = _read(REGULARITY_SURFACE_PATH)
    route_text = _read(ROUTE_PATH)

    continuum_tokens = [
        "GR_W2_CONTINUATION_INCREMENT_20260325_STATUS_v0: BOUNDED_W2_CONTINUATION_INCREMENT_PINNED_NONCLAIM",
        "GR_W2_CONTINUATION_INCREMENT_20260325_ARTIFACT_v0: gr_w2_continuum_regularity_increment_20260325_v0",
        "formal/output/gr_w2_continuum_regularity_increment_20260325_v0.json",
        "GR_W2_RESIDUAL_ORDER_STABILITY_v0: FOUR_LEVEL_REFINEMENT_RATIO_AND_P_WINDOW_PINNED",
        "GR_W2_ROUTE_TO_EVIDENCE_STEP_v0: LOCAL_H1_BOUND_AND_WEAK_GRADIENT_CAUCHY_TEMPLATE_LINKED_NONCLAIM",
    ]
    for token in continuum_tokens:
        assert token in continuum_text

    assert (
        "GR01_FUNCTION_SPACE_ROW_02_CONTINUATION_ARTIFACT_v0: gr_w2_continuum_regularity_increment_20260325_v0"
        in regularity_text
    )
    assert "formal/output/gr_w2_continuum_regularity_increment_20260325_v0.json" in regularity_text

    route_tokens = [
        "GR01_FUNCTION_SPACE_W2_CONTINUATION_STATUS_v0: ROUTE_TO_EVIDENCE_STEP_PINNED_NONCLAIM",
        "GR01_FUNCTION_SPACE_W2_CONTINUATION_ARTIFACT_POINTER_v0: formal/output/gr_w2_continuum_regularity_increment_20260325_v0.json",
        "GR01_FUNCTION_SPACE_W2_CONTINUATION_PAYLOAD_v0: FOUR_LEVEL_RESIDUAL_ORDER_STABILITY_PLUS_LOCAL_REGULARITY_TEMPLATE",
    ]
    for token in route_tokens:
        assert token in route_text


def test_gr_w2_continuation_increment_artifact_schema_and_numeric_payload() -> None:
    artifact = _artifact()

    assert artifact["artifact_id"] == "gr_w2_continuum_regularity_increment_20260325_v0"
    assert artifact["lane"] == "GR_CONTINUUM_FUNCTION_SPACE"
    assert artifact["status"] == "BOUNDED_W2_CONTINUATION_INCREMENT_PINNED_NONCLAIM"

    assert artifact["derived_from"]["artifact_id"] == "gr_continuum_science_increment_20260325_v0"
    assert artifact["derived_from"]["artifact_path"] == "formal/output/gr_continuum_science_increment_20260325_v0.json"

    residual = artifact["residual_order_witness"]
    h_values = residual["h_values"]
    e_values = residual["E_h"]
    ratios = residual["ratio_Eh_over_Eh2"]
    p_values = residual["p_estimate"]
    p_window = residual["p_stability_window"]

    assert len(h_values) == 4
    assert len(e_values) == 4
    assert len(ratios) == 3
    assert len(p_values) == 3

    assert all(h_values[i] > h_values[i + 1] for i in range(len(h_values) - 1))
    assert all(e_values[i] > e_values[i + 1] for i in range(len(e_values) - 1))

    recomputed_ratios = [e_values[i] / e_values[i + 1] for i in range(3)]
    for got, expected in zip(ratios, recomputed_ratios):
        assert math.isclose(got, expected, rel_tol=1e-12, abs_tol=1e-12)

    recomputed_p = [math.log2(r) for r in ratios]
    for got, expected in zip(p_values, recomputed_p):
        assert math.isclose(got, expected, rel_tol=1e-12, abs_tol=1e-12)

    p_min, p_max = p_window
    assert p_min < p_max
    assert all(p_min <= p <= p_max for p in p_values)

    local = artifact["local_regularity_witness"]
    assert local["compact_set"] == "K_subset_Omega_compact"
    assert "H1(K)" in local["h1_bound_template"]
    assert "grad u_h" in local["weak_gradient_cauchy_template"]
    assert local["route_step"] == "ROUTE_TO_EVIDENCE_STEP_PINNED_NONCLAIM"


def test_gr_w2_continuation_increment_nonclaim_boundary_is_explicit() -> None:
    bounded = _artifact()["bounded_scope"]

    assert bounded["continuum_theorem_completion_claimed"] is False
    assert bounded["sobolev_completion_claimed"] is False
    assert bounded["uniqueness_completion_claimed"] is False
    assert bounded["infinite_domain_uniqueness_claimed"] is False
    assert bounded["singular_source_completion_claimed"] is False

    adjudication = _artifact()["adjudication"]
    assert adjudication["token"] == "GR_W2_CONTINUATION_INCREMENT_20260325_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"
