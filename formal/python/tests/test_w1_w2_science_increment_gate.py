from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
SR_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md"
GR_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md"
GR_ROUTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md"
SR_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "sr_covariance_science_increment_20260325_v0.json"
GR_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_continuum_science_increment_20260325_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_w1_sr_covariance_science_increment_is_pinned_with_exact_witness() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)
    artifact = _json(SR_ARTIFACT_PATH)

    for token in (
        "SR_COVARIANCE_SCI_INCREMENT_20260325_STATUS_v0: BOUNDED_CLOSURE_EXTENSION_PINNED",
        "SR_COVARIANCE_INTERVAL_INVARIANCE_IDENTITY_v0: T_PRIME_SQUARED_MINUS_X_PRIME_SQUARED_EQUALS_T_SQUARED_MINUS_X_SQUARED",
        "SR_COVARIANCE_VELOCITY_COMPOSITION_FORM_v0: BETA12_EQUALS_BETA1_PLUS_BETA2_OVER_1_PLUS_BETA1_BETA2",
        "formal/output/sr_covariance_science_increment_20260325_v0.json",
    ):
        assert token in target_text
        assert token in state_text

    assert artifact["status"] == "BOUNDED_CLOSURE_EXTENSION_PINNED"
    interval = artifact["exact_rational_witness"]["interval_case"]
    assert Fraction(interval["s2"]) == Fraction(interval["s2_prime"])

    comp = artifact["exact_rational_witness"]["composition_case"]
    beta12 = Fraction(comp["beta12"])
    assert beta12 < 1
    assert comp["subluminal"] is True


def test_w2_gr_continuum_science_increment_has_ordered_refinement_witness() -> None:
    target_text = _read(GR_TARGET_PATH)
    route_text = _read(GR_ROUTE_PATH)
    state_text = _read(STATE_PATH)
    artifact = _json(GR_ARTIFACT_PATH)

    for token in (
        "GR_CONTINUUM_SCI_INCREMENT_20260325_STATUS_v0: RESIDUAL_ORDER_ESTIMATE_PINNED_NONCLAIM",
        "GR_CONTINUUM_RESIDUAL_ORDER_ESTIMATE_v0: P_APPROX_2_FROM_TWO_LEVEL_REFINEMENT_RATIO",
        "formal/output/gr_continuum_science_increment_20260325_v0.json",
    ):
        assert token in target_text
        assert token in state_text

    assert "GR01_FUNCTION_SPACE_CONTINUUM_SCI_INCREMENT_20260325_v0: ORDERED_REFINEMENT_WITNESS_LINKED_NONCLAIM" in route_text

    ratios = artifact["residual_witness"]["ratio_Eh_over_Eh2"]
    pvals = artifact["residual_witness"]["p_estimate"]
    assert all(r > 1.0 for r in ratios)
    assert all(1.5 <= p <= 2.5 for p in pvals)
    assert artifact["bounded_scope"]["infinite_domain_uniqueness_claimed"] is False
    assert artifact["bounded_scope"]["singular_source_completion_claimed"] is False
