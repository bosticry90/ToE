from __future__ import annotations

from formal.python.tools.authority_surface_parity_check import (
    compare_remediation_tokens,
    extract_remediation_tokens,
    run,
)


def test_extract_remediation_tokens_finds_expected_shape() -> None:
    content = "- `THEORY_RESTART_T26_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE`\n- `IGNORED_TOKEN_v0: NO`"
    tokens = extract_remediation_tokens(content)
    assert tokens == ["THEORY_RESTART_T26_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE"]


def test_compare_remediation_tokens_detects_missing_tokens() -> None:
    state_tokens = ["THEORY_RESTART_T25_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE"]
    roadmap_tokens: list[str] = []
    errors = compare_remediation_tokens(state_tokens, roadmap_tokens, strict_order=False)
    assert errors, "Expected missing-token error when roadmap token set is empty."
    assert "Missing in PHYSICS_ROADMAP_v0.md" in errors[0]


def test_compare_remediation_tokens_detects_order_mismatch_when_enabled() -> None:
    state_tokens = [
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE",
    ]
    roadmap_tokens = [
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE",
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE",
    ]
    errors = compare_remediation_tokens(state_tokens, roadmap_tokens, strict_order=True)
    assert any("Token order mismatch" in error for error in errors)


def test_run_parity_check_passes_on_current_repo_surfaces() -> None:
    assert run(strict_order=False) == 0
