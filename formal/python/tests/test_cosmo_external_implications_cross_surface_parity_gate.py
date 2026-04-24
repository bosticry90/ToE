from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0.md"
PARENT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
PILOT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md"
)
SUMMARY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md"
PACKAGE_PATH = REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_external_implications_pointer_parity_across_cosmo_surfaces() -> None:
    plan_text = _read(PLAN_PATH)
    parent_text = _read(PARENT_PATH)
    pilot_text = _read(PILOT_PATH)
    summary_text = _read(SUMMARY_PATH)
    package_text = _read(PACKAGE_PATH)
    state_text = _read(STATE_PATH)
    suite_text = _read(SUITE_PATH)

    target_id = "TARGET-COSMO-BG-EXTERNAL-HI-REFERENCE-SURFACE-v0"
    target_doc = "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md"
    parent_doc = "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
    plan_doc = "formal/docs/release/EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0.md"
    policy_gate = "formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py"
    parity_gate = "formal/python/tests/test_cosmo_external_implications_cross_surface_parity_gate.py"

    # Plan + pilot + parent must carry consistent pilot identity and pointers.
    assert target_doc in plan_text
    assert parent_doc in plan_text
    assert policy_gate in plan_text

    assert target_id in parent_text
    assert target_doc in parent_text
    assert policy_gate in parent_text

    assert target_id in pilot_text
    assert plan_doc in pilot_text
    assert parent_doc in pilot_text
    assert policy_gate in pilot_text

    # Rollup summary/package must include pilot plan/doc anchors.
    summary_required = [
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_PROGRESS_v0: REFERENCE_SURFACE_POLICY_GATE_PINNED",
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_TARGET_v0: TARGET-COSMO-BG-EXTERNAL-HI-REFERENCE-SURFACE-v0",
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_BOUNDARY_v0: REFERENCE_ONLY_NON_PROMOTIONAL",
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_PLAN_v0: formal/docs/release/EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0.md",
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_TARGET_DOC_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md",
        "COSMO_BG_EXTERNAL_IMPLICATIONS_PILOT_POLICY_GATE_v0: formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py",
    ]
    missing_summary = [token for token in summary_required if token not in summary_text]
    assert not missing_summary, "COSMO summary external-implications pointer drift: " + ", ".join(missing_summary)

    assert target_doc in package_text
    assert plan_doc in package_text

    # State + suite must anchor both policy gate and this parity gate.
    state_required = [
        "EXTERNAL_IMPLICATIONS_POLICY_MODE_v0: REFERENCE_ONLY_NON_PROMOTIONAL",
        "EXTERNAL_IMPLICATIONS_PILOT_TARGET_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md",
        "EXTERNAL_IMPLICATIONS_PARENT_BINDING_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "EXTERNAL_IMPLICATIONS_GOVERNANCE_GATE_v0: formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py",
        "formal/python/tests/test_cosmo_external_implications_cross_surface_parity_gate.py",
    ]
    missing_state = [token for token in state_required if token not in state_text]
    assert not missing_state, "State external-implications parity drift: " + ", ".join(missing_state)

    assert policy_gate in suite_text
    assert parity_gate in suite_text
