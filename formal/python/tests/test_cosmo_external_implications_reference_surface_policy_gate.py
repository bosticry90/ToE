from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0.md"
PILOT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md"
)
PARENT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_external_implications_plan_contract_tokens_are_present() -> None:
    text = _read(PLAN_PATH)
    required_tokens = [
        "EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0",
        "EXTERNAL_IMPLICATIONS_POLICY_MODE_v0: REFERENCE_ONLY_NON_PROMOTIONAL",
        "EXTERNAL_IMPLICATIONS_NO_PROMOTION_v0: NO_RESULTS_TABLE_OR_ADJUDICATION_PROMOTION",
        "EXTERNAL_IMPLICATIONS_LOCALIZATION_GATE_v0: PILOT_DOC_SCOPE_ONLY",
        "EXTERNAL_IMPLICATIONS_BOUNDARY_v0: NO_STATE_ROADMAP_MATRIX_WRITES",
        "EXTERNAL_IMPLICATIONS_CONFIDENCE_TIERS_v0: TIER_1_HIGH;TIER_2_MEDIUM;TIER_3_EXPLORATORY",
        "EXTERNAL_IMPLICATIONS_CITATION_MINIMUM_v0: SOURCE_URL_OR_DOI_AND_ACCESS_DATE_REQUIRED",
        "EXTERNAL_IMPLICATIONS_PILOT_TARGET_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md",
        "EXTERNAL_IMPLICATIONS_PARENT_BINDING_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "EXTERNAL_IMPLICATIONS_GOVERNANCE_GATE_v0: formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py",
        "No updates to `State_of_the_Theory.md` are authorized by this plan.",
        "No updates to `formal/docs/paper/PHYSICS_ROADMAP_v0.md` are authorized by this plan.",
        "No updates to `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json` are authorized by this plan.",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "External implications plan token drift: " + ", ".join(missing)


def test_external_implications_pilot_contract_tokens_are_present() -> None:
    text = _read(PILOT_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0",
        "TARGET-COSMO-BG-EXTERNAL-HI-REFERENCE-SURFACE-v0",
        "COSMO_EXTERNAL_IMPLICATIONS_PARENT_TARGET_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "COSMO_EXTERNAL_IMPLICATIONS_PLAN_POINTER_v0: formal/docs/release/EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0.md",
        "COSMO_EXTERNAL_IMPLICATIONS_ADJUDICATION_v0: NOT_YET_DISCHARGED_REFERENCE_ONLY",
        "COSMO_EXTERNAL_IMPLICATIONS_SCOPE_BOUNDARY_v0: BACKGROUND_REFERENCE_SURFACE_ONLY",
        "COSMO_EXTERNAL_IMPLICATIONS_LOCALIZATION_GATE_v0: PILOT_DOC_SCOPE_ONLY",
        "COSMO_EXTERNAL_IMPLICATIONS_NO_PROMOTION_v0: NO_RESULTS_TABLE_STATE_ROADMAP_OR_MATRIX_PROMOTION",
        "COSMO_EXTERNAL_IMPLICATIONS_BOUNDARY_v0: NO_CLAIM_OR_INEVITABILITY_PROMOTION",
        "COSMO_EXTERNAL_IMPLICATIONS_CONFIDENCE_TIERS_v0: TIER_1_HIGH;TIER_2_MEDIUM;TIER_3_EXPLORATORY",
        "COSMO_EXTERNAL_IMPLICATIONS_CITATION_MINIMUM_v0: SOURCE_URL_OR_DOI_AND_ACCESS_DATE_REQUIRED",
        "no external truth claim.",
        "formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "External implications pilot token drift: " + ", ".join(missing)


def test_cosmo_parent_target_references_external_implications_pilot() -> None:
    text = _read(PARENT_PATH)
    required_tokens = [
        "TARGET-COSMO-BG-EXTERNAL-HI-REFERENCE-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md",
        "formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target missing external implications pilot binding: " + ", ".join(missing)


def test_governance_suite_executes_external_implications_gate() -> None:
    suite_text = _read(SUITE_PATH)
    gate_relpath = "formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py"
    assert gate_relpath in suite_text, "governance_suite.ps1 must execute the external implications pilot gate."
