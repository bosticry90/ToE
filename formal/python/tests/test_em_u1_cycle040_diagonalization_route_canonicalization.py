from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
EM_DISCHARGE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_DISCHARGE_REGISTRY_v0.json"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _em_registry_required_theorem_surfaces() -> list[str]:
    registry = _read_json(REGISTRY_PATH)
    pillars = list(registry.get("pillars", []))
    em = [entry for entry in pillars if entry.get("pillar_key") == "EM"]
    assert len(em) == 1, "Registry must contain exactly one EM pillar entry."
    required = list(em[0].get("required_theorem_surfaces", []))
    assert required, "EM required_theorem_surfaces must be non-empty."
    return required


def _em_discharge_required_theorem_surfaces() -> list[str]:
    text = _read(EM_DISCHARGE_DOC_PATH)
    block_match = re.search(
        r"EM full-discharge completion mechanics \(v0\):(?P<body>.*?)"
        r"- `EM_PILLAR_FULL_DISCHARGE_CRITERIA_ROW_02_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate EM full-discharge completion mechanics theorem-surface block."
    return re.findall(r"`(em_u1_[^`]+)`", block_match.group("body"))


def test_cycle040_contract_promotes_derived_diagonalization_route_and_retires_cycle037_required_pair() -> None:
    registry_required = set(_em_registry_required_theorem_surfaces())
    discharge_required = set(_em_discharge_required_theorem_surfaces())

    required_now = {
        "em_u1_cycle040_diagonalization_scope_canonical_derived_route_v0",
        "em_u1_cycle046_build_diagonalization_scope_from_index_convention_route_v0",
        "em_u1_cycle046_diagonalization_scope_consumer_from_index_convention_route_v0",
        "em_u1_cycle046_diagonalization_scope_canonical_derived_route_v0",
    }
    retired_from_required = {
        "em_u1_cycle037_build_diagonalization_scope_assumptions_v0",
        "em_u1_cycle037_diagonalization_scope_explicit_consumer_v0",
    }

    missing_registry = sorted(required_now - registry_required)
    missing_discharge = sorted(required_now - discharge_required)
    assert not missing_registry, (
        "Cycle-040 contract requires derived diagonalization route surfaces in EM registry. Missing: "
        + ", ".join(missing_registry)
    )
    assert not missing_discharge, (
        "Cycle-040 contract requires derived diagonalization route surfaces in EM discharge doc. Missing: "
        + ", ".join(missing_discharge)
    )

    forbidden_registry = sorted(retired_from_required & registry_required)
    forbidden_discharge = sorted(retired_from_required & discharge_required)
    assert not forbidden_registry, (
        "Cycle-040 must retire Cycle-037 diagonalization required surfaces from EM registry. "
        "Forbidden still present: " + ", ".join(forbidden_registry)
    )
    assert not forbidden_discharge, (
        "Cycle-040 must retire Cycle-037 diagonalization required surfaces from EM discharge doc required list. "
        "Forbidden still present: " + ", ".join(forbidden_discharge)
    )

    assert registry_required == discharge_required, (
        "Cycle-040 requires registry/discharge theorem-surface parity for EM."
    )


def test_cycle040_discharge_doc_pins_superseded_and_canonical_diagonalization_tokens() -> None:
    text = _read(EM_DISCHARGE_DOC_PATH)
    required_tokens = [
        "EM_PILLAR_DIAGONALIZATION_SCOPE_ROUTE_SUPERSEDED_v0: "
        "Cycle-037_diagonalization_scope_builder_consumer_SUPERSEDED_BY_Cycle-039_derived_route",
        "EM_PILLAR_DIAGONALIZATION_SCOPE_CANONICAL_DERIVED_ROUTE_v0: "
        "Cycle-039_required_Cycle-037_diagonalization_route_NON_ADMISSIBLE_FOR_DISCHARGE",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-040 discharge-doc canonicalization token(s) missing: " + ", ".join(missing)


def test_cycle040_canonical_derived_route_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle040_diagonalization_scope_canonical_derived_route_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(indexConvention : MaxwellToContinuityResidualIndexConventionAssumptions\)\s*"
        r"\n\s*\(hCoupling : MaxwellToContinuityCurrentCouplingAssumptions d F J\)\s*"
        r"\n\s*\(hAgreement :"
        r"\n\s*MaxwellToContinuityIndexMapAgreementAssumptions d F J indexConvention hCoupling\)\s*"
        r":\s*\n\s*∀ μ, hCoupling\.residualIndexMap μ = μ\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-040 canonical derived-route theorem signature must remain exact."
    )


def test_cycle040_canonical_route_delegates_to_cycle046_and_forbids_cycle037_cycle039_fallback_calls() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle040_diagonalization_scope_canonical_derived_route_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-040 canonical derived-route theorem block."
    block = block_match.group("body")

    assert "em_u1_cycle046_diagonalization_scope_canonical_derived_route_v0" in block, (
        "Cycle-040 canonical theorem must delegate to Cycle-046 canonical diagonalization route."
    )
    assert "em_u1_cycle037_build_diagonalization_scope_assumptions_v0" not in block, (
        "Cycle-040 canonical theorem must not call the retained Cycle-037 diagonalization builder."
    )
    assert "em_u1_cycle037_diagonalization_scope_explicit_consumer_v0" not in block, (
        "Cycle-040 canonical theorem must not call the retained Cycle-037 diagonalization consumer directly."
    )
    assert "em_u1_cycle039_diagonalization_scope_consumer_from_index_convention_v0" not in block, (
        "Cycle-040 canonical theorem must not call Cycle-039 consumer directly after Cycle-046 canonicalization."
    )
