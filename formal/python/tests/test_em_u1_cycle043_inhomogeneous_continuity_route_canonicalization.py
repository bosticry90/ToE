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


def test_cycle043_contract_promotes_derived_continuity_route_and_retires_cycle035_required_pair() -> None:
    registry_required = set(_em_registry_required_theorem_surfaces())
    discharge_required = set(_em_discharge_required_theorem_surfaces())

    required_now = {
        "em_u1_cycle043_build_continuity_scope_from_typed_route_and_inhomogeneous_statement_v0",
        "em_u1_cycle043_continuity_scope_consumer_from_typed_route_and_inhomogeneous_statement_v0",
        "em_u1_cycle043_continuity_scope_canonical_derived_route_v0",
    }
    retired_from_required = {
        "em_u1_cycle035_build_coupling_from_inhomogeneous_statement_v0",
        "em_u1_cycle035_maxwell_implies_continuity_from_inhomogeneous_statement_v0",
    }

    missing_registry = sorted(required_now - registry_required)
    missing_discharge = sorted(required_now - discharge_required)
    assert not missing_registry, (
        "Cycle-043 contract requires derived continuity route surfaces in EM registry. Missing: "
        + ", ".join(missing_registry)
    )
    assert not missing_discharge, (
        "Cycle-043 contract requires derived continuity route surfaces in EM discharge doc. Missing: "
        + ", ".join(missing_discharge)
    )

    forbidden_registry = sorted(retired_from_required & registry_required)
    forbidden_discharge = sorted(retired_from_required & discharge_required)
    assert not forbidden_registry, (
        "Cycle-043 must retire Cycle-035 required surfaces from EM registry. "
        "Forbidden still present: " + ", ".join(forbidden_registry)
    )
    assert not forbidden_discharge, (
        "Cycle-043 must retire Cycle-035 required surfaces from EM discharge doc required list. "
        "Forbidden still present: " + ", ".join(forbidden_discharge)
    )

    assert registry_required == discharge_required, (
        "Cycle-043 requires registry/discharge theorem-surface parity for EM."
    )


def test_cycle043_discharge_doc_pins_superseded_and_canonical_continuity_tokens() -> None:
    text = _read(EM_DISCHARGE_DOC_PATH)
    required_tokens = [
        "EM_PILLAR_CONTINUITY_SCOPE_ROUTE_SUPERSEDED_v0: "
        "Cycle-035_coupling_builder_and_maxwell_to_continuity_surface_SUPERSEDED_BY_Cycle-043_derived_route",
        "EM_PILLAR_CONTINUITY_SCOPE_CANONICAL_DERIVED_ROUTE_v0: "
        "Cycle-043_required_Cycle-035_continuity_route_NON_ADMISSIBLE_FOR_DISCHARGE",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-043 discharge-doc canonicalization token(s) missing: " + ", ".join(missing)


def test_cycle043_continuity_route_surfaces_exist_and_are_unique() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityContinuityDerivedFromTypedRouteAndInhomogeneousScopeAssumptions",
        "em_u1_cycle043_build_continuity_scope_from_typed_route_and_inhomogeneous_statement_v0",
        "theorem em_u1_cycle043_continuity_scope_consumer_from_typed_route_and_inhomogeneous_statement_v0",
        "theorem em_u1_cycle043_continuity_scope_canonical_derived_route_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-043 continuity surfaces missing required token(s): " + ", ".join(missing)

    theorem_names = [
        "em_u1_cycle043_build_continuity_scope_from_typed_route_and_inhomogeneous_statement_v0",
        "em_u1_cycle043_continuity_scope_consumer_from_typed_route_and_inhomogeneous_statement_v0",
        "em_u1_cycle043_continuity_scope_canonical_derived_route_v0",
    ]
    for theorem_name in theorem_names:
        count = len(re.findall(rf"^(?:theorem|def)\s+{re.escape(theorem_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-043 theorem `{theorem_name}` must appear exactly once (found {count})."


def test_cycle043_canonical_derived_continuity_route_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle043_continuity_scope_canonical_derived_route_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(indexConvention : MaxwellToContinuityResidualIndexConventionAssumptions\)\s*"
        r"\n\s*\(routeObj : MaxwellToContinuityRouteWithDdSubstepAttempt d F\)\s*"
        r"\n\s*\(hInhom\s*:\s*"
        r"\n\s*MaxwellToContinuityInhomogeneousSourceStatementAssumptions d F J\)\s*"
        r":\s*\n\s*continuityPredicate d J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-043 canonical derived-route theorem signature must remain exact."
    )


def test_cycle043_canonical_route_delegates_to_cycle043_consumer_and_forbids_cycle035_fallback_calls() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle043_continuity_scope_canonical_derived_route_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-043 canonical derived-route theorem block."
    block = block_match.group("body")

    assert "em_u1_cycle043_build_continuity_scope_from_typed_route_and_inhomogeneous_statement_v0" in block, (
        "Cycle-043 canonical theorem must build continuity scope through the Cycle-043 builder."
    )
    assert "em_u1_cycle043_continuity_scope_consumer_from_typed_route_and_inhomogeneous_statement_v0" in block, (
        "Cycle-043 canonical theorem must delegate to the Cycle-043 continuity consumer."
    )
    assert "em_u1_cycle035_build_coupling_from_inhomogeneous_statement_v0" not in block, (
        "Cycle-043 canonical theorem must not call the retired Cycle-035 coupling builder."
    )
    assert "em_u1_cycle035_maxwell_implies_continuity_from_inhomogeneous_statement_v0" not in block, (
        "Cycle-043 canonical theorem must not call the retired Cycle-035 Maxwell->continuity theorem."
    )


def test_cycle043_continuity_consumer_delegates_to_cycle031_continuity_surface() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle043_continuity_scope_consumer_from_typed_route_and_inhomogeneous_statement_v0(?P<body>.*?)"
        r"\ntheorem em_u1_cycle043_continuity_scope_canonical_derived_route_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-043 continuity-consumer theorem block."
    block = block_match.group("body")

    assert "em_u1_cycle031_consume_typed_route_object_for_continuity_v0" in block, (
        "Cycle-043 continuity consumer must delegate through the Cycle-031 continuity consumer surface."
    )
    assert "scope.routeObj.ddZero" not in block, (
        "Cycle-043 continuity consumer must not bypass Cycle-031 by reading scope.routeObj.ddZero directly."
    )


def test_cycle043_builder_delegates_to_cycle044_canonical_diagonal_residual_route() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"def em_u1_cycle043_build_continuity_scope_from_typed_route_and_inhomogeneous_statement_v0(?P<body>.*?)"
        r"\ntheorem em_u1_cycle043_continuity_scope_consumer_from_typed_route_and_inhomogeneous_statement_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-043 continuity-scope builder block."
    block = block_match.group("body")

    assert "em_u1_cycle044_diagonal_residual_scope_canonical_derived_route_v0" in block, (
        "Cycle-043 builder must delegate through Cycle-044 canonical diagonal-residual route."
    )
    assert "em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0" not in block, (
        "Cycle-043 builder must not call Cycle-036 directly after Cycle-044 canonicalization."
    )
