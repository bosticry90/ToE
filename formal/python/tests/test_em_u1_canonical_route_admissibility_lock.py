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


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _em_registry_required_theorem_surfaces() -> set[str]:
    registry = _read_json(REGISTRY_PATH)
    pillars = list(registry.get("pillars", []))
    em = [entry for entry in pillars if entry.get("pillar_key") == "EM"]
    assert len(em) == 1, "Registry must contain exactly one EM pillar entry."
    required = set(em[0].get("required_theorem_surfaces", []))
    assert required, "EM required_theorem_surfaces must be non-empty."
    return required


def _em_discharge_required_theorem_surfaces() -> set[str]:
    text = _read(EM_DISCHARGE_DOC_PATH)
    block_match = re.search(
        r"EM full-discharge completion mechanics \(v0\):(?P<body>.*?)"
        r"- `EM_PILLAR_FULL_DISCHARGE_CRITERIA_ROW_02_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate EM full-discharge completion mechanics theorem-surface block."
    return set(re.findall(r"`(em_u1_[^`]+)`", block_match.group("body")))


def test_em_canonical_route_admissibility_lock_for_cycle040_041_042_043_044_045_046() -> None:
    registry_required = _em_registry_required_theorem_surfaces()
    discharge_required = _em_discharge_required_theorem_surfaces()

    assert registry_required == discharge_required, (
        "EM canonical route lock requires registry/discharge required-surface parity."
    )

    # Governance lock: Cycle-037 required-surface retirement is irreversible; 040/041/042/043/044/045/046 are canonical.
    canonical_required = {
        "em_u1_cycle040_diagonalization_scope_canonical_derived_route_v0",
        "em_u1_cycle041_build_smoothness_scope_from_typed_route_v0",
        "em_u1_cycle041_smoothness_scope_consumer_from_typed_route_v0",
        "em_u1_cycle041_smoothness_scope_canonical_derived_route_v0",
        "em_u1_cycle042_build_bridge_scope_from_intro_surface_v0",
        "em_u1_cycle042_bridge_scope_consumer_from_intro_surface_v0",
        "em_u1_cycle042_bridge_scope_canonical_derived_route_v0",
        "em_u1_cycle043_build_continuity_scope_from_typed_route_and_inhomogeneous_statement_v0",
        "em_u1_cycle043_continuity_scope_consumer_from_typed_route_and_inhomogeneous_statement_v0",
        "em_u1_cycle043_continuity_scope_canonical_derived_route_v0",
        "em_u1_cycle044_build_diagonal_residual_scope_from_inhomogeneous_statement_v0",
        "em_u1_cycle044_diagonal_residual_scope_consumer_from_inhomogeneous_statement_v0",
        "em_u1_cycle044_diagonal_residual_scope_canonical_derived_route_v0",
        "em_u1_cycle045_build_typed_route_spine_scope_from_subroute_chain_v0",
        "em_u1_cycle045_typed_route_spine_scope_consumer_from_subroute_chain_v0",
        "em_u1_cycle045_typed_route_spine_scope_canonical_derived_route_v0",
        "em_u1_cycle046_build_diagonalization_scope_from_index_convention_route_v0",
        "em_u1_cycle046_diagonalization_scope_consumer_from_index_convention_route_v0",
        "em_u1_cycle046_diagonalization_scope_canonical_derived_route_v0",
    }
    missing = sorted(canonical_required - registry_required)
    assert not missing, (
        "EM canonical route lock missing required Cycle-040/041/042/043/044/045/046 surfaces: "
        + ", ".join(missing)
    )

    forbidden_cycle037_required = sorted(surface for surface in registry_required if "em_u1_cycle037_" in surface)
    assert not forbidden_cycle037_required, (
        "EM canonical route lock forbids Cycle-037 surfaces in required sets. Found: "
        + ", ".join(forbidden_cycle037_required)
    )
