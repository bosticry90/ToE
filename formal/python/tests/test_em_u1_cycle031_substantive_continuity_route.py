from __future__ import annotations

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
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_cycle031_lean_surfaces_exist() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def continuityResidual",
        "def continuityPredicate",
        "structure PotentialFieldStrengthBridgeAssumptions",
        "def fieldStrengthFromPotentialForms",
        "structure MaxwellToContinuityCurrentCouplingAssumptions",
        "theorem em_u1_cycle031_define_continuity_residual_v0",
        "theorem em_u1_cycle031_continuity_predicate_is_residual_zero_v0",
        "em_u1_cycle031_bridge_assumption_object_intro_v0",
        "theorem em_u1_cycle031_bridge_assumption_object_export_v0",
        "theorem em_u1_cycle031_consume_typed_route_object_for_continuity_v0",
        "theorem em_u1_cycle031_maxwell_implies_continuity_for_current_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-031 Lean surfaces missing required token(s): " + ", ".join(missing)


def test_cycle031_replaces_vacuous_continuity_and_placeholder_forms_bridge() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert (
        "def continuityPredicate (_J : CovariantCurrent) : Prop := True" not in text
    ), "continuityPredicate must not remain vacuous (`:= True`)."
    assert (
        "def fieldStrengthFromPotentialForms (_A : GaugePotential) : FieldStrength :=" not in text
    ), "fieldStrengthFromPotentialForms must not remain the old placeholder signature."
    assert (
        re.search(
            r"def fieldStrengthFromPotentialForms[\s\S]*?\{\s*component\s*:=\s*fun\s+_\s+_\s*=>\s*0\s*\}",
            text,
        )
        is None
    ), "fieldStrengthFromPotentialForms must not return the zero placeholder field."


def test_cycle031_uniqueness_guards_for_substantive_definitions() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert len(re.findall(r"^def continuityResidual\b", text, flags=re.MULTILINE)) == 1, (
        "Cycle-031 hardening requires exactly one `def continuityResidual`."
    )
    assert len(re.findall(r"^def continuityPredicate\b", text, flags=re.MULTILINE)) == 1, (
        "Cycle-031 hardening requires exactly one `def continuityPredicate`."
    )
    assert len(re.findall(r"^def fieldStrengthFromPotentialForms\b", text, flags=re.MULTILINE)) == 1, (
        "Cycle-031 hardening requires exactly one `def fieldStrengthFromPotentialForms`."
    )


def test_cycle031_forbids_legacy_continuity_predicate_call_shape() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert re.search(r"\bcontinuityPredicate\s*\{", text) is None, (
        "Legacy one-argument `continuityPredicate { ... }` call-shape must not reappear."
    )


def test_cycle031_continuity_consumer_theorem_uses_typed_route_and_coupling() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle031_consume_typed_route_object_for_continuity_v0(?P<body>.*?)"
        r"\ntheorem em_u1_cycle031_maxwell_implies_continuity_for_current_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-031 continuity-consumer theorem block."
    block = block_match.group("body")
    assert "MaxwellToContinuityRouteWithDdSubstepAttempt d F" in block, (
        "Cycle-031 continuity theorem must consume the typed route object."
    )
    assert "MaxwellToContinuityCurrentCouplingAssumptions d F J" in block, (
        "Cycle-031 continuity theorem must keep Maxwell/source coupling explicit."
    )
    assert "hCoupling.divergenceCurrentFromDd μ" in block, (
        "Cycle-031 continuity theorem must use coupling to map continuity residual from DD terms."
    )
    assert "routeObj.ddZero μ μ" in block, (
        "Cycle-031 continuity theorem must use typed route DD=0 field access."
    )


def test_cycle031_continuity_consumer_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle031_consume_typed_route_object_for_continuity_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(routeObj : MaxwellToContinuityRouteWithDdSubstepAttempt d F\)\s*"
        r"\n\s*\(hCoupling : MaxwellToContinuityCurrentCouplingAssumptions d F J\)\s*"
        r":\s*\n\s*continuityPredicate d J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-031 continuity-consumer theorem signature must remain exact."
    )


def test_cycle031_maxwell_implies_continuity_theorem_uses_cycle030_constructor() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle031_maxwell_implies_continuity_for_current_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-031 Maxwell->continuity theorem block."
    block = block_match.group("body")
    assert "DoubleDivergenceSmoothnessLaneAssumptions d F" in block, (
        "Cycle-031 theorem must keep smoothness assumptions explicit."
    )
    assert "em_u1_cycle030_build_typed_route_consumer_entrypoint_v0" in block, (
        "Cycle-031 theorem must build typed route via Cycle-030 constructor."
    )
    assert "em_u1_cycle031_consume_typed_route_object_for_continuity_v0" in block, (
        "Cycle-031 theorem must consume typed route object through the Cycle-031 continuity surface."
    )


def test_cycle031_maxwell_implies_continuity_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle031_maxwell_implies_continuity_for_current_v0\s*"
        r"\n\s*\(consumerPkg : MaxwellToContinuityTypedRouteConsumerAttemptPackage\)\s*"
        r"\n\s*\(hConsumer : maxwellToContinuityTypedRouteConsumerAttemptHarness consumerPkg\)\s*"
        r"\n\s*\(routePkg : MaxwellToContinuityRouteClosureAttemptPackage\)\s*"
        r"\n\s*\(subroutePkg : MaxwellToContinuityDdSubrouteCompositionAttemptPackage\)\s*"
        r"\n\s*\(hRoute : maxwellToContinuityRouteClosureAttemptHarness routePkg\)\s*"
        r"\n\s*\(hSubroute : maxwellToContinuityDdSubrouteCompositionAttemptHarness subroutePkg\)\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(hSmooth : DoubleDivergenceSmoothnessLaneAssumptions d F\)\s*"
        r"\n\s*\(hFantisym : ∀ α β, F.component α β = -F.component β α\)\s*"
        r"\n\s*\(hCoupling : MaxwellToContinuityCurrentCouplingAssumptions d F J\)\s*"
        r":\s*\n\s*continuityPredicate d J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-031 Maxwell->continuity theorem signature must remain exact."
    )
