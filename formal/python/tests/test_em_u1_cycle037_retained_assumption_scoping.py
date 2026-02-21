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


def test_cycle037_retained_assumption_scope_surfaces_exist() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityBridgeScopeAssumptions",
        "structure MaxwellToContinuitySmoothnessScopeAssumptions",
        "structure MaxwellToContinuityDiagonalizationScopeAssumptions",
        "em_u1_cycle037_build_bridge_scope_assumptions_v0",
        "theorem em_u1_cycle037_bridge_scope_explicit_consumer_v0",
        "em_u1_cycle037_build_smoothness_scope_assumptions_v0",
        "theorem em_u1_cycle037_smoothness_scope_explicit_consumer_v0",
        "em_u1_cycle037_build_diagonalization_scope_assumptions_v0",
        "theorem em_u1_cycle037_diagonalization_scope_explicit_consumer_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-037 retained-assumption scoping surfaces missing required token(s): " + ", ".join(missing)


def test_cycle037_uniqueness_guards_for_structures_and_theorems() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    structure_names = [
        "MaxwellToContinuityBridgeScopeAssumptions",
        "MaxwellToContinuitySmoothnessScopeAssumptions",
        "MaxwellToContinuityDiagonalizationScopeAssumptions",
    ]
    for structure_name in structure_names:
        count = len(re.findall(rf"^structure\s+{re.escape(structure_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-037 structure `{structure_name}` must appear exactly once (found {count})."

    theorem_names = [
        "em_u1_cycle037_build_bridge_scope_assumptions_v0",
        "em_u1_cycle037_bridge_scope_explicit_consumer_v0",
        "em_u1_cycle037_build_smoothness_scope_assumptions_v0",
        "em_u1_cycle037_smoothness_scope_explicit_consumer_v0",
        "em_u1_cycle037_build_diagonalization_scope_assumptions_v0",
        "em_u1_cycle037_diagonalization_scope_explicit_consumer_v0",
    ]
    for theorem_name in theorem_names:
        count = len(re.findall(rf"^(?:theorem|def)\s+{re.escape(theorem_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-037 theorem `{theorem_name}` must appear exactly once (found {count})."


def test_cycle037_scope_tags_are_non_empty_and_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    forbidden_patterns = [
        r"scopeTag\s*:=\s*\"\"",
        r"consumerSurfaceTag\s*:=\s*\"\"",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-037 scope tags must be non-empty and pinned. Forbidden pattern(s): " + ", ".join(violations)
    )

    expected_tags = [
        'scopeTag := "cycle37-retained-bridge-scope"',
        'consumerSurfaceTag := "em_u1_cycle031_bridge_assumption_object_export_v0"',
        'scopeTag := "cycle37-retained-smoothness-scope"',
        'consumerSurfaceTag := "em_u1_cycle027_double_divergence_zero_via_built_binding_v0"',
        'scopeTag := "cycle37-retained-diagonalization-scope"',
        'consumerSurfaceTag := "em_u1_cycle032_coupling_map_diagonalization_v0"',
    ]
    missing = [tag for tag in expected_tags if tag not in text]
    assert not missing, "Cycle-037 pinned scope/consumer tag(s) missing: " + ", ".join(missing)


def test_cycle037_bridge_scope_consumer_delegates_to_cycle031_surface() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle037_bridge_scope_explicit_consumer_v0(?P<body>.*?)"
        r"\n(?:theorem|def) em_u1_cycle037_build_smoothness_scope_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-037 bridge-scope consumer theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle031_bridge_assumption_object_export_v0" in block, (
        "Cycle-037 bridge-scope consumer theorem must delegate to Cycle-031 bridge export surface."
    )


def test_cycle037_smoothness_scope_consumer_delegates_to_cycle027_surface() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle037_smoothness_scope_explicit_consumer_v0(?P<body>.*?)"
        r"\n(?:theorem|def) em_u1_cycle037_build_diagonalization_scope_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-037 smoothness-scope consumer theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle027_double_divergence_zero_via_built_binding_v0" in block, (
        "Cycle-037 smoothness-scope consumer theorem must delegate to Cycle-027 DD=0 surface."
    )


def test_cycle037_diagonalization_scope_consumer_delegates_to_cycle032_surface() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle037_diagonalization_scope_explicit_consumer_v0(?P<body>.*?)"
        r"\nstructure MaxwellToContinuityIndexMapAgreementAssumptions",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-037 diagonalization-scope consumer theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle032_coupling_map_diagonalization_v0" in block, (
        "Cycle-037 diagonalization-scope consumer theorem must delegate to Cycle-032 diagonalization surface."
    )


def test_cycle037_consumers_do_not_accept_ambient_raw_retained_assumptions() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)

    bridge_block_match = re.search(
        r"theorem em_u1_cycle037_bridge_scope_explicit_consumer_v0(?P<body>.*?)"
        r"\n(?:theorem|def) em_u1_cycle037_build_smoothness_scope_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert bridge_block_match is not None, "Could not isolate Cycle-037 bridge-scope consumer theorem block."
    bridge_block = bridge_block_match.group("body")
    assert "(scope : MaxwellToContinuityBridgeScopeAssumptions)" in bridge_block, (
        "Cycle-037 bridge consumer must consume the scoped bridge object."
    )
    assert re.search(r"\(bridge\s*:\s*PotentialFieldStrengthBridgeAssumptions\)", bridge_block) is None, (
        "Cycle-037 bridge consumer must not accept ambient raw bridge assumptions."
    )

    smoothness_block_match = re.search(
        r"theorem em_u1_cycle037_smoothness_scope_explicit_consumer_v0(?P<body>.*?)"
        r"\n(?:theorem|def) em_u1_cycle037_build_diagonalization_scope_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert smoothness_block_match is not None, "Could not isolate Cycle-037 smoothness-scope consumer theorem block."
    smoothness_block = smoothness_block_match.group("body")
    assert "(scope : MaxwellToContinuitySmoothnessScopeAssumptions d F)" in smoothness_block, (
        "Cycle-037 smoothness consumer must consume the scoped smoothness object."
    )
    assert re.search(
        r"\(hSmooth\s*:\s*DoubleDivergenceSmoothnessLaneAssumptions d F\)", smoothness_block
    ) is None, "Cycle-037 smoothness consumer must not accept ambient raw smoothness assumptions."

    diagonalization_block_match = re.search(
        r"theorem em_u1_cycle037_diagonalization_scope_explicit_consumer_v0(?P<body>.*?)"
        r"\nstructure MaxwellToContinuityIndexMapAgreementAssumptions",
        text,
        flags=re.DOTALL,
    )
    assert diagonalization_block_match is not None, (
        "Could not isolate Cycle-037 diagonalization-scope consumer theorem block."
    )
    diagonalization_block = diagonalization_block_match.group("body")
    assert "(scope : MaxwellToContinuityDiagonalizationScopeAssumptions d F J)" in diagonalization_block, (
        "Cycle-037 diagonalization consumer must consume the scoped diagonalization object."
    )
    assert re.search(
        r"\(hCoupling\s*:\s*MaxwellToContinuityCurrentCouplingAssumptions d F J\)", diagonalization_block
    ) is None, "Cycle-037 diagonalization consumer must not accept ambient raw coupling assumptions."
    assert "residualIndexMapDiagonal" not in diagonalization_block, (
        "Cycle-037 diagonalization consumer must not read `residualIndexMapDiagonal` directly."
    )


def test_cycle037_forbids_post_scope_reintroduction_of_ambient_retained_assumption_tokens() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert re.search(
        r"^(?:theorem|def)\s+em_u1_cycle037_build_bridge_scope_assumptions_v0\b",
        text,
        flags=re.MULTILINE,
    ) is not None
    assert "theorem em_u1_field_strength_invariance_under_contract_assumptions_v0" in text

    split = re.split(
        r"^(?:theorem|def)\s+em_u1_cycle037_build_bridge_scope_assumptions_v0\b",
        text,
        maxsplit=1,
        flags=re.MULTILINE,
    )
    assert len(split) == 2, "Could not split text at Cycle-037 bridge-scope builder declaration."
    pre_cycle037, cycle037_and_after = split
    cycle037_block, post_cycle037 = cycle037_and_after.split(
        "theorem em_u1_field_strength_invariance_under_contract_assumptions_v0", 1
    )
    _ = pre_cycle037
    _ = cycle037_block

    forbidden_post_scope_tokens = [
        "PotentialFieldStrengthBridgeAssumptions",
        "DoubleDivergenceSmoothnessLaneAssumptions",
        "residualIndexMapDiagonal",
    ]
    violations = [token for token in forbidden_post_scope_tokens if token in post_cycle037]
    assert not violations, (
        "Post-Cycle-037 region must not reintroduce ambient retained-assumption tokens. "
        "Forbidden token(s): " + ", ".join(violations)
    )
