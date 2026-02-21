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


def test_cycle039_diagonalization_scope_derivation_surfaces_exist() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityIndexMapAgreementAssumptions",
        "theorem em_u1_cycle039_coupling_index_map_agrees_with_convention_v0",
        "em_u1_cycle039_build_diagonalization_scope_from_index_convention_v0",
        "theorem em_u1_cycle039_diagonalization_scope_consumer_from_index_convention_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-039 diagonalization derivation surfaces missing required token(s): " + ", ".join(missing)


def test_cycle039_uniqueness_guards_for_structure_and_theorems() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    structure_count = len(
        re.findall(r"^structure MaxwellToContinuityIndexMapAgreementAssumptions\b", text, flags=re.MULTILINE)
    )
    assert structure_count == 1, (
        "Cycle-039 agreement structure must appear exactly once "
        f"(found {structure_count})."
    )

    theorem_names = [
        "em_u1_cycle039_coupling_index_map_agrees_with_convention_v0",
        "em_u1_cycle039_build_diagonalization_scope_from_index_convention_v0",
        "em_u1_cycle039_diagonalization_scope_consumer_from_index_convention_v0",
    ]
    for theorem_name in theorem_names:
        count = len(re.findall(rf"^(?:theorem|def)\s+{re.escape(theorem_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-039 theorem `{theorem_name}` must appear exactly once (found {count})."


def test_cycle039_agreement_structure_is_not_vacuous() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"structure MaxwellToContinuityIndexMapAgreementAssumptions(?P<body>.*?)"
        r"\ntheorem em_u1_cycle039_coupling_index_map_agrees_with_convention_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-039 agreement structure block."
    block = block_match.group("body")
    assert ":= True" not in block, "Cycle-039 agreement structure must not collapse to `:= True`."
    assert "couplingIndexMapAgreesWithConvention" in block, (
        "Cycle-039 agreement structure must explicitly carry the coupling-index-map agreement field."
    )
    assert "agreementTag : String" in block, (
        "Cycle-039 agreement structure must include an explicit agreementTag for auditability."
    )


def test_cycle039_forbids_inline_trivialization_for_alignment_and_scope_builders() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    forbidden_patterns = [
        r"em_u1_cycle039_coupling_index_map_agrees_with_convention_v0\s*:=\s*by\s*trivial",
        r"em_u1_cycle039_coupling_index_map_agrees_with_convention_v0\s*:=\s*by\s*simp\b",
        r"em_u1_cycle039_coupling_index_map_agrees_with_convention_v0\s*:=\s*by\s*aesop\b",
        r"em_u1_cycle039_build_diagonalization_scope_from_index_convention_v0\s*:=\s*by\s*trivial",
        r"em_u1_cycle039_build_diagonalization_scope_from_index_convention_v0\s*:=\s*by\s*simp\b",
        r"em_u1_cycle039_build_diagonalization_scope_from_index_convention_v0\s*:=\s*by\s*aesop\b",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-039 alignment/scope-builder theorem surfaces must not be trivialized. "
        "Forbidden pattern(s): " + ", ".join(violations)
    )


def test_cycle039_scope_builder_derives_diagonalization_from_agreement_and_convention() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"(?:theorem|def) em_u1_cycle039_build_diagonalization_scope_from_index_convention_v0(?P<body>.*?)"
        r"\ntheorem em_u1_cycle039_diagonalization_scope_consumer_from_index_convention_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-039 diagonalization-scope builder theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle039_coupling_index_map_agrees_with_convention_v0" in block, (
        "Cycle-039 scope builder must derive diagonalization through the Cycle-039 agreement theorem surface."
    )
    assert "indexConvention.residualIndexMapDiagonal" in block, (
        "Cycle-039 scope builder must use the index-convention diagonalization witness."
    )
    assert "hDiagonalization := hCoupling.residualIndexMapDiagonal" not in block, (
        "Cycle-039 scope builder must not reintroduce direct raw-coupling diagonalization assignment."
    )


def test_cycle039_consumer_delegates_to_cycle037_consumer_surface() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle039_diagonalization_scope_consumer_from_index_convention_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-039 diagonalization consumer theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle039_build_diagonalization_scope_from_index_convention_v0" in block, (
        "Cycle-039 consumer theorem must build scope via the Cycle-039 scope-builder theorem surface."
    )
    assert "em_u1_cycle037_diagonalization_scope_explicit_consumer_v0" in block, (
        "Cycle-039 consumer theorem must delegate to the Cycle-037 scoped consumer surface."
    )
