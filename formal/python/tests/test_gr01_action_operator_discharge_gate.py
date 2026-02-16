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
LEAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01ActionToOperatorDiscrete.lean"
)
DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr01_bridge_witness_constructor_tokens_exist() -> None:
    text = _read(LEAN_PATH)
    required_tokens = [
        "theorem mk_ELImpliesDiscretePoissonResidual_from_bridge_v0",
        "theorem actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_v0",
    ]
    for token in required_tokens:
        assert token in text, f"Missing required GR01 bridge/witness token: {token}"


def test_gr01_action_to_operator_adjudication_flip_gated_by_constructor() -> None:
    doc_text = _read(DOC_PATH)
    lean_text = _read(LEAN_PATH)

    m = re.search(
        r"ACTION_TO_OPERATOR_ADJUDICATION:\s*(NOT_YET_DISCHARGED|DISCHARGED_v0_DISCRETE)",
        doc_text,
    )
    assert m is not None, "Missing ACTION_TO_OPERATOR_ADJUDICATION token line in derivation target doc."
    adjudication = m.group(1)

    if adjudication == "DISCHARGED_v0_DISCRETE":
        required_tokens = [
            "theorem mk_ELImpliesDiscretePoissonResidual_from_bridge_v0",
            "theorem actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_v0",
        ]
        missing = [tok for tok in required_tokens if tok not in lean_text]
        assert not missing, (
            "Cannot set ACTION_TO_OPERATOR_ADJUDICATION to DISCHARGED_v0_DISCRETE without "
            "the required witness-constructor theorem tokens in GR01ActionToOperatorDiscrete.lean: "
            + ", ".join(missing)
        )

