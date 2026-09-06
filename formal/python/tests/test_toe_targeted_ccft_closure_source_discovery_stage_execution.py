from __future__ import annotations

from formal.python.tools.toe_targeted_ccft_closure_source_discovery_stage_execution import (
    gate_text,
)


BRANCH_TERMS = {
    "CP_NLSE": ["CP-NLSE", "UCFF"],
    "LCRD_V3": ["LCRD-v3", "rotor-curvature"],
}
CONTRACT_TERMS = ["initial condition", "parameter range", "invariant"]


def test_two_axis_gate_accepts_branch_and_contract_term() -> None:
    result = gate_text(
        "The CP-NLSE initial condition is periodic.",
        branch_terms=BRANCH_TERMS,
        contract_terms=CONTRACT_TERMS,
    )
    assert result is not None
    assert result["branch_term_hits"] == {"CP_NLSE": ["CP-NLSE"]}
    assert result["contract_term_hits"] == ["initial condition"]


def test_gate_rejects_branch_only_and_contract_only_text() -> None:
    assert (
        gate_text(
            "This paragraph mentions CP-NLSE without a contract.",
            branch_terms=BRANCH_TERMS,
            contract_terms=CONTRACT_TERMS,
        )
        is None
    )
    assert (
        gate_text(
            "The parameter range is finite.",
            branch_terms=BRANCH_TERMS,
            contract_terms=CONTRACT_TERMS,
        )
        is None
    )


def test_structural_gate_remains_branch_bound() -> None:
    accepted = gate_text(
        "LCRD rotor-curvature fields require a constitutive map.",
        branch_terms=BRANCH_TERMS,
        contract_terms=CONTRACT_TERMS,
    )
    assert accepted is not None
    assert "LCRD_ROTOR_CURVATURE_CONSTITUTIVE_OR_COARSE_GRAINING_MAP" in accepted[
        "structural_signature_hits"
    ]
    assert (
        gate_text(
            "A generic rotor field requires a constitutive map.",
            branch_terms=BRANCH_TERMS,
            contract_terms=CONTRACT_TERMS,
        )
        is None
    )


def test_gate_records_deterministic_line_locations() -> None:
    result = gate_text(
        "header\nCP-NLSE\ninitial condition\nCP-NLSE\n",
        branch_terms=BRANCH_TERMS,
        contract_terms=CONTRACT_TERMS,
    )
    assert result is not None
    assert result["term_line_locations"]["CP-NLSE"] == [2, 4]
    assert result["term_line_locations"]["initial condition"] == [3]
