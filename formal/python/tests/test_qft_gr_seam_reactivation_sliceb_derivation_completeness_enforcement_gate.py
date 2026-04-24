from __future__ import annotations

import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
STANDARD_PATH = (
    RELEASE_DIR
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_ENFORCEMENT_STANDARD_v0.md"
)
SCIENCE_STANDARD_PATH = (
    RELEASE_DIR / "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ENFORCEMENT_STANDARD_v0.md"
)
OBJECTIVE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
DERIVATION_GATE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_COMPLETENESS_GATE_v0.md"
GOVERNANCE_SUITE_PATH = REPO_ROOT / "governance_suite.ps1"

INCREMENT_EXECUTION_PACKET_RE = re.compile(
    r"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT(\d+)_EXECUTION_PACKET_v0\.md$"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token_value(text: str, token_name: str) -> str:
    m = re.search(rf"`?{re.escape(token_name)}`?\s*:\s*([^\n]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1).strip().strip("`")


def _extract_token_int(text: str, token_name: str) -> int:
    raw = _extract_token_value(text, token_name)
    try:
        return int(raw)
    except ValueError as exc:
        raise AssertionError(f"Token `{token_name}` is not an integer: {raw}") from exc


def _increment_numbers_from_execution_packets() -> list[int]:
    numbers: list[int] = []
    for path in RELEASE_DIR.glob("QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT*_EXECUTION_PACKET_v0.md"):
        m = INCREMENT_EXECUTION_PACKET_RE.fullmatch(path.name)
        if m is None:
            continue
        numbers.append(int(m.group(1)))
    numbers.sort()
    return numbers


def test_sliceb_derivation_completeness_standard_is_pinned_and_wired() -> None:
    standard_text = _read(STANDARD_PATH)
    science_standard_text = _read(SCIENCE_STANDARD_PATH)
    objective_text = _read(OBJECTIVE_PATH)
    derivation_gate_text = _read(DERIVATION_GATE_PATH)
    suite_text = _read(GOVERNANCE_SUITE_PATH)

    required_tokens = [
        "QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_ENFORCEMENT_STATUS_v0: ACTIVE_HARD_BLOCK",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_ENFORCEMENT_START_INCREMENT_v0: 61",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_ADVANCEMENT_RULE_v0: NEXT_INCREMENT_JUSTIFICATION_REQUIRES_DERIVATION_COMPLETENESS_PASS",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_REQUIRED_TEST_v0: formal/python/tests/test_qft_gr_seam_reactivation_sliceb_derivation_completeness_enforcement_gate.py",
    ]
    for token in required_tokens:
        assert token in standard_text

    start_increment = _extract_token_int(
        standard_text, "QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_ENFORCEMENT_START_INCREMENT_v0"
    )
    assert start_increment >= 1

    for required_path in (
        "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md",
        "formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md",
        "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ENFORCEMENT_STANDARD_v0.md",
        "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_ENFORCEMENT_STANDARD_v0.md",
        "formal/python/tests/test_qft_gr_seam_reactivation_sliceb_derivation_completeness_enforcement_gate.py",
    ):
        assert required_path in standard_text

    assert "stress_energy_to_weak_curvature_handoff_strengthening" in objective_text
    assert "Derivation Completeness Gate v0" in derivation_gate_text
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ENFORCEMENT_STATUS_v0: ACTIVE_HARD_BLOCK"
        in science_standard_text
    )
    assert (
        "formal/python/tests/test_qft_gr_seam_reactivation_sliceb_derivation_completeness_enforcement_gate.py"
        in suite_text
    )


def test_sliceb_derivation_completeness_hard_block_for_enforced_increments() -> None:
    standard_text = _read(STANDARD_PATH)
    start_increment = _extract_token_int(
        standard_text, "QFT_GR_SEAM_REACTIVATION_SLICEB_DERIVATION_COMPLETENESS_ENFORCEMENT_START_INCREMENT_v0"
    )
    increments = _increment_numbers_from_execution_packets()
    assert increments, "No Slice B increment execution packets found."

    max_increment = max(increments)
    assert max_increment >= start_increment - 1, (
        "Derivation-completeness start increment is inconsistent with available increment history."
    )

    for increment in range(start_increment, max_increment + 1):
        decision_path = (
            RELEASE_DIR
            / f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_SEMANTIC_DELTA_DECISION_NOTE_v0.md"
        )
        packet_path = RELEASE_DIR / f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_EXECUTION_PACKET_v0.md"
        assess_path = RELEASE_DIR / f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_ASSESSMENT_NOTE_v0.md"
        science_note_path = (
            RELEASE_DIR / f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_SCIENCE_VALIDATION_NOTE_v0.md"
        )

        decision_text = _read(decision_path)
        packet_text = _read(packet_path)
        assess_text = _read(assess_path)
        science_note_text = _read(science_note_path)

        decision_required = (
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_OPEN_CONDITION_v0: "
            "SATISFIED_BY_BOUNDED_DERIVATION_COMPLETENESS_PASS"
        )
        packet_required = (
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_GATE_ENFORCEMENT_v0: "
            "REQUIRED_FOR_ADVANCEMENT"
        )
        assess_required = (
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_COMPLETENESS_GATE_STATUS_v0: "
            "ENFORCED"
        )
        assert decision_required in decision_text, (
            f"Increment{increment} decision note missing derivation open-condition token."
        )
        assert packet_required in packet_text, (
            f"Increment{increment} execution packet missing derivation gate enforcement token."
        )
        assert assess_required in assess_text, (
            f"Increment{increment} assessment note missing derivation-completeness gate status token."
        )
        assert (
            "formal/python/tests/test_qft_gr_seam_reactivation_sliceb_derivation_completeness_enforcement_gate.py"
            in packet_text
        ), (
            f"Increment{increment} execution packet focused ladder must include derivation-completeness gate path."
        )

        assert "## 7) Derivation Completeness" in science_note_text, (
            f"Increment{increment} science note missing derivation-completeness section."
        )
        science_required_tokens = [
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_EQUATION_TRACE_STATUS_v0: PRESENT",
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_ASSUMPTION_TRACE_STATUS_v0: PRESENT",
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_STEP_TRACE_STATUS_v0: PRESENT",
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_FALSIFIER_LINK_STATUS_v0: PRESENT",
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_REPRODUCIBILITY_STATUS_v0: PRESENT",
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_BOUNDARY_STATUS_v0: DECLARED",
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_COMPLETENESS_STATUS_v0: PASS_BOUNDED",
        ]
        for token in science_required_tokens:
            assert token in science_note_text, (
                f"Increment{increment} science note missing derivation-completeness token: {token}"
            )

        next_token_name = f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment + 1}_JUSTIFICATION_v0"
        next_token = _extract_token_value(assess_text, next_token_name)
        if next_token == "CONDITIONAL_YES_BOUNDED_ONLY":
            assert (
                f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_DERIVATION_COMPLETENESS_STATUS_v0: PASS_BOUNDED"
                in science_note_text
            ), (
                f"Increment{increment} cannot emit conditional-yes next-increment justification without derivation-completeness pass."
            )

