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
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
OUTPUT_DIR = REPO_ROOT / "formal" / "output"
STANDARD_PATH = (
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


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


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


def _assert_science_validation_note_content(increment: int, note_text: str) -> str:
    required_sections = [
        "## 1) Equation Surface",
        "## 2) Units and Dimensions",
        "## 3) Falsifier and Threshold",
        "## 4) Measurement Result",
        "## 5) Reproducibility",
        "## 6) Non-Claim Boundary",
    ]
    for section in required_sections:
        assert section in note_text, f"Increment{increment} science note missing section: {section}"

    token_prefix = f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}"
    required_tokens = [
        f"{token_prefix}_SCIENCE_EQUATION_STATUS_v0: PRESENT",
        f"{token_prefix}_DIMENSIONAL_CONSISTENCY_STATUS_v0: PASS",
        f"{token_prefix}_FALSIFIER_STATUS_v0: DECLARED",
        f"{token_prefix}_NUMERIC_MEASUREMENT_STATUS_v0: MEASURED",
    ]
    for token in required_tokens:
        assert token in note_text, f"Increment{increment} science note missing token: {token}"

    # Require at least one explicit equation-style surface line and at least one physics symbol.
    assert "=" in note_text, f"Increment{increment} science note must contain at least one equation with '='."
    lowered = note_text.lower()
    assert any(sym in lowered for sym in ("rho", "phi", "nabla", "curvature", "stress")), (
        f"Increment{increment} science note must include at least one physics symbol/context keyword."
    )

    # Require a units table surface.
    assert "| symbol |" in lowered, f"Increment{increment} science note must include a units table with `symbol`."
    assert ("| units |" in lowered) or ("| unit |" in lowered), (
        f"Increment{increment} science note must include a units table with `unit(s)`."
    )

    assert f"{token_prefix}_SCIENCE_REPRO_COMMAND_v0" in note_text, (
        f"Increment{increment} science note must include reproducibility command token."
    )
    artifact_token = f"{token_prefix}_SCIENCE_ARTIFACT_PATH_v0"
    return _extract_token_value(note_text, artifact_token)


def _assert_science_artifact_schema(increment: int, artifact_rel_path: str) -> dict:
    expected_rel = f"formal/output/qft_gr_seam_reactivation_sliceb_increment{increment}_science_validation_v0.json"
    assert artifact_rel_path == expected_rel, (
        f"Increment{increment} science artifact path mismatch. Expected `{expected_rel}`, got `{artifact_rel_path}`."
    )
    artifact_path = REPO_ROOT / artifact_rel_path
    assert artifact_path.exists(), f"Increment{increment} science artifact missing: {artifact_path}"
    artifact = _read_json(artifact_path)

    assert artifact.get("increment") == increment
    assert isinstance(artifact.get("equation_id"), str) and artifact["equation_id"].strip()
    assert isinstance(artifact.get("observed_value"), (int, float))
    assert isinstance(artifact.get("threshold_value"), (int, float))
    assert artifact.get("comparison") in {"<=", ">=", "<", ">", "==", "abs<="}
    assert isinstance(artifact.get("units"), str) and artifact["units"].strip()
    assert isinstance(artifact.get("passes_threshold"), bool)
    return artifact


def test_sliceb_science_first_standard_is_pinned_and_wired() -> None:
    standard_text = _read(STANDARD_PATH)
    objective_text = _read(OBJECTIVE_PATH)
    derivation_gate_text = _read(DERIVATION_GATE_PATH)
    suite_text = _read(GOVERNANCE_SUITE_PATH)

    required_tokens = [
        "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ENFORCEMENT_STATUS_v0: ACTIVE_HARD_BLOCK",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ENFORCEMENT_START_INCREMENT_v0: 50",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ADVANCEMENT_RULE_v0: NEXT_INCREMENT_JUSTIFICATION_REQUIRES_SCIENCE_ARTIFACT_PASS",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_REQUIRED_TEST_v0: formal/python/tests/test_qft_gr_seam_reactivation_sliceb_science_first_enforcement_gate.py",
    ]
    for token in required_tokens:
        assert token in standard_text

    start_increment = _extract_token_int(
        standard_text, "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ENFORCEMENT_START_INCREMENT_v0"
    )
    assert start_increment >= 1

    for required_path in (
        "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md",
        "formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md",
        "formal/python/tests/test_qft_gr_seam_reactivation_sliceb_science_first_enforcement_gate.py",
    ):
        assert required_path in standard_text

    assert "stress_energy_to_weak_curvature_handoff_strengthening" in objective_text
    assert "Derivation Completeness Gate v0" in derivation_gate_text
    assert "formal/python/tests/test_qft_gr_seam_reactivation_sliceb_science_first_enforcement_gate.py" in suite_text


def test_sliceb_science_first_hard_block_for_enforced_increments() -> None:
    standard_text = _read(STANDARD_PATH)
    start_increment = _extract_token_int(
        standard_text, "QFT_GR_SEAM_REACTIVATION_SLICEB_SCIENCE_FIRST_ENFORCEMENT_START_INCREMENT_v0"
    )
    increments = _increment_numbers_from_execution_packets()
    assert increments, "No Slice B increment execution packets found."

    max_increment = max(increments)
    assert max_increment >= start_increment - 1, (
        "Science-first start increment is inconsistent with available increment history."
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
        note_text = _read(science_note_path)

        decision_required = (
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_SCIENCE_OPEN_CONDITION_v0: "
            "SATISFIED_BY_PHYSICS_EVIDENCE_ARTIFACT_PASS"
        )
        packet_required = (
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_SCIENCE_GATE_ENFORCEMENT_v0: "
            "REQUIRED_FOR_ADVANCEMENT"
        )
        assess_required = (
            f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment}_SCIENCE_GATE_STATUS_v0: "
            "ENFORCED"
        )
        assert decision_required in decision_text, f"Increment{increment} decision note missing science open-condition token."
        assert packet_required in packet_text, f"Increment{increment} execution packet missing science enforcement token."
        assert assess_required in assess_text, f"Increment{increment} assessment note missing science gate status token."
        assert (
            "formal/python/tests/test_qft_gr_seam_reactivation_sliceb_science_first_enforcement_gate.py"
            in packet_text
        ), f"Increment{increment} execution packet focused ladder must include science-first enforcement gate path."

        artifact_rel_path = _assert_science_validation_note_content(increment, note_text)
        artifact = _assert_science_artifact_schema(increment, artifact_rel_path)

        next_token_name = f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT{increment + 1}_JUSTIFICATION_v0"
        next_token = _extract_token_value(assess_text, next_token_name)
        if next_token == "CONDITIONAL_YES_BOUNDED_ONLY":
            assert artifact["passes_threshold"] is True, (
                f"Increment{increment} cannot emit conditional-yes next-increment justification with failing science artifact."
            )

