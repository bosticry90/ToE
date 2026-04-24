from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_export_compile_validation_checkpoint_v0.json"
MAIN_TEX_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "main.tex"
MAIN_PDF_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "main.pdf"
MAIN_LOG_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "main.log"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_export_compile_validation_note_has_required_structure() -> None:
    text = _read(NOTE_PATH)
    required_strings = [
        "Compile environment:",
        "Validation checks:",
        "Compiler availability:",
        "Compile replay:",
        "PDF artifact generation:",
        "Log-level diagnostics:",
        "Governance invariants:",
        "SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_STATUS_v0: COMPILE_AND_PDF_ARTIFACT_VALIDATED",
    ]
    for marker in required_strings:
        assert marker in text, f"Export compile-validation note missing marker: {marker}"


def test_toe_qft_scalar_export_compile_validation_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_export_compile_validation_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_EXPORT_COMPILE_AND_PDF_VALIDATION"
    assert artifact.get("scope") == "bounded_free_scalar_paper1_canonical_export_compile_validation"

    env = artifact.get("compile_environment", {})
    assert env.get("latex_compiler") == "pdflatex"
    assert env.get("bib_tool") == "bibtex"
    assert env.get("workspace_tex_tooling_available") is True

    replay = artifact.get("compile_replay", {})
    assert replay.get("final_pass_fatal_error") is False
    assert isinstance(replay.get("commands"), list) and replay.get("commands")

    pdf = artifact.get("pdf_artifact", {})
    assert pdf.get("path") == "formal/docs/submission/scalar_paper1/main.pdf"
    assert pdf.get("exists") is True
    assert isinstance(pdf.get("size_bytes"), int) and pdf.get("size_bytes") > 0

    logs = artifact.get("log_checks", {})
    assert logs.get("main_log_path") == "formal/docs/submission/scalar_paper1/main.log"
    assert logs.get("output_written_marker_present") is True

    guardrails = artifact.get("policy_guardrails", {})
    assert guardrails.get("scalar_paper1_baseline_freeze") is True
    assert guardrails.get("no_new_scalar_tranche_authorized") is True
    assert guardrails.get("seam_hold_token") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"

    assert artifact.get("status_token") == "SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_STATUS_v0: COMPILE_AND_PDF_ARTIFACT_VALIDATED"
    assert artifact.get("status") == "COMPILE_AND_PDF_ARTIFACT_VALIDATED"


def test_toe_qft_scalar_export_compile_validation_artifacts_are_present() -> None:
    checkpoint = _read_json(CHECKPOINT_PATH)
    pdf_size = checkpoint.get("pdf_artifact", {}).get("size_bytes")

    assert MAIN_TEX_PATH.exists(), "Missing canonical TeX manuscript"
    assert MAIN_PDF_PATH.exists(), "Missing compiled PDF artifact"
    assert MAIN_LOG_PATH.exists(), "Missing compile log"

    assert MAIN_PDF_PATH.stat().st_size > 0
    assert MAIN_PDF_PATH.stat().st_size == pdf_size

    log_text = _read(MAIN_LOG_PATH)
    assert "Output written on main.pdf" in log_text
    assert "Fatal error occurred" not in log_text


def test_toe_qft_scalar_export_compile_validation_is_mirrored_in_authority_surfaces() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_v0.md",
        "formal/output/toe_qft_scalar_route_export_compile_validation_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_scalar_route_export_compile_validation_gate.py",
        "formal/docs/submission/scalar_paper1/main.pdf",
        "SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_STATUS_v0: COMPILE_AND_PDF_ARTIFACT_VALIDATED",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]

    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"State/Inventory missing compile-validation ref: {ref}"
        )
        assert ref in roadmap_text, f"Roadmap missing compile-validation ref: {ref}"
