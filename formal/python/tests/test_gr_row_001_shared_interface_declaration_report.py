from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_row_001_shared_interface_declaration_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "target_row": "ROW-PILLAR-GR-001",
        "required_concept_outcome": "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED",
        "required_structural_gap_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
        "required_packet05_decision": "RETAIN_v0",
        "required_packet05_status": "RUN_BOUNDED_v0_NONCLAIM",
        "required_note_tokens": [
            "GR_ROW_001_SHARED_INTERFACE_STATUS_v0: DECLARED_NONEXECUTING_DESIGN_PACKET",
            "GR_ROW_001_SHARED_INTERFACE_TARGET_ROW_v0: ROW-PILLAR-GR-001",
            "GR_ROW_001_SHARED_INTERFACE_OBJECT_v0: XI_GR_TRANSPORT_ALIGNMENT_INTERFACE",
            "GR_ROW_001_SHARED_INTERFACE_DOMAIN_v0: WEAK_FIELD_TRANSPORT_RESIDUAL_CLASS",
            "GR_ROW_001_SHARED_INTERFACE_CODOMAIN_v0: REGIME_LIMIT_ALIGNMENT_DEFECT_CLASS",
            "GR_ROW_001_SHARED_INTERFACE_MAP_v0: XI_MAP_TRANSPORT_TO_ALIGNMENT_DEFECT",
            "GR_ROW_001_SHARED_INTERFACE_OBSERVABLE_v0: DELTA_XI_GR_INTERFACE_SIGNED_RESIDUAL",
            "GR_ROW_001_SHARED_INTERFACE_COMPARISON_SURFACE_v0: SINGLE_SHARED_SCALAR_RESIDUAL_SURFACE",
            "GR_ROW_001_SHARED_INTERFACE_FAILURE_RULE_v0: FAIL_IF_NO_SINGLE_SIGNED_RESIDUAL_CAN_BE_DECLARED_FOR_BOTH_VIEWS",
            "GR_ROW_001_SHARED_INTERFACE_EXECUTION_POLICY_v0: NONEXECUTING_DECLARATION_ONLY_UNTIL_P75_AND_P77_CLEAR",
        ],
        "required_formula_phrase": "Delta_Xi_GR = r_a - M(r_t)",
        "interface_object": "XI_GR_TRANSPORT_ALIGNMENT_INTERFACE",
        "interface_domain": "WEAK_FIELD_TRANSPORT_RESIDUAL_CLASS",
        "interface_codomain": "REGIME_LIMIT_ALIGNMENT_DEFECT_CLASS",
        "comparison_surface": "SINGLE_SHARED_SCALAR_RESIDUAL_SURFACE",
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("required_formula_phrase")

    _write_json(
        path,
        {
            "required_inputs": {
                "gr_row_001_new_structure_concept_packet_report": "formal/output/reports/gr_row_001_new_structure_concept_packet_20260413_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "gr_empirical_comparison_packet_05_artifact": "formal/output/gr_empirical_comparison_packet_05_v0.json",
                "shared_interface_note": "formal/docs/paper/GR_ROW_001_SHARED_INTERFACE_DECLARATION_v0.md",
            },
            "shared_interface_policy": policy,
            "shared_interface_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_ROW_001_SHARED_INTERFACE_DECLARATION_OUTCOME",
                "no_loop_rule": "ONE_GR_ROW_001_SHARED_INTERFACE_DECLARATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "GR_ROW_001_SHARED_INTERFACE_DECLARED",
                    "GR_ROW_001_SHARED_INTERFACE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_GR_ROW_001_SHARED_INTERFACE_REPAIR",
                ],
                "default_outcome": "GR_ROW_001_SHARED_INTERFACE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, concept_outcome: str = "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_new_structure_concept_packet_20260413_v0.json",
        {"summary": {"terminal_outcome": concept_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {"summary": {"terminal_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"}},
    )
    _write_json(
        root / "formal" / "output" / "gr_empirical_comparison_packet_05_v0.json",
        {"payload": {"status": "RUN_BOUNDED_v0_NONCLAIM", "decision": "RETAIN_v0"}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "GR_ROW_001_SHARED_INTERFACE_DECLARATION_v0.md",
        "GR_ROW_001_SHARED_INTERFACE_STATUS_v0: DECLARED_NONEXECUTING_DESIGN_PACKET\n"
        "GR_ROW_001_SHARED_INTERFACE_TARGET_ROW_v0: ROW-PILLAR-GR-001\n"
        "GR_ROW_001_SHARED_INTERFACE_OBJECT_v0: XI_GR_TRANSPORT_ALIGNMENT_INTERFACE\n"
        "GR_ROW_001_SHARED_INTERFACE_DOMAIN_v0: WEAK_FIELD_TRANSPORT_RESIDUAL_CLASS\n"
        "GR_ROW_001_SHARED_INTERFACE_CODOMAIN_v0: REGIME_LIMIT_ALIGNMENT_DEFECT_CLASS\n"
        "GR_ROW_001_SHARED_INTERFACE_MAP_v0: XI_MAP_TRANSPORT_TO_ALIGNMENT_DEFECT\n"
        "GR_ROW_001_SHARED_INTERFACE_OBSERVABLE_v0: DELTA_XI_GR_INTERFACE_SIGNED_RESIDUAL\n"
        "GR_ROW_001_SHARED_INTERFACE_COMPARISON_SURFACE_v0: SINGLE_SHARED_SCALAR_RESIDUAL_SURFACE\n"
        "GR_ROW_001_SHARED_INTERFACE_FAILURE_RULE_v0: FAIL_IF_NO_SINGLE_SIGNED_RESIDUAL_CAN_BE_DECLARED_FOR_BOTH_VIEWS\n"
        "GR_ROW_001_SHARED_INTERFACE_EXECUTION_POLICY_v0: NONEXECUTING_DECLARATION_ONLY_UNTIL_P75_AND_P77_CLEAR\n"
        "Delta_Xi_GR = r_a - M(r_t)\n",
    )


def test_reports_gr_row_001_shared_interface_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_SHARED_INTERFACE_DECLARATION_20260413_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_ROW_001_SHARED_INTERFACE_DECLARED"


def test_reports_gr_row_001_shared_interface_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_SHARED_INTERFACE_DECLARATION_20260413_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, concept_outcome="GR_ROW_001_NEW_STRUCTURE_CONCEPT_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_ROW_001_SHARED_INTERFACE_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_gr_row_001_shared_interface_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_SHARED_INTERFACE_DECLARATION_20260413_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_GR_ROW_001_SHARED_INTERFACE_REPAIR"