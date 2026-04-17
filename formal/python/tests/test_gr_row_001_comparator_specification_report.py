from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_row_001_comparator_specification_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "target_row": "ROW-PILLAR-GR-001",
        "required_shared_interface_outcome": "GR_ROW_001_SHARED_INTERFACE_DECLARED",
        "required_concept_outcome": "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED",
        "required_packet05_decision": "RETAIN_v0",
        "required_packet05_status": "RUN_BOUNDED_v0_NONCLAIM",
        "required_note_tokens": [
            "GR_ROW_001_COMPARATOR_SPEC_STATUS_v0: DECLARED_NONEXECUTING_COMPARATOR_SPEC",
            "GR_ROW_001_COMPARATOR_SPEC_TARGET_ROW_v0: ROW-PILLAR-GR-001",
            "GR_ROW_001_COMPARATOR_SPEC_INTERFACE_OBJECT_v0: XI_GR_TRANSPORT_ALIGNMENT_INTERFACE",
            "GR_ROW_001_COMPARATOR_SPEC_COMPARATOR_ID_v0: XI_GR_SINGLE_SURFACE_SIGNED_RESIDUAL_COMPARATOR",
            "GR_ROW_001_COMPARATOR_SPEC_INPUT_OBSERVABLE_v0: DELTA_XI_GR_INTERFACE_SIGNED_RESIDUAL",
            "GR_ROW_001_COMPARATOR_SPEC_COMPARISON_SURFACE_v0: SINGLE_SHARED_SCALAR_RESIDUAL_SURFACE",
            "GR_ROW_001_COMPARATOR_SPEC_ORIENTATION_RULE_v0: HOLD_ONE_SIGN_AND_ORDERING_CONVENTION_ACROSS_BOTH_VIEWS",
            "GR_ROW_001_COMPARATOR_SPEC_CLASS_A_v0: SIGN_COHERENT_SHARED_SURFACE",
            "GR_ROW_001_COMPARATOR_SPEC_CLASS_B_v0: SCALE_UNDERDECLARED_BUT_SURFACE_PRESERVED",
            "GR_ROW_001_COMPARATOR_SPEC_CLASS_C_v0: SURFACE_INCOHERENT_FAIL",
            "GR_ROW_001_COMPARATOR_SPEC_FAILURE_RULE_v0: FAIL_IF_MAP_OR_SIGN_CONVENTION_CANNOT_BE_KEPT_SINGLE_VALUED",
            "GR_ROW_001_COMPARATOR_SPEC_EXECUTION_POLICY_v0: NONEXECUTING_SPECIFICATION_ONLY_UNTIL_P75_AND_P77_CLEAR",
        ],
        "required_formula_phrase": "Delta_Xi_GR = r_a - M(r_t)",
        "required_dormancy_phrase": "It does not authorize numerical thresholds, packet execution, blocker movement claims, or lane reopen.",
        "required_capstone_phrase": "This comparator specification is the final dormant GR design checkpoint under current dormancy rules.",
        "required_package_phrase": "The concept packet, shared-interface declaration, and comparator specification form the canonical dormant GR design package for ROW-PILLAR-GR-001.",
        "required_handoff_phrase": "If GR later resumes legitimately, resume from the concept packet, shared-interface declaration, and comparator specification package rather than returning to abstract review layers.",
        "required_canonical_report_phrase": "Treat the current comparator-spec report as the canonical dormant GR design handoff report under present dormancy standards.",
        "required_preparation_not_progress_phrase": "It must not be summarized as live GR execution progress, blocker movement, or restart readiness.",
        "interface_object": "XI_GR_TRANSPORT_ALIGNMENT_INTERFACE",
        "comparator_id": "XI_GR_SINGLE_SURFACE_SIGNED_RESIDUAL_COMPARATOR",
        "input_observable": "DELTA_XI_GR_INTERFACE_SIGNED_RESIDUAL",
        "comparison_surface": "SINGLE_SHARED_SCALAR_RESIDUAL_SURFACE",
        "allowed_classes": [
            "SIGN_COHERENT_SHARED_SURFACE",
            "SCALE_UNDERDECLARED_BUT_SURFACE_PRESERVED",
            "SURFACE_INCOHERENT_FAIL",
        ],
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("required_dormancy_phrase")

    _write_json(
        path,
        {
            "required_inputs": {
                "gr_row_001_shared_interface_declaration_report": "formal/output/reports/gr_row_001_shared_interface_declaration_20260413_v0.json",
                "gr_row_001_new_structure_concept_packet_report": "formal/output/reports/gr_row_001_new_structure_concept_packet_20260413_v0.json",
                "gr_empirical_comparison_packet_05_artifact": "formal/output/gr_empirical_comparison_packet_05_v0.json",
                "comparator_spec_note": "formal/docs/paper/GR_ROW_001_COMPARATOR_SPECIFICATION_v0.md",
            },
            "comparator_spec_policy": policy,
            "comparator_spec_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_ROW_001_COMPARATOR_SPECIFICATION_OUTCOME",
                "no_loop_rule": "ONE_GR_ROW_001_COMPARATOR_SPECIFICATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "GR_ROW_001_COMPARATOR_SPEC_DECLARED",
                    "GR_ROW_001_COMPARATOR_SPEC_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_GR_ROW_001_COMPARATOR_SPEC_REPAIR",
                ],
                "default_outcome": "GR_ROW_001_COMPARATOR_SPEC_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, shared_interface_outcome: str = "GR_ROW_001_SHARED_INTERFACE_DECLARED") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_shared_interface_declaration_20260413_v0.json",
        {"summary": {"terminal_outcome": shared_interface_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_new_structure_concept_packet_20260413_v0.json",
        {"summary": {"terminal_outcome": "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED"}},
    )
    _write_json(
        root / "formal" / "output" / "gr_empirical_comparison_packet_05_v0.json",
        {"payload": {"status": "RUN_BOUNDED_v0_NONCLAIM", "decision": "RETAIN_v0"}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "GR_ROW_001_COMPARATOR_SPECIFICATION_v0.md",
        "GR_ROW_001_COMPARATOR_SPEC_STATUS_v0: DECLARED_NONEXECUTING_COMPARATOR_SPEC\n"
        "GR_ROW_001_COMPARATOR_SPEC_TARGET_ROW_v0: ROW-PILLAR-GR-001\n"
        "GR_ROW_001_COMPARATOR_SPEC_INTERFACE_OBJECT_v0: XI_GR_TRANSPORT_ALIGNMENT_INTERFACE\n"
        "GR_ROW_001_COMPARATOR_SPEC_COMPARATOR_ID_v0: XI_GR_SINGLE_SURFACE_SIGNED_RESIDUAL_COMPARATOR\n"
        "GR_ROW_001_COMPARATOR_SPEC_INPUT_OBSERVABLE_v0: DELTA_XI_GR_INTERFACE_SIGNED_RESIDUAL\n"
        "GR_ROW_001_COMPARATOR_SPEC_COMPARISON_SURFACE_v0: SINGLE_SHARED_SCALAR_RESIDUAL_SURFACE\n"
        "GR_ROW_001_COMPARATOR_SPEC_ORIENTATION_RULE_v0: HOLD_ONE_SIGN_AND_ORDERING_CONVENTION_ACROSS_BOTH_VIEWS\n"
        "GR_ROW_001_COMPARATOR_SPEC_CLASS_A_v0: SIGN_COHERENT_SHARED_SURFACE\n"
        "GR_ROW_001_COMPARATOR_SPEC_CLASS_B_v0: SCALE_UNDERDECLARED_BUT_SURFACE_PRESERVED\n"
        "GR_ROW_001_COMPARATOR_SPEC_CLASS_C_v0: SURFACE_INCOHERENT_FAIL\n"
        "GR_ROW_001_COMPARATOR_SPEC_FAILURE_RULE_v0: FAIL_IF_MAP_OR_SIGN_CONVENTION_CANNOT_BE_KEPT_SINGLE_VALUED\n"
        "GR_ROW_001_COMPARATOR_SPEC_EXECUTION_POLICY_v0: NONEXECUTING_SPECIFICATION_ONLY_UNTIL_P75_AND_P77_CLEAR\n"
        "Delta_Xi_GR = r_a - M(r_t)\n"
        "It does not authorize numerical thresholds, packet execution, blocker movement claims, or lane reopen.\n"
        "The concept packet, shared-interface declaration, and comparator specification form the canonical dormant GR design package for ROW-PILLAR-GR-001.\n"
        "This comparator specification is the final dormant GR design checkpoint under current dormancy rules.\n"
        "If GR later resumes legitimately, resume from the concept packet, shared-interface declaration, and comparator specification package rather than returning to abstract review layers.\n"
        "Treat the current comparator-spec report as the canonical dormant GR design handoff report under present dormancy standards.\n"
        "It must not be summarized as live GR execution progress, blocker movement, or restart readiness.\n",
    )


def test_reports_gr_row_001_comparator_spec_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_COMPARATOR_SPECIFICATION_20260413_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_ROW_001_COMPARATOR_SPEC_DECLARED"


def test_reports_gr_row_001_comparator_spec_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_COMPARATOR_SPECIFICATION_20260413_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, shared_interface_outcome="GR_ROW_001_SHARED_INTERFACE_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_ROW_001_COMPARATOR_SPEC_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_gr_row_001_comparator_spec_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_COMPARATOR_SPECIFICATION_20260413_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_GR_ROW_001_COMPARATOR_SPEC_REPAIR"