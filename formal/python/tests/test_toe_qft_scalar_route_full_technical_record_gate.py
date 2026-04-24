from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
TECH_RECORD_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_full_technical_record_checkpoint_v0.json"
MANIFEST_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_scalar_inventory_manifest_v0.json"

ALLOWED_MATH_CAPTURE = {
    "FULLY_DERIVED_v0",
    "SUMMARIZED_ONLY_v0",
    "DISTRIBUTED_DERIVATION_v0",
    "MISSING_DERIVATION_v0",
}
ALLOWED_CLAIM_CRITICALITY = {"BLOCKER", "HIGH", "MEDIUM", "LOW"}
ALLOWED_LEAN_LINKAGE = {"LINKED_v0", "PARTIAL_LINKED_v0", "MISSING_LINKAGE_v0"}
ALLOWED_GAP_ADJUDICATION_ACTION = {
    "RECOVER_IN_LEDGER_v0",
    "RETAIN_AS_SUMMARY_v0",
    "SCOPE_DOWNGRADE_REQUIRED_v0",
    "BLOCKER_PENDING_DERIVATION_v0",
}
ALLOWED_LEAN_LINKAGE_DISPOSITION = {
    "LINKAGE_ACCEPTED_v0",
    "LINKAGE_RECOVERY_REQUIRED_v0",
    "LINKAGE_BLOCKER_v0",
}
ALLOWED_PAPER_RELIANCE_STATUS = {
    "MAY_RELY_WITH_BOUNDARY_v0",
    "MAY_RELY_WITH_GAP_FLAG_v0",
    "MUST_NOT_RELY_UNTIL_DISCHARGED_v0",
}
ALLOWED_RECOVERY_PASS = {
    "RECOVERY_PASS_00_BASELINE_v0",
    "RECOVERY_PASS_01_BLOCKER_HIGH_LEDGER_v0",
    "RECOVERY_PASS_02_REMAINING_HIGH_MEDIUM_LEDGER_v0",
    "RECOVERY_PASS_03_LINKAGE_CLOSURE_v0",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_scalar_full_technical_record_has_required_markers() -> None:
    text = _read(TECH_RECORD_PATH)

    required_strings = [
        "Spec ID:",
        "Target ID:",
        "Scope lock:",
        "Non-claim boundary:",
        "math_capture_status taxonomy:",
        "claim_criticality taxonomy:",
        "lean_linkage_status taxonomy:",
        "gap_adjudication_action taxonomy:",
        "lean_linkage_disposition taxonomy:",
        "paper_reliance_status taxonomy:",
        "recovery_pass taxonomy:",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
        "TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_ARTIFACT_v0",
        "TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_MANIFEST_ARTIFACT_v0",
        "TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_GATE_v0",
        "## Claim Ledger",
        "## Gap Matrix",
    ]
    for marker in required_strings:
        assert marker in text, f"Full technical record missing marker: {marker}"


def test_scalar_full_technical_record_ledger_fields_and_enums() -> None:
    text = _read(TECH_RECORD_PATH)

    claim_ids = re.findall(r"^\- claim_id:\s*(.+)$", text, flags=re.MULTILINE)
    math_statuses = re.findall(r"^\s+math_capture_status:\s*(.+)$", text, flags=re.MULTILINE)
    criticalities = re.findall(r"^\s+claim_criticality:\s*(.+)$", text, flags=re.MULTILINE)
    lean_statuses = re.findall(r"^\s+lean_linkage_status:\s*(.+)$", text, flags=re.MULTILINE)
    gap_actions = re.findall(r"^\s+gap_adjudication_action:\s*(.+)$", text, flags=re.MULTILINE)
    lean_dispositions = re.findall(r"^\s+lean_linkage_disposition:\s*(.+)$", text, flags=re.MULTILINE)
    paper_reliance = re.findall(r"^\s+paper_reliance_status:\s*(.+)$", text, flags=re.MULTILINE)
    recovery_pass = re.findall(r"^\s+recovery_pass:\s*(.+)$", text, flags=re.MULTILINE)

    assert len(claim_ids) >= 8, "Expected at least 8 scalar claims in full technical record ledger."
    assert len(math_statuses) == len(claim_ids), "Each claim must define math_capture_status."
    assert len(criticalities) == len(claim_ids), "Each claim must define claim_criticality."
    assert len(lean_statuses) == len(claim_ids), "Each claim must define lean_linkage_status."
    assert len(gap_actions) == len(claim_ids), "Each claim must define gap_adjudication_action."
    assert len(lean_dispositions) == len(claim_ids), "Each claim must define lean_linkage_disposition."
    assert len(paper_reliance) == len(claim_ids), "Each claim must define paper_reliance_status."
    assert len(recovery_pass) == len(claim_ids), "Each claim must define recovery_pass."

    for value in math_statuses:
        assert value in ALLOWED_MATH_CAPTURE, f"Unsupported math_capture_status: {value}"
    for value in criticalities:
        assert value in ALLOWED_CLAIM_CRITICALITY, f"Unsupported claim_criticality: {value}"
    for value in lean_statuses:
        assert value in ALLOWED_LEAN_LINKAGE, f"Unsupported lean_linkage_status: {value}"
    for value in gap_actions:
        assert value in ALLOWED_GAP_ADJUDICATION_ACTION, f"Unsupported gap_adjudication_action: {value}"
    for value in lean_dispositions:
        assert value in ALLOWED_LEAN_LINKAGE_DISPOSITION, f"Unsupported lean_linkage_disposition: {value}"
    for value in paper_reliance:
        assert value in ALLOWED_PAPER_RELIANCE_STATUS, f"Unsupported paper_reliance_status: {value}"
    for value in recovery_pass:
        assert value in ALLOWED_RECOVERY_PASS, f"Unsupported recovery_pass: {value}"

    # For incomplete or distributed/summarized claims, adjudication must not be empty passthrough.
    for idx, claim_id in enumerate(claim_ids):
        if math_statuses[idx] in {"SUMMARIZED_ONLY_v0", "DISTRIBUTED_DERIVATION_v0", "MISSING_DERIVATION_v0"}:
            assert gap_actions[idx] in {
                "RECOVER_IN_LEDGER_v0",
                "RETAIN_AS_SUMMARY_v0",
                "SCOPE_DOWNGRADE_REQUIRED_v0",
                "BLOCKER_PENDING_DERIVATION_v0",
            }, f"Claim requires adjudication action: {claim_id}"

        if lean_statuses[idx] in {"PARTIAL_LINKED_v0", "MISSING_LINKAGE_v0"}:
            assert lean_dispositions[idx] in {
                "LINKAGE_RECOVERY_REQUIRED_v0",
                "LINKAGE_BLOCKER_v0",
            }, f"Claim requires linkage disposition for incomplete Lean linkage: {claim_id}"

        if criticalities[idx] == "BLOCKER" and gap_actions[idx] == "BLOCKER_PENDING_DERIVATION_v0":
            assert (
                paper_reliance[idx] == "MUST_NOT_RELY_UNTIL_DISCHARGED_v0"
            ), f"Blocker pending derivation must not be relied on in paper lane: {claim_id}"


def test_scalar_full_technical_record_manifest_schema_and_paths() -> None:
    manifest = _read_json(MANIFEST_PATH)

    assert manifest.get("artifact_id") == "toe_qft_scalar_route_scalar_inventory_manifest_v0"
    assert manifest.get("phase") == "PHASE_1_SCALAR_FULL_TECHNICAL_INVENTORY"
    assert manifest.get("scope") == "scalar_lane_plus_scalar_linked_cross_lane_evidence"

    for key in [
        "report_inventory",
        "artifact_inventory",
        "gate_inventory",
        "scalar_linked_cross_lane_evidence_inventory",
    ]:
        values = manifest.get(key)
        assert isinstance(values, list) and values, f"Manifest list is missing or empty: {key}"
        for rel_path in values:
            assert isinstance(rel_path, str)
            abs_path = REPO_ROOT / rel_path
            assert abs_path.exists(), f"Manifest path does not exist: {rel_path}"

    counts = manifest.get("counts", {})
    assert counts.get("report_inventory") == len(manifest["report_inventory"])
    assert counts.get("artifact_inventory") == len(manifest["artifact_inventory"])
    assert counts.get("gate_inventory") == len(manifest["gate_inventory"])
    assert counts.get("scalar_linked_cross_lane_evidence_inventory") == len(
        manifest["scalar_linked_cross_lane_evidence_inventory"]
    )


def test_scalar_full_technical_record_checkpoint_consistency() -> None:
    text = _read(TECH_RECORD_PATH)
    checkpoint = _read_json(CHECKPOINT_PATH)

    assert checkpoint.get("artifact_id") == "toe_qft_scalar_route_full_technical_record_checkpoint_v0"
    assert checkpoint.get("phase") == "PHASE_1_SCALAR_FULL_TECHNICAL_RECORD_CHECKPOINT"

    payload = checkpoint.get("payload", {})
    assert payload.get("technical_record_path") == "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_v0.md"
    assert payload.get("inventory_manifest_path") == "formal/output/toe_qft_scalar_route_scalar_inventory_manifest_v0.json"

    coverage = payload.get("coverage_summary", {})
    required_coverage_keys = [
        "ledger_claims",
        "full_derived",
        "summarized_only",
        "distributed_derivation",
        "missing_derivation",
        "lean_linked",
        "lean_partial_linked",
        "lean_missing_linkage",
        "blocker_critical_claims",
        "high_critical_claims",
        "medium_critical_claims",
        "low_critical_claims",
        "recover_in_ledger",
        "retain_as_summary",
        "scope_downgrade_required",
        "blocker_pending_derivation",
        "paper_may_rely_with_boundary",
        "paper_may_rely_with_gap_flag",
        "paper_must_not_rely",
    ]
    for key in required_coverage_keys:
        assert key in coverage, f"Coverage summary missing key: {key}"

    total_math = (
        coverage["full_derived"]
        + coverage["summarized_only"]
        + coverage["distributed_derivation"]
        + coverage["missing_derivation"]
    )
    total_lean = coverage["lean_linked"] + coverage["lean_partial_linked"] + coverage["lean_missing_linkage"]
    total_criticality = (
        coverage["blocker_critical_claims"]
        + coverage["high_critical_claims"]
        + coverage["medium_critical_claims"]
        + coverage["low_critical_claims"]
    )
    total_adjudication = (
        coverage["recover_in_ledger"]
        + coverage["retain_as_summary"]
        + coverage["scope_downgrade_required"]
        + coverage["blocker_pending_derivation"]
    )
    total_paper_reliance = (
        coverage["paper_may_rely_with_boundary"]
        + coverage["paper_may_rely_with_gap_flag"]
        + coverage["paper_must_not_rely"]
    )

    assert coverage["ledger_claims"] == total_math
    assert coverage["ledger_claims"] == total_lean
    assert coverage["ledger_claims"] == total_criticality
    assert coverage["ledger_claims"] == total_adjudication
    assert coverage["ledger_claims"] == total_paper_reliance
    assert coverage["paper_may_rely_with_gap_flag"] == 0, "Gap-flag paper reliance must be closed in current scalar baseline."

    doc_artifact = _extract_token(text, "TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_ARTIFACT_v0")
    doc_manifest_artifact = _extract_token(text, "TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_MANIFEST_ARTIFACT_v0")
    doc_gate = _extract_token(text, "TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_GATE_v0")

    assert doc_artifact == checkpoint["artifact_id"]
    assert doc_manifest_artifact == "toe_qft_scalar_route_scalar_inventory_manifest_v0"
    assert doc_gate == "REQUIRED_FIELDS_AND_TRACEABILITY_ENFORCED"

    governance = payload.get("governance", {})
    assert governance.get("non_claim_boundary_locked") is True
    assert governance.get("lean_linkage_required") is True
    assert governance.get("cross_lane_scope_included") is True
    assert governance.get("seam_hold_status") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"
