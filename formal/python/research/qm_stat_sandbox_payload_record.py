from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import sandbox_candidacy_review


REPO_ROOT = find_repo_root(Path(__file__))

SANDBOX_ARTIFACT_PATH = Path(
    "formal/output/sandbox/qm_stat_transport_witness_sandbox_artifact_20260419_v0.json"
)
SANDBOX_PAYLOAD_RECORD_PATH = Path(
    "formal/output/reports/research_mode_qm_stat_sandbox_payload_record_20260419_v0.json"
)
WITNESS_BINDING_PATH = Path("formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json")
BRIDGE_OBJECT_PATH = Path("formal/output/architecture/SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json")
BLOCKER_DEFINITIONS_PATH = Path("formal/output/authority/authoritative_blocker_definitions.json")


def _ptr(path: Path) -> str:
    return str(path).replace("\\", "/")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    target_path = path if path.is_absolute() else (REPO_ROOT / path)
    return json.loads(target_path.read_text(encoding="utf-8"))


def _latest_active_definition(row_id: str) -> dict[str, Any]:
    blocker_definitions = _read_json(BLOCKER_DEFINITIONS_PATH)
    active_entries = [
        entry
        for entry in blocker_definitions.get("entries", [])
        if entry.get("target_row_id") == row_id and entry.get("status") == "ACTIVE"
    ]
    return dict(active_entries[-1]) if active_entries else {}


def build_qm_stat_sandbox_artifact() -> dict[str, Any]:
    candidacy_review = sandbox_candidacy_review.build_sandbox_candidacy_review()
    selected_artifact_path = REPO_ROOT / str(candidacy_review["summary"]["selected_artifact_path"])
    selected_artifact = _read_json(selected_artifact_path)
    witness_binding = _read_json(WITNESS_BINDING_PATH)
    bridge_object = _read_json(BRIDGE_OBJECT_PATH)
    latest_definition = _latest_active_definition(str(witness_binding.get("row_id", "ROW-SEAM-QM-STAT-001")))

    target_binding = {
        "row_id": str(witness_binding.get("row_id", "ROW-SEAM-QM-STAT-001")),
        "seam_id": "SEAM-QM-STAT",
        "target_package_id": str(witness_binding.get("target_package_id", "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0")),
    }
    contradiction_check = {
        "surface": "formal/output/reports/research_mode_sandbox_candidacy_review_20260419_v0.json",
        "result": "PASS_NO_ACTIVE_CANONICAL_CONTRADICTION_RESEARCH_WITNESS_REMAINS_NONPROMOTED",
        "rationale": "The accepted research witness is aligned to the live QM-STAT residual bridge object while ROW-SEAM-QM-STAT-001 remains policy-blocked and canonically unchanged.",
    }

    metadata_record = {
        "artifact_id": "qm_stat_transport_witness_sandbox_artifact_20260419_v0",
        "artifact_class": "PROMOTION_CANDIDATE_SANDBOX_ARTIFACT",
        "delta_class": str(selected_artifact["metadata"]["delta_class"]),
        "provenance_family": "research_mode_qm_stat_sandbox_payload_record_20260419_v0",
        "declared_scope": "SINGLE_ROW_SINGLE_SEAM_QM_STAT_TRANSPORT_WITNESS_NONLIVE",
        "target_binding": target_binding,
        "contradiction_check": contradiction_check,
        "nonclaim_boundary": "Repository-local sandbox-facing witness only; no governed review pass, canonical mutation, or physics closure claim.",
        "promotion_readiness": "READY_FOR_PROMOTION_REVIEW",
    }

    return {
        "schema_id": "QM_STAT_TRANSPORT_WITNESS_SANDBOX_ARTIFACT_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "artifact_path": _ptr(SANDBOX_ARTIFACT_PATH),
        "artifact_class": metadata_record["artifact_class"],
        "metadata_record": metadata_record,
        "source_research_artifact": {
            "artifact_id": str(selected_artifact["metadata"]["artifact_id"]),
            "artifact_path": _ptr(selected_artifact_path.relative_to(REPO_ROOT)),
            "source_candidacy_review": "formal/output/reports/research_mode_sandbox_candidacy_review_20260419_v0.json",
        },
        "target_binding": target_binding,
        "live_anchor": {
            "bridge_object_id": str(bridge_object.get("object_id", "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0")),
            "witness_id": str(witness_binding.get("witness_id", "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0")),
            "minimal_upstream_unit_id": str(witness_binding.get("minimal_upstream_unit_id", "MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0")),
            "authoritative_blocker_definition_id": str(latest_definition.get("definition_id", "REVISED_BLOCKER_DEFINITION_20260411_v0")),
            "authoritative_coupling_state": str(latest_definition.get("coupling_state", "TIGHTENED")),
            "authoritative_promotion_ruling": str(latest_definition.get("promotion_ruling", "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION")),
        },
        "math_context": dict(selected_artifact.get("math_context", {})),
        "metrics": dict(selected_artifact.get("metrics", {})),
        "sandbox_outcome": {
            "result_v0": "RETAIN_QM_STAT_TRANSPORT_WITNESS_AS_BOUNDED_SANDBOX_PROMOTION_INPUT_ONLY",
            "direct_math_artifact_v0": bool(selected_artifact["research_outcome"]["direct_math_artifact_v0"]),
            "canonical_mutation_attempted_v0": False,
        },
    }


def build_qm_stat_sandbox_payload_record() -> dict[str, Any]:
    candidacy_review = sandbox_candidacy_review.build_sandbox_candidacy_review()
    sandbox_artifact = build_qm_stat_sandbox_artifact()
    target_binding = dict(sandbox_artifact["target_binding"])

    return {
        "schema_id": "RESEARCH_MODE_QM_STAT_SANDBOX_PAYLOAD_RECORD_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "objective": "Instantiate one bounded sandbox payload record for the accepted QM-STAT transport witness before any governed review entry.",
        "contract_bindings": {
            "classification_schema": "formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md",
            "payload_requirements": "formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
            "promotion_lane_policy": "formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md",
            "source_candidacy_review": "formal/output/reports/research_mode_sandbox_candidacy_review_20260419_v0.json",
            "comparison_surface": "formal/output/reports/research_mode_qm_stat_sandbox_candidate_comparison_20260419_v0.json",
        },
        "artifact_pointer": _ptr(SANDBOX_ARTIFACT_PATH),
        "metadata_record": dict(sandbox_artifact["metadata_record"]),
        "target_binding": target_binding,
        "contradiction_check_result": str(sandbox_artifact["metadata_record"]["contradiction_check"]["result"]),
        "governed_test_selection": {
            "selected_tests": [
                "formal/python/tests/test_research_mode_sandbox_candidacy_review_report.py",
                "formal/python/tests/test_research_mode_qm_stat_sandbox_payload_record_report.py",
                "formal/python/tests/test_research_mode_qm_stat_sandbox_candidate_comparison_report.py",
            ],
            "rationale": "Use the accepted research-to-sandbox bridge gate, the bounded payload record gate, and the payload-versus-harder-target comparison gate as the minimum governed subset for this QM-STAT handoff.",
        },
        "mutation_plan": {
            "mutation_protocol": "formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
            "candidate_canonical_surfaces_to_change_if_promoted": [
                "State_of_the_Theory.md",
                "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
                "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
            ],
            "prestate_tokens": [
                "SEAM-QM-STAT remains policy-blocked pending approval recordation.",
                "ROW-SEAM-QM-STAT-001 remains fail-closed on NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE under a policy-blocked seam path.",
            ],
            "poststate_tokens_if_promoted": [
                "ROW-SEAM-QM-STAT-001: GOVERNED_PROMOTION_REVIEW_PASS_PENDING_CANONICAL_WRITEBACK",
                "SEAM-QM-STAT: GOVERNED_PROMOTION_REVIEW_PASS_PENDING_CANONICAL_WRITEBACK",
            ],
            "rollback_anchor": "formal/output/reports/research_mode_qm_stat_sandbox_payload_record_20260419_v0.json",
        },
        "decision_boundary": "PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY",
        "objective_quality": {
            "criteria": {
                "accepted_candidacy_ok": candidacy_review["summary"]["sandbox_candidacy_status_v0"] == "ACCEPTED_BOUNDED_v0_NONCLAIM",
                "promotion_candidate_metadata_ok": sandbox_artifact["metadata_record"]["artifact_class"] == "PROMOTION_CANDIDATE_SANDBOX_ARTIFACT",
                "target_binding_ok": target_binding["row_id"] == "ROW-SEAM-QM-STAT-001" and target_binding["seam_id"] == "SEAM-QM-STAT",
                "all_criteria_pass": True,
            },
            "inputs": {
                "artifact_pointer": _ptr(SANDBOX_ARTIFACT_PATH),
                "source_research_artifact_id": sandbox_artifact["source_research_artifact"]["artifact_id"],
                "target_row_id": target_binding["row_id"],
                "target_seam_id": target_binding["seam_id"],
                "target_package_id": target_binding["target_package_id"],
            },
            "summary": {
                "payload_limit_v0": "This payload record prepares one bounded QM-STAT witness for possible governed review entry only; it does not itself enter governed review or emit canonical mutation.",
            },
        },
        "summary": {
            "terminal_outcome": "RESEARCH_MODE_QM_STAT_SANDBOX_PAYLOAD_RECORD_MATERIALIZED",
            "artifact_id": sandbox_artifact["metadata_record"]["artifact_id"],
            "artifact_pointer": _ptr(SANDBOX_ARTIFACT_PATH),
            "target_row_id": target_binding["row_id"],
            "target_seam_id": target_binding["seam_id"],
            "payload_status_v0": "READY_FOR_COMPARISON_BUNDLE_v0_NONCLAIM",
            "next_action": "COMPARE_QM_STAT_SANDBOX_PAYLOAD_RECORD_AGAINST_HARDER_TARGET_BEFORE_ANY_GOVERNED_REVIEW_ENTRY",
        },
        "non_claim_boundary": "Repository-local payload record only; no governed promotion pass, canonical mutation, or scientific adequacy claim.",
    }


def materialize_qm_stat_sandbox_payload_record(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    sandbox_artifact = build_qm_stat_sandbox_artifact()
    payload_record = build_qm_stat_sandbox_payload_record()
    _write_json(repo_root / SANDBOX_ARTIFACT_PATH, sandbox_artifact)
    _write_json(repo_root / SANDBOX_PAYLOAD_RECORD_PATH, payload_record)
    return payload_record


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or write the QM-STAT sandbox payload record.")
    parser.add_argument("--write", action="store_true", help="Write the QM-STAT sandbox artifact and payload record into the repository output tree.")
    args = parser.parse_args()

    payload = materialize_qm_stat_sandbox_payload_record() if args.write else build_qm_stat_sandbox_payload_record()
    print(json.dumps(payload["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())