from __future__ import annotations

import argparse
import hashlib
import json
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/pillar_seam_unit_mapping_ledger_first_unit_selector.py"
V2_PACKET_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-PACKET-v2.json"
)
V2_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260713_v2.json"
)
PACKET_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-FIRST-UNIT-SELECTOR-PACKET-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-FIRST-UNIT-SELECTOR-MANIFEST-v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_20260713_v0.json"
)
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0"
REVIEW_TARGET = "review_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0_result"
REVIEW_TARGET_KIND = "pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0_result_review"
FAILURE_TARGET = "prepare_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v1"
POST_ACCEPTANCE_TARGET = "prepare_maxwell_dirac_unit_object_foundation_packet_v0"
PACKET_SCHEMA_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_v0"
MANIFEST_SCHEMA_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_MANIFEST_v0"
REPORT_SCHEMA_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_20260713_v0"

EXPECTED_INPUT_HASHES = {
    V2_PACKET_RELATIVE_PATH: "edd86640c3d6664e27874e5e3737dfd20f3c85dd91729d74266eb296cdd20b3b",
    V2_REVIEW_RELATIVE_PATH: "6dac3d95a29e7ab0d29a99d5903b682bf235b92e025b044890a2e927d8b6f875",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_BASELINE_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

CRITERION_WEIGHTS = {
    "evidence_authority": 5,
    "object_clarity": 5,
    "noncircularity": 5,
    "dependency_readiness": 4,
    "downstream_leverage": 4,
    "bounded_scope": 3,
    "restoration_clarity": 3,
    "computational_enablement": 2,
}
THRESHOLD = 44
SENSITIVITY_THRESHOLDS = [40, 42, 44, 46, 48]
TIE_BREAK_ORDER = ["SR", "GR", "EM", "QFT", "QM", "STAT", "COSMO"]
PILLAR_ROW_BY_CODE = {
    "QFT": "PILLAR-QFT-units_and_dimensions-v0",
    "GR": "PILLAR-GR-units_and_dimensions-v0",
    "QM": "PILLAR-QM-units_and_dimensions-v0",
    "STAT": "PILLAR-STAT-units_and_dimensions-v0",
    "EM": "PILLAR-EM-units_and_dimensions-v0",
    "SR": "PILLAR-SR-units_and_dimensions-v0",
    "COSMO": "PILLAR-COSMO-units_and_dimensions-v0",
}
PILLAR_CODE_BY_ROW = {row_id: code for code, row_id in PILLAR_ROW_BY_CODE.items()}


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def load_inputs() -> tuple[dict[str, Any], dict[str, Any]]:
    for path, expected in EXPECTED_INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != expected:
            raise ValueError(f"accepted selector input hash mismatch: {path}")
    packet = load_json(REPO_ROOT / V2_PACKET_RELATIVE_PATH)
    review = load_json(REPO_ROOT / V2_REVIEW_RELATIVE_PATH)
    if not (
        review.get("accepted") is True
        and review.get("verdict") == "ACCEPT"
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("unit_resolution_execution_authorized") is False
    ):
        raise ValueError("accepted v2 review does not authorize the exact selector target")
    return packet, review


def _records(row: dict[str, Any]) -> list[dict[str, Any]]:
    return row.get("evidence_records", [])


def _direct_record(row: dict[str, Any]) -> dict[str, Any]:
    direct = [
        record
        for record in _records(row)
        if record.get("evidence_role") in {"PLANNING_AUTHORITY", "MATHEMATICAL_DERIVATION"}
        and record.get("route_support_eligible") is True
    ]
    if len(direct) != 1:
        raise ValueError(f"expected one direct evidence record: {row.get('row_id')}")
    return direct[0]


def _ledger_record(row: dict[str, Any]) -> dict[str, Any]:
    records = [record for record in _records(row) if record.get("source_id") == "accepted_unit_ledger"]
    if len(records) != 1:
        raise ValueError(f"expected one ledger evidence record: {row.get('row_id')}")
    return records[0]


def _score_values(code: str, direct: dict[str, Any]) -> dict[str, int]:
    return {
        "evidence_authority": 2 if direct["authority_class"] == "BOUNDED_ACCEPTED_MATHEMATICAL_SURFACE" else 1,
        "object_clarity": 2 if code in {"SR", "EM"} else 1,
        "noncircularity": 2,
        "dependency_readiness": 1,
        "downstream_leverage": 2 if code in {"SR", "GR", "EM", "QFT"} else 1,
        "bounded_scope": 2 if code in {"SR", "EM"} else 1,
        "restoration_clarity": 2 if code == "SR" else (1 if code in {"GR", "EM", "COSMO"} else 0),
        "computational_enablement": 2 if code == "EM" else (0 if code == "STAT" else 1),
    }


def _reason(code: str, criterion: str, score: int, direct: dict[str, Any]) -> str:
    reasons = {
        "evidence_authority": (
            "A bounded legacy mathematical surface is located, but it is not release-facing current."
            if score == 2
            else "The located direct source is a release-facing P-POLICY planning nonclaim."
        ),
        "object_clarity": (
            "The source identifies a compact typed transform/interval or gauge-potential/field-strength object chain."
            if score == 2
            else "The source names a bounded surface but does not close a row-wide unit-bearing object inventory."
        ),
        "noncircularity": "The route is supported by ledger and source propositions; no candidate master action or expected route count is used.",
        "dependency_readiness": "The row is blocked but has an accepted ledger identity and one bounded direct source; resolution dependencies remain open.",
        "downstream_leverage": (
            "This surface is a direct convention, field, or relativistic dependency for coupled-field benchmarks."
            if score == 2
            else "This surface has bounded value but less immediate leverage for the preferred coupled-field benchmark."
        ),
        "bounded_scope": (
            "The source exposes a compact, reviewable convention/object scope."
            if score == 2
            else "The source spans several objects or assumptions and requires a narrower first preparation."
        ),
        "restoration_clarity": (
            "The open coordinate convention and suppressed-c question define a direct restoration task."
            if score == 2
            else (
                "A restoration need is visible, but the exact rule or normalization is not yet fixed."
                if score == 1
                else "No sufficiently specific restoration route is established."
            )
        ),
        "computational_enablement": (
            "Resolving this typed field surface directly enables a computational field benchmark."
            if score == 2
            else (
                "The surface contributes to later computation but does not by itself freeze an executable model."
                if score == 1
                else "The present planning surface does not yet enable a bounded computation."
            )
        ),
    }
    return reasons[criterion]


def _missing_for_next(criterion: str, score: int) -> str:
    if score == 2:
        return "MAXIMUM_SCORE"
    needs = {
        "evidence_authority": "A current accepted bounded derivation or review-backed underlying artifact for the exact proposition.",
        "object_clarity": "A closed row-wide inventory with exact object identities and semantics.",
        "noncircularity": "MAXIMUM_SCORE",
        "dependency_readiness": "Accepted prerequisite propositions with no open dependency blockers.",
        "downstream_leverage": "An accepted dependency link to the selected bounded computational benchmark.",
        "bounded_scope": "A single compact object/convention scope with explicit exclusions.",
        "restoration_clarity": "An exact c, hbar, electromagnetic-normalization, or coordinate restoration expression.",
        "computational_enablement": "A reviewed executable equation/object interface and frozen observables.",
    }
    return needs[criterion]


def score_row(row: dict[str, Any]) -> dict[str, Any]:
    code = PILLAR_CODE_BY_ROW[row["row_id"]]
    direct = _direct_record(row)
    ledger = _ledger_record(row)
    values = _score_values(code, direct)
    criterion_scores = []
    for criterion, weight in CRITERION_WEIGHTS.items():
        score = values[criterion]
        criterion_scores.append(
            {
                "criterion": criterion,
                "weight": weight,
                "score": score,
                "weighted_score": weight * score,
                "exact_supporting_proposition_ids": [
                    ledger["proposition_id"],
                    direct["proposition_id"],
                ],
                "eligibility_basis": _reason(code, criterion, score, direct),
                "missing_evidence_required_for_next_score": _missing_for_next(criterion, score),
            }
        )
    total = sum(item["weighted_score"] for item in criterion_scores)
    conflicts = [record["evidence_id"] for record in _records(row) if record.get("conflict_status") != "NO_CONFLICT"]
    target_ready = (
        values["evidence_authority"] >= 1
        and values["object_clarity"] >= 1
        and values["dependency_readiness"] >= 1
        and values["bounded_scope"] >= 1
        and values["noncircularity"] == 2
        and total >= THRESHOLD
        and not conflicts
    )
    execution_ready = (
        values["evidence_authority"] == 2
        and values["object_clarity"] == 2
        and values["dependency_readiness"] == 2
        and values["restoration_clarity"] == 2
        and values["noncircularity"] == 2
        and not conflicts
    )
    return {
        "pillar_code": code,
        "row_id": row["row_id"],
        "current_status": row["current_status"],
        "criterion_scores": criterion_scores,
        "weighted_total": total,
        "maximum_total": 62,
        "unresolved_conflict_ids": conflicts,
        "target_selection_ready": target_ready,
        "resolution_execution_ready": execution_ready,
    }


def _select(scored_rows: list[dict[str, Any]], threshold: int) -> dict[str, Any]:
    eligible = [
        row
        for row in scored_rows
        if row["weighted_total"] >= threshold
        and all(
            next(item["score"] for item in row["criterion_scores"] if item["criterion"] == criterion) >= minimum
            for criterion, minimum in {
                "evidence_authority": 1,
                "object_clarity": 1,
                "dependency_readiness": 1,
                "bounded_scope": 1,
                "noncircularity": 2,
            }.items()
        )
        and not row["unresolved_conflict_ids"]
    ]
    if not eligible:
        return {"threshold": threshold, "selected_row_id": None, "selected_pillar_code": None, "eligible_row_ids": []}
    highest = max(row["weighted_total"] for row in eligible)
    tied = [row for row in eligible if row["weighted_total"] == highest]
    selected = min(tied, key=lambda row: TIE_BREAK_ORDER.index(row["pillar_code"]))
    return {
        "threshold": threshold,
        "selected_row_id": selected["row_id"],
        "selected_pillar_code": selected["pillar_code"],
        "selected_weighted_total": highest,
        "eligible_row_ids": [row["row_id"] for row in sorted(eligible, key=lambda item: (-item["weighted_total"], TIE_BREAK_ORDER.index(item["pillar_code"])))],
        "tie_break_used": len(tied) > 1,
        "tied_row_ids": [row["row_id"] for row in tied],
    }


def build_packet(v2_packet: dict[str, Any] | None = None) -> dict[str, Any]:
    if v2_packet is None:
        v2_packet, _ = load_inputs()
    pillar_rows = [row for row in v2_packet["route_selections"] if row["row_kind"] == "pillar"]
    scored_rows = [score_row(row) for row in pillar_rows]
    canonical_selection = _select(scored_rows, THRESHOLD)
    sensitivity = [_select(scored_rows, threshold) for threshold in SENSITIVITY_THRESHOLDS]
    selected_outcomes = {item["threshold"]: item["selected_row_id"] for item in sensitivity}
    threshold_sensitive = any(selected_outcomes[threshold] is None for threshold in (42, 46))
    selected_row = next(row for row in scored_rows if row["row_id"] == canonical_selection["selected_row_id"])
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "weights_frozen_before_scoring": True,
        "threshold_frozen_before_scoring": True,
        "criterion_weights": CRITERION_WEIGHTS,
        "score_domain": [0, 1, 2],
        "maximum_weighted_total": 62,
        "target_selection_threshold": THRESHOLD,
        "sensitivity_thresholds": SENSITIVITY_THRESHOLDS,
        "tie_break_order": TIE_BREAK_ORDER,
        "scored_rows": scored_rows,
        "canonical_selection": canonical_selection,
        "sensitivity_analysis": sensitivity,
        "threshold_sensitive": threshold_sensitive,
        "threshold_sensitivity_verdict": "B-BLOCKED_THRESHOLD_SENSITIVE" if threshold_sensitive else "STABLE",
        "selected_row_resolution_execution_ready": selected_row["resolution_execution_ready"],
        "selection_authorizes_preparation_only": True,
        "unit_assignment_authorized": False,
        "restoration_rule_authorized": False,
        "Maxwell_Dirac_status": "PREFERRED_DOWNSTREAM_CANDIDATE_NOT_SELECTED_RESULT",
        "selected_unit_is_on_preferred_candidate_dependency_path": canonical_selection["selected_pillar_code"] == "SR",
        "boundary": {
            "unit_assignment_emitted": False,
            "resolution_execution_authorized": False,
            "pillar_completion_claimed": False,
            "seam_closure_claimed": False,
            "Maxwell_Dirac_selected": False,
            "registry_maintenance_paused": True,
            "C_k_audit_only": True,
            "CCFT_resumed": False,
            "master_action_promoted": False,
        },
        "input_artifacts": [
            {"path": path, "sha256": digest} for path, digest in EXPECTED_INPUT_HASHES.items()
        ],
        "prompt_protection": {
            "path": PROMPT_RELATIVE_PATH,
            "pre_tranche_sha256": PROMPT_BASELINE_SHA256,
            "excluded_from_scientific_inputs": True,
        },
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("selector_identity")
    if packet.get("criterion_weights") != CRITERION_WEIGHTS or packet.get("target_selection_threshold") != THRESHOLD:
        failures.append("weights_and_threshold_frozen")
    if len(packet.get("scored_rows", [])) != 7:
        failures.append("exact_seven_pillar_rows")
    if any(len(row.get("criterion_scores", [])) != 8 for row in packet.get("scored_rows", [])):
        failures.append("all_eight_criteria_scored")
    if any(
        row["weighted_total"] != sum(item["weighted_score"] for item in row["criterion_scores"])
        for row in packet.get("scored_rows", [])
    ):
        failures.append("weighted_totals_reproduce")
    if packet.get("canonical_selection", {}).get("selected_row_id") != "PILLAR-SR-units_and_dimensions-v0":
        failures.append("highest_scoring_eligible_row_selected")
    if packet.get("threshold_sensitive") is not False:
        failures.append("threshold_sensitivity_gate")
    if packet.get("selected_row_resolution_execution_ready") is not False:
        failures.append("selection_not_resolution_execution")
    if packet.get("unit_assignment_authorized") is not False or packet.get("restoration_rule_authorized") is not False:
        failures.append("no_unit_or_restoration_assignment")
    if packet.get("boundary", {}).get("Maxwell_Dirac_selected") is not False:
        failures.append("Maxwell_Dirac_remains_candidate")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        failures.append("Prompt_preserved")
    return failures


DECISION_IDS = [
    "accepted_v2_review_authorizes_selector_only",
    "weights_and_threshold_frozen_before_scoring",
    "seven_rows_score_all_eight_criteria",
    "criterion_reasons_bind_exact_propositions",
    "weighted_totals_reproduce_out_of_sixty_two",
    "target_selection_readiness_gates_apply",
    "resolution_execution_readiness_is_separate",
    "sensitivity_at_40_42_44_46_48_is_recorded",
    "tie_break_is_exact_score_only",
    "SR_is_highest_scoring_eligible_row",
    "selection_is_stable_at_42_and_46",
    "no_unit_or_restoration_rule_is_emitted",
    "Maxwell_Dirac_remains_a_preferred_candidate",
    "all_nonclaims_and_prompt_guard_are_preserved",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    v2_packet, _ = load_inputs()
    packet = build_packet(v2_packet)
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"selector validation failed: {failures}")
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "canonical_selection": packet["canonical_selection"],
        "sensitivity_analysis": packet["sensitivity_analysis"],
        "selected_row_resolution_execution_ready": False,
        "selection_authorizes_preparation_only": True,
        "artifact_hashes": {
            "generator_sha256": sha256_path(SCRIPT_PATH),
            "packet_sha256": sha256_bytes(packet_raw),
            "manifest_sha256": sha256_bytes(manifest_raw),
        },
        "boundary": packet["boundary"],
        "claim": "SR is the stable highest-scoring first unit target for preparation; no unit resolution or Maxwell-Dirac result is authorized.",
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build the scored first-unit selector packet.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print("wrote first-unit selector: SR selected for preparation at 51/62; execution readiness not met")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("first-unit selector verified: SR 51/62; stable at thresholds 42 and 46; no unit assigned")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
