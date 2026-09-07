"""Generate the frozen v6 payload-mismatch ledger and execution run-log seed.

The generated records are deliberately NOT_RUN.  Actual attempts copy their
frozen row/check inventories into new result artifacts and add observations;
they never edit these seed records or the v1 evidence bundle.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any, Iterable, Mapping

from formal.python.toe.generic_runner.verified_calculator.canonical import digest


RELEASE = Path("formal/docs/release")
REFERENCE_BUNDLE = RELEASE / "verified_calculator/c03_rv_exact/93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f.json"
PAYLOAD_CONTRACT = RELEASE / "VERIFIED_CALCULATOR_C03_RV_EXACT_PAYLOAD_EQUIVALENCE_TEST_20260907_v1.json"
CHECKLIST = RELEASE / "VERIFIED_CALCULATOR_C03_RV_EXACT_V6_EXECUTION_CHECKLIST_20260907_v1.md"
MISMATCH_REPORT = RELEASE / "VERIFIED_CALCULATOR_C03_RV_EXACT_V6_PAYLOAD_MISMATCH_REPORT_20260907_v1.json"
RUN_LOG = RELEASE / "VERIFIED_CALCULATOR_C03_RV_EXACT_V6_EXECUTION_RUN_LOG_20260907_v1.json"


def _json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_text_sha256(raw: bytes) -> str:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ValueError("CANONICAL_TEXT_V1_BOM")
    text = raw.decode("utf-8", errors="strict").replace("\r\n", "\n").replace("\r", "\n")
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _validated_definition(path: Path, hash_field: str) -> tuple[dict[str, Any], str]:
    value = _json(path)
    claimed = value.pop(hash_field)
    actual = digest(value, domain=value["schema_id"])
    if claimed != actual:
        raise ValueError(f"SELF_HASH_MISMATCH:{path}:{claimed}:{actual}")
    value[hash_field] = claimed
    return value, claimed


def _row(
    surface_id: str,
    ordinal: int,
    subject_key: str,
    locators: Iterable[str],
    reference_object: Any,
) -> dict[str, Any]:
    row_id = f"{surface_id}:{ordinal:04d}:{subject_key}"
    return {
        "row_id": row_id,
        "surface_id": surface_id,
        "ordinal": ordinal,
        "subject_key": subject_key,
        "reference": {
            "locators": list(locators),
            "object_hash": digest(reference_object, domain=f"VPCV6ReferenceRow:{surface_id}"),
            "object_hash_purpose": "REFERENCE_CUSTODY_ONLY__NOT_AN_EQUIVALENCE_DISPOSITION",
        },
        "amended_projection_hash": None,
        "disposition": "NOT_RUN",
        "allowed_delta_class": None,
        "mismatch_fields": [],
        "evidence": [],
        "notes": None,
    }


def _index_unique(rows: Iterable[Mapping[str, Any]], key: str) -> dict[str, Mapping[str, Any]]:
    result: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        identity = str(row[key])
        if identity in result:
            raise ValueError(f"DUPLICATE_ID:{key}:{identity}")
        result[identity] = row
    return result


def _challenge_instance_rows(bundle: Mapping[str, Any]) -> list[dict[str, Any]]:
    specs = _index_unique(bundle["challenge_specs"], "challenge_id")
    spec_by_hash = {digest(row, domain="ChallengeSpecV1"): identity for identity, row in specs.items()}
    packets_by_hash = {
        digest(row, domain="ChallengePacketV1"): row for row in bundle["challenge_packets"]
    }
    rows: list[dict[str, Any]] = []
    keys: set[str] = set()
    for result in bundle["verification_receipt"]["challenge_results"]:
        packet_hash = result["challenge_packet_hash"]
        packet = packets_by_hash.get(packet_hash)
        if packet is None:
            raise ValueError(f"CHALLENGE_PACKET_NOT_FOUND:{packet_hash}")
        challenge_id = spec_by_hash.get(packet["challenge_spec_hash"])
        if challenge_id != result["challenge_id"]:
            raise ValueError(f"CHALLENGE_SPEC_RESULT_MISMATCH:{result['challenge_id']}")
        key = f"{challenge_id}|{packet['injection_node']}|{packet['concrete_seed']}"
        if key in keys:
            raise ValueError(f"DUPLICATE_CHALLENGE_INSTANCE:{key}")
        keys.add(key)
        rows.append(
            {
                "subject_key": key,
                "packet_hash": packet_hash,
                "packet": packet,
                "result": result,
            }
        )
    return sorted(rows, key=lambda row: row["subject_key"])


def build_mismatch_report(repo_root: Path) -> dict[str, Any]:
    release = repo_root / RELEASE
    contract, contract_hash = _validated_definition(repo_root / PAYLOAD_CONTRACT, "definition_hash")
    bundle_path = repo_root / REFERENCE_BUNDLE
    bundle_raw = bundle_path.read_bytes()
    if hashlib.sha256(bundle_raw).hexdigest() != contract["reference"]["raw_file_sha256"]:
        raise ValueError("REFERENCE_BUNDLE_RAW_HASH_MISMATCH")
    bundle = json.loads(bundle_raw)

    nodes = _index_unique(bundle["candidate"]["graph"]["nodes"], "node_id")
    source_bindings = _index_unique(bundle["candidate"]["source_bindings"], "node_id")
    traces = _index_unique(bundle["runtime_certificate"]["node_trace"], "node_id")
    receipt_outputs = _index_unique(bundle["verification_receipt"]["outputs"], "root_id")
    claims = _index_unique(bundle["verification_receipt"]["claim_ledger"], "claim_id")
    authority_wrapper = bundle["authority_bindings"][0]
    authorities = authority_wrapper["claim_bindings"]

    source_nodes = sorted((row for row in nodes.values() if row["kind"] == "SOURCE"), key=lambda row: row["node_id"])
    derived_nodes = sorted((row for row in nodes.values() if row["kind"] == "DERIVED"), key=lambda row: row["node_id"])
    output_nodes = sorted((row for row in nodes.values() if row["kind"] == "OUTPUT"), key=lambda row: row["node_id"])
    source_evidence = bundle["verification_receipt"]["source_evidence"]
    source_evidence_by_id: dict[str, Mapping[str, Any]] = {}
    for evidence in source_evidence:
        locator = str(evidence["material_contract"]["canonical_locator"])
        match = re.fullmatch(r"/nodes/([^/]+)/profile_value_digest", locator)
        if match is None:
            raise ValueError(f"SOURCE_EVIDENCE_LOCATOR:{locator}")
        identity = match.group(1)
        if identity in source_evidence_by_id:
            raise ValueError(f"DUPLICATE_SOURCE_EVIDENCE:{identity}")
        source_evidence_by_id[identity] = evidence
    if set(source_evidence_by_id) != {row["node_id"] for row in source_nodes}:
        raise ValueError("SOURCE_EVIDENCE_ID_SET")

    surface_contracts = {row["surface_id"]: row for row in contract["comparison_surfaces"]}
    rows: list[dict[str, Any]] = []

    convention_object = {
        "frozen_semantics": bundle["frozen_semantics"],
        "requested_roots": bundle["request"]["requested_roots"],
        "input_contracts": bundle["request"]["inputs"],
        "value_types": {identity: row["value_type"] for identity, row in nodes.items()},
    }
    rows.append(_row("PE-00-SCOPE-AND-MODEL-CONVENTIONS", 1, "C03_RV_MODEL_CONVENTIONS", ["frozen_semantics", "request", "candidate.graph.nodes[*].value_type"], convention_object))

    for ordinal, node in enumerate(source_nodes, 1):
        identity = node["node_id"]
        reference_object = {
            "node": node,
            "source_binding": source_bindings[identity],
            "source_evidence": source_evidence_by_id[identity],
            "runtime_trace": traces[identity],
        }
        rows.append(_row("PE-01-SOURCES", ordinal, identity, [f"candidate.graph.nodes[{identity}]", f"candidate.source_bindings[{identity}]", f"verification_receipt.source_evidence[{identity}]"], reference_object))

    for ordinal, node in enumerate(derived_nodes, 1):
        identity = node["node_id"]
        rows.append(_row("PE-02-DERIVED-GRAPH", ordinal, identity, [f"candidate.graph.nodes[{identity}]", f"runtime_certificate.node_trace[{identity}]"], {"node": node, "runtime_trace": traces[identity]}))

    operation_ids = surface_contracts["PE-03-TRUSTED-OPERATION-VOCABULARY"]["required_ids"]
    for ordinal, operation in enumerate(operation_ids, 1):
        applications = [row for row in derived_nodes if row["operation"] == operation]
        rows.append(_row("PE-03-TRUSTED-OPERATION-VOCABULARY", ordinal, operation, [f"candidate.graph.nodes[operation={operation}]"], {"operation": operation, "applications": applications}))

    root_ids = surface_contracts["PE-04-AUTHORITATIVE-ROOTS"]["required_ids"]
    output_by_id = {row["node_id"]: row for row in output_nodes}
    for ordinal, root_id in enumerate(root_ids, 1):
        claim_id = root_id.replace(".OUTPUT.", ".claim.")
        reference_object = {
            "node": output_by_id[root_id],
            "claimed_output": bundle["candidate"]["claimed_outputs"][root_id],
            "receipt_output": receipt_outputs[root_id],
            "certificate_value_digest": bundle["runtime_certificate"]["output_node_value_digests"][root_id],
            "claim_id": claim_id,
        }
        rows.append(_row("PE-04-AUTHORITATIVE-ROOTS", ordinal, root_id, [f"candidate.graph.nodes[{root_id}]", f"verification_receipt.outputs[{root_id}]"], reference_object))

    challenge_specs = sorted(bundle["challenge_specs"], key=lambda row: row["challenge_id"])
    for ordinal, spec in enumerate(challenge_specs, 1):
        identity = spec["challenge_id"]
        rows.append(_row("PE-05-CHALLENGE-SPECIFICATIONS", ordinal, identity, [f"challenge_specs[{identity}]"], spec))

    for ordinal, instance in enumerate(_challenge_instance_rows(bundle), 1):
        rows.append(_row("PE-06-CHALLENGE-INSTANCES-AND-RESULTS", ordinal, instance["subject_key"], [f"challenge_packets[{instance['packet_hash']}]", f"verification_receipt.challenge_results[{instance['subject_key']}]"], {"packet": instance["packet"], "result": instance["result"]}))

    for ordinal, claim_id in enumerate(sorted(claims), 1):
        rows.append(_row("PE-07-CLAIM-LEDGER", ordinal, claim_id, [f"verification_receipt.claim_ledger[{claim_id}]"], claims[claim_id]))

    for ordinal, claim_id in enumerate(sorted(authorities), 1):
        rows.append(_row("PE-08-SCIENTIFIC-AUTHORITY", ordinal, claim_id, [f"authority_bindings[0].claim_bindings[{claim_id}]"], {"claim_binding": authorities[claim_id], "calculator_profile_review_status": authority_wrapper["calculator_profile_review_status"]}))

    scope_object = {
        "bundle_scientific_promotion": bundle["verification_receipt"]["scientific_promotion"],
        "product_v1_release": bundle["verification_receipt"]["product_v1_release"],
        "production_activation": bundle["verification_receipt"]["production_activation"],
        "stochastic_experiments": bundle["request"]["stochastic_experiments"],
    }
    rows.append(_row("PE-09-NON-PROMOTION-AND-EXACT-SCOPE", 1, "NON_PROMOTION_AND_EXACT_SCOPE", ["request.stochastic_experiments", "verification_receipt.*promotion*"], scope_object))

    expected_by_surface = {row["surface_id"]: row["required_rows"] for row in contract["comparison_surfaces"]}
    actual_by_surface = Counter(row["surface_id"] for row in rows)
    if dict(actual_by_surface) != expected_by_surface or len(rows) != 643:
        raise ValueError(f"PAYLOAD_ROW_CENSUS:{dict(actual_by_surface)}:{expected_by_surface}:{len(rows)}")
    if len({row["row_id"] for row in rows}) != len(rows):
        raise ValueError("DUPLICATE_PAYLOAD_ROW_ID")

    report: dict[str, Any] = {
        "schema_id": "VerifiedCalculatorC03RVExactV6PayloadMismatchReportV1",
        "report_id": "C03_RV_EXACT_V6_PAYLOAD_MISMATCH_REPORT_20260907_v1",
        "record_kind": "IMMUTABLE_NOT_RUN_ROW_INVENTORY",
        "status": "NOT_RUN",
        "payload_test_path": PAYLOAD_CONTRACT.as_posix(),
        "payload_test_hash": contract_hash,
        "reference_bundle": {
            "path": REFERENCE_BUNDLE.as_posix(),
            "bundle_id": contract["reference"]["bundle_id"],
            "raw_file_sha256": contract["reference"]["raw_file_sha256"],
        },
        "amended_bundle": None,
        "comparison_execution": None,
        "required_row_count": 643,
        "surface_counts": dict(actual_by_surface),
        "summary": {
            "NOT_RUN": 643,
            "MATCH": 0,
            "ALLOWED_EVIDENCE_DELTA": 0,
            "MISMATCH": 0,
            "MISSING": 0,
            "DUPLICATE": 0,
            "UNCLASSIFIED_DELTA": 0,
        },
        "rows": rows,
        "execution_rule": "An actual attempt copies this complete row inventory into a new immutable result, fills amended projections and evidence, and recomputes its own result hash. This seed report is never edited into a PASS.",
        "final_disposition": "NOT_RUN",
        "scientific_promotion": False,
        "product_v1_release": False,
        "production_activation": False,
    }
    report["report_hash"] = digest(report, domain=report["schema_id"])
    return report


def _checklist_items(markdown: str) -> list[dict[str, Any]]:
    items: list[dict[str, Any]] = []
    section = "UNSECTIONED"
    for line in markdown.splitlines():
        if line.startswith("## "):
            section = line[3:].strip()
            continue
        match = re.fullmatch(r"- \[ \] (.+)", line)
        if match:
            items.append({"section": section, "instruction": match.group(1)})
    return items


def build_run_log(repo_root: Path) -> dict[str, Any]:
    checklist_path = repo_root / CHECKLIST
    checklist_raw = checklist_path.read_bytes()
    items = _checklist_items(checklist_raw.decode("utf-8", errors="strict"))
    if len(items) != 104:
        raise ValueError(f"RUN_LOG_CHECK_COUNT:{len(items)}")
    checks = []
    for ordinal, item in enumerate(items, 1):
        checks.append(
            {
                "check_id": f"V6-RUN-{ordinal:03d}",
                "ordinal": ordinal,
                "section": item["section"],
                "instruction": item["instruction"],
                "mandatory": True,
                "status": "NOT_RUN",
                "started_at": None,
                "completed_at": None,
                "operator": None,
                "command": None,
                "exit_code": None,
                "evidence": [],
                "failure_code": None,
                "notes": None,
            }
        )
    log: dict[str, Any] = {
        "schema_id": "VerifiedCalculatorC03RVExactV6ExecutionRunLogV1",
        "run_log_id": "C03_RV_EXACT_V6_EXECUTION_RUN_LOG_20260907_v1",
        "record_kind": "IMMUTABLE_NOT_RUN_CHECK_INVENTORY",
        "status": "NOT_RUN",
        "checklist_path": CHECKLIST.as_posix(),
        "checklist_canonical_text_v1_sha256": _canonical_text_sha256(checklist_raw),
        "attempt_id": None,
        "tested_commit": None,
        "operator": None,
        "started_at": None,
        "completed_at": None,
        "required_check_count": 104,
        "summary": {"NOT_RUN": 104, "PASS": 0, "FAIL": 0, "INCONCLUSIVE": 0, "BLOCKED": 0},
        "checks": checks,
        "execution_rule": "An actual attempt copies all 104 checks into a new immutable run log, records observations and evidence, stops at the first mandatory failure, and never edits this seed inventory or a prior attempt.",
        "final_disposition": "NOT_RUN",
        "scientific_promotion": False,
        "product_v1_release": False,
        "production_activation": False,
    }
    log["run_log_hash"] = digest(log, domain=log["schema_id"])
    return log


def _render(value: Mapping[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=True) + "\n"


def write_or_check(path: Path, value: Mapping[str, Any], check: bool) -> None:
    rendered = _render(value)
    if check:
        if not path.is_file() or path.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"generated record is stale: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(rendered, encoding="utf-8", newline="\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    repo_root = args.repo_root.resolve()
    write_or_check(repo_root / MISMATCH_REPORT, build_mismatch_report(repo_root), args.check)
    write_or_check(repo_root / RUN_LOG, build_run_log(repo_root), args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
