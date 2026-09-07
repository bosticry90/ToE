"""Populate the frozen 643-row v6 payload-equivalence inventory."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import re
from typing import Any, Mapping

from formal.python.toe.generic_runner.verified_calculator.canonical import canonical_bytes, digest


def _index(rows, key):
    result = {row[key]: row for row in rows}
    if len(result) != len(rows):
        raise ValueError(f"DUPLICATE:{key}")
    return result


def _mismatch_paths(left: Any, right: Any, path: str = "$") -> list[str]:
    if type(left) is not type(right):
        return [path]
    if isinstance(left, Mapping):
        paths: list[str] = []
        for key in sorted(set(left) | set(right)):
            child = f"{path}.{key}"
            if key not in left or key not in right:
                paths.append(child)
            else:
                paths.extend(_mismatch_paths(left[key], right[key], child))
        return paths
    if isinstance(left, list):
        if len(left) != len(right):
            return [f"{path}.length"]
        paths = []
        for index, (old, new) in enumerate(zip(left, right)):
            paths.extend(_mismatch_paths(old, new, f"{path}[{index}]"))
        return paths
    return [] if left == right else [path]


def _source_evidence(bundle):
    result = {}
    for row in bundle["verification_receipt"]["source_evidence"]:
        match = re.fullmatch(r"/nodes/([^/]+)/profile_value_digest", row["material_contract"]["canonical_locator"])
        if match is None or match.group(1) in result:
            raise ValueError("SOURCE_EVIDENCE_LOCATOR")
        result[match.group(1)] = row
    return result


def _value_type(node):
    value = dict(node["value_type"])
    if "shape" not in value:
        if value["mathematical_kind"] == "EXACT_TENSOR":
            value["shape"] = list(node["claimed_value"]["shape"])
        elif value["mathematical_kind"] in {"EXACT_SCALAR", "EXACT_ATOM", "EXACT_BOOLEAN"}:
            value["shape"] = []
        else:
            value["shape"] = None
    return value


def _node(node):
    return {**node, "value_type": _value_type(node)}


def _trace(bundle):
    return _index(bundle["runtime_certificate"]["node_trace"], "node_id")


def _challenge_instances(bundle):
    specs = _index(bundle["challenge_specs"], "challenge_id")
    spec_ids = {digest(row, "ChallengeSpecV1"): identity for identity, row in specs.items()}
    packets = {digest(row, "ChallengePacketV1"): row for row in bundle["challenge_packets"]}
    result = {}
    for observed in bundle["verification_receipt"]["challenge_results"]:
        packet = packets[observed["challenge_packet_hash"]]
        challenge_id = spec_ids[packet["challenge_spec_hash"]]
        key = f"{challenge_id}|{packet['injection_node']}|{packet['concrete_seed']}"
        result[key] = {
            "packet": {
                "challenge_id": challenge_id,
                "injection_node": packet["injection_node"],
                "permitted_descendants": packet["permitted_descendants"],
                "affected_roots": packet["affected_roots"],
                "concrete_seed": packet["concrete_seed"],
            },
            "result": {
                key: value for key, value in observed.items()
                if key not in {"challenge_spec_hash", "challenge_packet_hash"}
            },
        }
    return result


def _root_projection(bundle, identity):
    nodes = _index(bundle["candidate"]["graph"]["nodes"], "node_id")
    outputs = _index(bundle["verification_receipt"]["outputs"], "root_id")
    output = outputs[identity]
    coverage = output["challenge_coverage"]
    normalized_coverage = {
        "complete": coverage["complete"],
        "applicable_result_count": coverage["applicable_result_count"],
        "failed_challenge_count": len(coverage["failed_challenges"]),
        "mandatory_applicable_count": len(coverage["mandatory_applicable_packet_hashes"]),
        "mandatory_missing_or_failed_count": len(coverage["mandatory_missing_or_failed"]),
    }
    normalized_output = {
        "root_id": output["root_id"], "value": output["value"],
        "verification_class": output["verification_class"],
        "challenge_coverage": normalized_coverage,
        "uncertainty_semantics": output["uncertainty_semantics"],
    }
    return {
        "node": _node(nodes[identity]),
        "claimed_output": bundle["candidate"]["claimed_outputs"][identity],
        "receipt_output": normalized_output,
        "certificate_value_digest": bundle["runtime_certificate"]["output_node_value_digests"][identity],
        "claim_id": identity.replace(".OUTPUT.", ".claim."),
    }


def projection(bundle: Mapping[str, Any], surface: str, subject: str) -> Any:
    nodes = _index(bundle["candidate"]["graph"]["nodes"], "node_id")
    traces = _trace(bundle)
    if surface == "PE-00-SCOPE-AND-MODEL-CONVENTIONS":
        return {
            "frozen_semantics": bundle["frozen_semantics"],
            "requested_roots": bundle["request"]["requested_roots"],
            "input_contracts": bundle["request"]["inputs"],
            "value_types": {identity: _value_type(node) for identity, node in nodes.items()},
        }
    if surface == "PE-01-SOURCES":
        bindings = _index(bundle["candidate"]["source_bindings"], "node_id")
        evidence = _source_evidence(bundle)
        return {"node": _node(nodes[subject]), "source_binding": bindings[subject], "source_evidence": evidence[subject], "runtime_trace": traces[subject]}
    if surface == "PE-02-DERIVED-GRAPH":
        return {"node": _node(nodes[subject]), "runtime_trace": traces[subject]}
    if surface == "PE-03-TRUSTED-OPERATION-VOCABULARY":
        applications = [_node(row) for row in nodes.values() if row["kind"] == "DERIVED" and row["operation"] == subject]
        return {"operation": subject, "applications": sorted(applications, key=lambda row: row["node_id"])}
    if surface == "PE-04-AUTHORITATIVE-ROOTS":
        return _root_projection(bundle, subject)
    if surface == "PE-05-CHALLENGE-SPECIFICATIONS":
        return _index(bundle["challenge_specs"], "challenge_id")[subject]
    if surface == "PE-06-CHALLENGE-INSTANCES-AND-RESULTS":
        return _challenge_instances(bundle)[subject]
    if surface == "PE-07-CLAIM-LEDGER":
        claim = dict(_index(bundle["verification_receipt"]["claim_ledger"], "claim_id")[subject])
        claim.pop("supporting_receipts", None)
        return claim
    if surface == "PE-08-SCIENTIFIC-AUTHORITY":
        authority = bundle["authority_bindings"][0]
        return {"claim_binding": authority["claim_bindings"][subject], "calculator_profile_review_status": authority["calculator_profile_review_status"]}
    if surface == "PE-09-NON-PROMOTION-AND-EXACT-SCOPE":
        receipt = bundle["verification_receipt"]
        return {"bundle_scientific_promotion": receipt["scientific_promotion"], "product_v1_release": receipt["product_v1_release"], "production_activation": receipt["production_activation"], "stochastic_experiments": bundle["request"]["stochastic_experiments"]}
    raise ValueError(f"UNKNOWN_SURFACE:{surface}")


def compare(seed_path: Path, reference_path: Path, amended_path: Path, output_path: Path, attempt_id: str) -> dict[str, Any]:
    seed = json.loads(seed_path.read_text(encoding="utf-8"))
    reference = json.loads(reference_path.read_text(encoding="utf-8"))
    amended = json.loads(amended_path.read_text(encoding="utf-8"))
    rows = []
    for template in seed["rows"]:
        row = dict(template)
        left = projection(reference, row["surface_id"], row["subject_key"])
        right = projection(amended, row["surface_id"], row["subject_key"])
        left_hash = digest(left, f"VPCV6ScientificProjection:{row['surface_id']}")
        right_hash = digest(right, f"VPCV6ScientificProjection:{row['surface_id']}")
        row["reference_projection"] = left
        row["reference_projection_hash"] = left_hash
        row["amended_projection"] = right
        row["amended_projection_hash"] = right_hash
        row["disposition"] = "MATCH" if left == right else "MISMATCH"
        row["mismatch_fields"] = _mismatch_paths(left, right)
        row["evidence"] = [{"reference_projection_hash": left_hash, "amended_projection_hash": right_hash}]
        row["notes"] = "Explicit shape metadata is normalized from the exact value for the v1 reference." if left == right and row["surface_id"] in {"PE-00-SCOPE-AND-MODEL-CONVENTIONS", "PE-01-SOURCES", "PE-02-DERIVED-GRAPH", "PE-03-TRUSTED-OPERATION-VOCABULARY", "PE-04-AUTHORITATIVE-ROOTS"} else None
        rows.append(row)
    summary = Counter(row["disposition"] for row in rows)
    for status in seed["summary"]:
        summary.setdefault(status, 0)
    result = {
        **{key: value for key, value in seed.items() if key not in {"report_id", "record_kind", "status", "amended_bundle", "comparison_execution", "summary", "rows", "final_disposition", "report_hash"}},
        "schema_id": "VerifiedCalculatorC03RVExactPayloadEquivalenceResultV1",
        "report_id": f"C03_RV_EXACT_V6_PAYLOAD_MISMATCH_REPORT_{attempt_id}",
        "record_kind": "IMMUTABLE_EXECUTED_COMPARISON_RESULT",
        "status": "PASS" if summary["MISMATCH"] == summary["MISSING"] == summary["DUPLICATE"] == summary["UNCLASSIFIED_DELTA"] == 0 and summary["MATCH"] + summary["ALLOWED_EVIDENCE_DELTA"] == len(rows) else "FAIL",
        "amended_bundle": {"path": amended_path.as_posix(), "bundle_id": amended_path.stem},
        "comparison_execution": {"attempt_id": attempt_id, "completed_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"), "engine": "formal/python/tools/compare_vpc_v6_payload.py", "comparison_oracle_access": "COMPARATOR_ONLY_AFTER_TRUSTED_EXECUTION"},
        "summary": dict(summary),
        "rows": rows,
        "final_disposition": "643_OF_643_SCIENTIFIC_PAYLOAD_OBLIGATIONS_MATCH" if summary["MATCH"] == len(rows) else "PAYLOAD_EQUIVALENCE_FAILED",
        "scientific_promotion": False,
        "product_v1_release": False,
        "production_activation": False,
    }
    result["report_hash"] = digest(result, result["schema_id"])
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(canonical_bytes(result))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=Path, required=True)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--amended", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--attempt-id", required=True)
    args = parser.parse_args()
    result = compare(args.seed, args.reference, args.amended, args.output, args.attempt_id)
    print(json.dumps({"status": result["status"], "summary": result["summary"], "report_hash": result["report_hash"]}, sort_keys=True))


if __name__ == "__main__":
    main()
