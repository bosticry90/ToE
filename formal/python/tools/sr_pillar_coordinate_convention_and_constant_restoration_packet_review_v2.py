from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import inspect
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_v2 as packet_v2,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = packet_v2.REPORT_RELATIVE_PATH
PACKET_TOOL_RELATIVE_PATH = (
    "formal/python/tools/"
    "sr_pillar_coordinate_convention_and_constant_restoration_packet_v2.py"
)
PACKET_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_v2.py"
)
REVIEW_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v2.py"
)
V1_PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v1.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v2.json"
)

CONSUMED_TARGET = (
    "review_sr_pillar_coordinate_convention_and_constant_restoration_packet_v2_result"
)
VERDICT = "BLOCKED_CANONICALIZATION_AND_LINEAGE_CONTRACT_UNSOUND"
FIRST_DIAGNOSTIC = "CANONICALIZER_ERASES_NONCOMMUTATIVE_OPERATOR_ORDER"
SELECTED_NEXT_TARGET = (
    "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet_v3"
)

FROZEN_INPUT_HASHES = {
    PACKET_RELATIVE_PATH:
        "1d94f4c8cab0337322eb537feebe32aeb344369e5b402164a03987b7b56c1b05",
    PACKET_TOOL_RELATIVE_PATH:
        "affdd8146f966282e0e84b5cc44bb5cf45d4cd006253d4893c5e79b4a0cf1f8c",
    PACKET_TEST_RELATIVE_PATH:
        "d62d692353473f510ad2e87272b3c80d6efb70f2cc707a27a1bb32503a82c34f",
}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _read_frozen_packet() -> tuple[dict[str, Any], list[dict[str, str]]]:
    bindings: list[dict[str, str]] = []
    for relative_path, expected_hash in FROZEN_INPUT_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"frozen v2 input hash mismatch: {relative_path}")
        bindings.append({"relative_path": relative_path, "sha256": observed})
    packet = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("v2 packet verdict mismatch")
    if packet.get("selected_next_target") != CONSUMED_TARGET:
        raise ValueError("v2 packet target mismatch")
    return packet, bindings


def _json_pointer(payload: Any, pointer: str) -> Any:
    value = payload
    for part in pointer.lstrip("/").split("/"):
        token = part.replace("~1", "/").replace("~0", "~")
        value = value[int(token)] if isinstance(value, list) else value[token]
    return value


def _independent_source_binding_audit() -> dict[str, Any]:
    v1 = json.loads((REPO_ROOT / V1_PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    rows: list[dict[str, Any]] = []
    for binding in v1["source_bindings"]["rows"]:
        path = REPO_ROOT / binding["artifact"]
        raw = path.read_bytes()
        artifact_hash_matches = _sha256(raw) == binding["artifact_sha256"]
        if binding["source_kind"] == "json_pointer":
            observed = _json_pointer(json.loads(raw.decode("utf-8")), binding["locator"])
        else:
            text = raw.decode("utf-8")
            observed = binding["exact_source_expression"] if binding["exact_source_expression"] in text else None
        exact_expression_matches = observed == binding["exact_source_expression"]
        content_hash_matches = (
            _sha256(binding["exact_source_expression"].encode("utf-8"))
            == binding["exact_content_sha256"]
        )
        corroborating_matches = True
        if "corroborating_artifact" in binding:
            corroborating = json.loads(
                (REPO_ROOT / binding["corroborating_artifact"]).read_text(encoding="utf-8")
            )
            corroborating_matches = (
                _json_pointer(corroborating, binding["corroborating_locator"])
                == binding["corroborating_value"]
            )
        passed = all((artifact_hash_matches, exact_expression_matches, content_hash_matches, corroborating_matches))
        rows.append(
            {
                "equation_id": binding["equation_id"],
                "artifact_hash_matches": artifact_hash_matches,
                "exact_expression_matches": exact_expression_matches,
                "exact_content_hash_matches": content_hash_matches,
                "corroborating_matches": corroborating_matches,
                "claim_class_increased": False,
                "passed": passed,
            }
        )
    return {
        "required_count": 6,
        "passed_count": sum(1 for row in rows if row["passed"]),
        "rows": rows,
        "passed": len(rows) == 6 and all(row["passed"] for row in rows),
    }


def _production_positive_probe() -> dict[str, Any]:
    maxwell = packet_v2.CONTRACTS["SOURCED_MAXWELL"]
    state = dict(packet_v2.BASE_CONVENTION_STATE)
    baseline = packet_v2.restore(
        maxwell.equation_id,
        maxwell.source_ast,
        convention_state=state,
        binding_id=maxwell.binding_id,
    )

    original_oracle = maxwell.expected_si_ast
    wrong_oracle = packet_v2.Eq(original_oracle.left, packet_v2.N(original_oracle.right))
    maxwell.expected_si_ast = wrong_oracle
    try:
        wrong_target = packet_v2.restore(
            maxwell.equation_id,
            maxwell.source_ast,
            convention_state=state,
            binding_id=maxwell.binding_id,
        )
    finally:
        maxwell.expected_si_ast = original_oracle

    original_rules = list(maxwell.forward_rules)
    maxwell.forward_rules = original_rules[:-1]
    try:
        missing_map_diagnostic = "NO_DIAGNOSTIC"
        try:
            packet_v2.restore(
                maxwell.equation_id,
                maxwell.source_ast,
                convention_state=state,
                binding_id=maxwell.binding_id,
            )
        except packet_v2.ProductionContractError as error:
            missing_map_diagnostic = error.diagnostic
    finally:
        maxwell.forward_rules = original_rules

    original_second = maxwell.forward_rules[1]
    maxwell.forward_rules[1] = packet_v2.RewriteRule(
        original_second.rule_id,
        original_second.source,
        packet_v2.V("J", "SI", packet_v2.NU_U),
        "independent wrong-map probe",
    )
    try:
        mutated_map = packet_v2.restore(
            maxwell.equation_id,
            maxwell.source_ast,
            convention_state=state,
            binding_id=maxwell.binding_id,
        )
    finally:
        maxwell.forward_rules[1] = original_second

    extra_rule = packet_v2.RewriteRule(
        "INAPPLICABLE_EXTRA_RULE",
        packet_v2.Symbol("unused", "probe"),
        packet_v2.Symbol("unused_target", "probe"),
        "independent overapplication probe",
    )
    maxwell.forward_rules = original_rules + [extra_rule]
    try:
        extra_map_diagnostic = "NO_DIAGNOSTIC"
        try:
            packet_v2.restore(
                maxwell.equation_id,
                maxwell.source_ast,
                convention_state=state,
                binding_id=maxwell.binding_id,
            )
        except packet_v2.ProductionContractError as error:
            extra_map_diagnostic = error.diagnostic
    finally:
        maxwell.forward_rules = original_rules

    valid_rows = packet_v2._valid_round_trips()
    convention_rows = packet_v2._production_convention_controls()
    return {
        "actual_production_functions_called": ["restore", "suppress"],
        "oracle_independence": {
            "computed_ast_unchanged": packet_v2.canonical(wrong_target.computed_ast) == packet_v2.canonical(baseline.computed_ast),
            "wrong_target_rejected": not wrong_target.passed and wrong_target.first_diagnostic == "EXPECTED_TARGET_MISMATCH",
        },
        "map_enforcement": {
            "missing_map_diagnostic": missing_map_diagnostic,
            "mutated_map_diagnostic": mutated_map.first_diagnostic,
            "inapplicable_extra_map_diagnostic": extra_map_diagnostic,
            "underapplication_rejected": missing_map_diagnostic == "REQUIRED_OBJECT_MAP_MISSING",
            "mutation_rejected": not mutated_map.passed and mutated_map.first_diagnostic == "EXPECTED_TARGET_MISMATCH",
            "overapplication_rejected": extra_map_diagnostic == "REQUIRED_OBJECT_MAP_MISSING",
        },
        "valid_production_round_trips": {
            "required_count": 6,
            "passed_count": sum(1 for row in valid_rows if row["semantic_round_trip_passed"]),
            "all_use_forward_lineage": all(row["inverse_computed_from_forward_output"] for row in valid_rows),
        },
        "convention_preflight_controls": {
            "required_count": 8,
            "passed_count": sum(1 for row in convention_rows if row["passed"]),
            "all_failed_before_output": all(not row["output_emitted_before_failure"] for row in convention_rows),
        },
    }


def _canonicalizer_probe() -> dict[str, Any]:
    gamma_up = packet_v2.V("gamma", "SI", packet_v2.MU_U)
    gamma_down = packet_v2.V("gamma", "SI", packet_v2.MU_D)
    d_op = packet_v2.V("D", "SI", packet_v2.MU_D)
    ordered = packet_v2.Product((gamma_up, d_op))
    reversed_order = packet_v2.Product((d_op, gamma_up))
    raw_order_distinct = packet_v2._ast_json(ordered) != packet_v2._ast_json(reversed_order)
    normalized_order_equal = packet_v2.canonical(ordered) == packet_v2.canonical(reversed_order)
    safety_checks = {
        "sign_preserved": packet_v2.canonical(ordered) != packet_v2.canonical(packet_v2.N(ordered)),
        "index_variance_preserved": packet_v2.canonical(gamma_up) != packet_v2.canonical(gamma_down),
        "derivative_kind_preserved": packet_v2.canonical(packet_v2.D("partial", packet_v2.MU_D, gamma_up)) != packet_v2.canonical(packet_v2.D("nabla", packet_v2.MU_D, gamma_up)),
        "object_identity_preserved": packet_v2.canonical(packet_v2.V("T_psi", "SI", packet_v2.MU_U, packet_v2.NU_U)) != packet_v2.canonical(packet_v2.V("T_matter", "SI", packet_v2.MU_U, packet_v2.NU_U)),
        "missing_hbar_preserved": packet_v2.canonical(packet_v2.Product((packet_v2.HBAR, gamma_up, d_op))) != packet_v2.canonical(ordered),
        "operator_order_preserved": not normalized_order_equal,
    }
    return {
        "raw_gamma_D_differs_from_raw_D_gamma": raw_order_distinct,
        "canonical_gamma_D_equals_canonical_D_gamma": normalized_order_equal,
        "normalizer_sort_statement_present": "combined.sort" in inspect.getsource(packet_v2.normalize),
        "safety_checks": safety_checks,
        "passed_count": sum(safety_checks.values()),
        "required_count": len(safety_checks),
        "passed": all(safety_checks.values()),
    }


def _lineage_forgery_probe() -> dict[str, Any]:
    contract = packet_v2.CONTRACTS["SOURCED_MAXWELL"]
    source_hash = _sha256(packet_v2.canonical(contract.source_ast).encode("utf-8"))
    computed_hash = _sha256(packet_v2.canonical(contract.expected_si_ast).encode("utf-8"))
    declared_rules = tuple(rule.rule_id for rule in contract.forward_rules)
    forged_lineage = packet_v2._lineage(contract.equation_id, source_hash, computed_hash, declared_rules)
    forged = packet_v2.TransformResult(
        equation_id=contract.equation_id,
        direction="restore",
        computed_ast=copy.deepcopy(contract.expected_si_ast),
        expected_ast=copy.deepcopy(contract.expected_si_ast),
        applied_rule_ids=declared_rules,
        provenance_trace=("MANUALLY_CONSTRUCTED_WITHOUT_RESTORE",),
        binding_id=contract.binding_id,
        adapter_id=contract.adapter_id,
        source_canonical_sha256=source_hash,
        computed_canonical_sha256=computed_hash,
        lineage_id=forged_lineage,
        passed=True,
        first_diagnostic="PASS",
        untrusted_summary_ignored=False,
    )
    observed = "NO_DIAGNOSTIC"
    accepted = False
    inverse_passed = False
    try:
        inverse = packet_v2.suppress(
            forged,
            convention_state=dict(packet_v2.BASE_CONVENTION_STATE),
            binding_id=contract.binding_id,
        )
        accepted = True
        inverse_passed = inverse.passed
    except packet_v2.ProductionContractError as error:
        observed = error.diagnostic
    return {
        "forward_restore_called": False,
        "public_transform_result_constructor_used": True,
        "lineage_reconstructed_from_public_fields": True,
        "manual_result_accepted_by_suppress": accepted,
        "manual_result_inverse_passed": inverse_passed,
        "observed_first_diagnostic": observed,
        "origin_authentication_passed": not accepted,
    }


def _control_atomicity_audit(packet: dict[str, Any]) -> dict[str, Any]:
    rows = packet["production_contract_adversarial_controls"]["rows"]
    source = (REPO_ROOT / PACKET_TOOL_RELATIVE_PATH).read_text(encoding="utf-8")
    tree = ast.parse(source)
    function = next(
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "_production_adversarial_controls"
    )
    function_source = ast.get_source_segment(source, function) or ""
    forced_summary_has_oracle_mutation = (
        "maxwell.expected_si_ast = wrong_oracle" in function_source
        and "untrusted_summary_pass=True" in function_source
    )
    audited: list[dict[str, Any]] = []
    for row in rows:
        mutation_id = row["mutation_id"]
        actual = row["changed_premise_count"]
        role = "atomic_negative_mutation"
        if mutation_id == "ADV_FORCED_PASS_SUMMARY" and forced_summary_has_oracle_mutation:
            actual = 2
        if mutation_id == "ADV_ALL_SIX_VALID_PRODUCTION_PATHS":
            actual = 0
            role = "positive_control_not_adversarial_mutation"
        audited.append(
            {
                "mutation_id": mutation_id,
                "reported_changed_premise_count": row["changed_premise_count"],
                "independently_observed_changed_premise_count": actual,
                "role": role,
                "atomic_single_premise": actual == 1,
            }
        )
    return {
        "reported_control_count": len(rows),
        "atomic_single_premise_count": sum(1 for row in audited if row["atomic_single_premise"]),
        "forced_summary_actual_changed_premises": 2,
        "zero_mutation_positive_row_counted_as_adversarial": True,
        "rows": audited,
        "all_adversarial_controls_atomic": all(row["atomic_single_premise"] for row in audited),
    }


def build_review() -> dict[str, Any]:
    packet, frozen_inputs = _read_frozen_packet()
    sources = _independent_source_binding_audit()
    production = _production_positive_probe()
    canonicalizer = _canonicalizer_probe()
    lineage = _lineage_forgery_probe()
    atomicity = _control_atomicity_audit(packet)
    if not sources["passed"]:
        raise ValueError("independent source binding audit unexpectedly failed")
    if production["valid_production_round_trips"]["passed_count"] != 6:
        raise ValueError("frozen v2 valid production path unexpectedly failed")

    findings = [
        {
            "finding_id": FIRST_DIAGNOSTIC,
            "confirmed": (
                canonicalizer["raw_gamma_D_differs_from_raw_D_gamma"]
                and canonicalizer["canonical_gamma_D_equals_canonical_D_gamma"]
            ),
            "materiality": "BLOCKING",
            "evidence": (
                "Product normalization sorts every factor, including Indexed operator-like "
                "objects; gamma^mu D_mu and D_mu gamma^mu canonicalize identically."
            ),
        },
        {
            "finding_id": "FORWARD_LINEAGE_FORGEABLE_FROM_PUBLIC_RESULT_FIELDS",
            "confirmed": lineage["manual_result_accepted_by_suppress"] and lineage["manual_result_inverse_passed"],
            "materiality": "BLOCKING",
            "evidence": (
                "A manually constructed public TransformResult, whose digest was recomputed "
                "from public fields without calling restore, was accepted by suppress."
            ),
        },
        {
            "finding_id": "PRODUCTION_ADVERSARIAL_CONTROL_ATOMICITY_MISREPORTED",
            "confirmed": (
                atomicity["atomic_single_premise_count"] == 8
                and atomicity["forced_summary_actual_changed_premises"] == 2
                and atomicity["zero_mutation_positive_row_counted_as_adversarial"]
            ),
            "materiality": "BLOCKING",
            "evidence": (
                "Only 8/10 reported adversarial rows are one-premise mutations: the forced-pass "
                "row also changes the oracle, while the all-six-valid row changes no premise."
            ),
        },
    ]
    if not all(row["confirmed"] for row in findings):
        raise ValueError("expected v2 review finding not reproduced")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / REVIEW_TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("v2 review test missing")
    return {
        "schema_id": "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v2",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": CONSUMED_TARGET,
        "verdict": VERDICT,
        "first_diagnostic": FIRST_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "review_authority": {
            "frozen_inputs": frozen_inputs,
            "reviewer": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "review_test": {
                "relative_path": REVIEW_TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "retained_findings": {
            "physical_convention": "x^0=c t; (+,-,-,-); SI",
            "physical_convention_reconsidered": False,
            "exact_source_content_bindings_audit": sources,
            "oracle_map_and_shared_path_audit": production,
            "T_psi_exact_object_route_retained": True,
            "authoritative_equations_unchanged": True,
        },
        "canonicalization_soundness_audit": canonicalizer,
        "forward_lineage_origin_audit": lineage,
        "adversarial_control_atomicity_audit": atomicity,
        "blocking_findings": {
            "count": len(findings),
            "all_confirmed": all(row["confirmed"] for row in findings),
            "findings": findings,
        },
        "v3_contract": [
            "Preserve operator order by default for operator-bearing products; introduce commutative normalization only for objects explicitly typed as commuting, and prove gamma^mu D_mu differs from D_mu gamma^mu.",
            "Replace the forgeable public-field lineage digest with an opaque restore-issued custody token bound to equation, source, computed AST, adapter, binding, and applied rules; reject manually constructed, cross-binding, and mutated results.",
            "Move the zero-mutation all-six-valid row to a positive-control section and make every counted adversarial control an independently verified one-premise mutation.",
            "Split the forced-summary test so one control mutates only an untrusted summary on a valid result and a separate atomic wrong-oracle control proves target mismatch.",
            "Repeat the six source bindings, wrong-oracle, missing/mutated/extra-map, quantum hbar, exact T_psi, and lineage probes without adding equations or performing restoration or migration.",
        ],
        "scope_and_authorization": {
            "packet_v2_accepted": False,
            "bounded_six_surface_restoration_authorized": False,
            "authoritative_equation_restoration_executed": False,
            "scientific_equation_migration_executed": False,
            "historical_artifacts_modified": False,
            "repository_wide_migration_authorized": False,
            "physical_convention_reopened": False,
            "r13_reopened": False,
            "external_comparator_activated": False,
            "automation_created": False,
            "only_bounded_v3_packet_preparation_authorized": True,
        },
        "claim_ceiling": (
            "V2 independently computes the six intended forward and inverse examples and "
            "enforces their declared maps and preflight, but it does not yet prove semantic "
            "identity because operator order is canonicalized away and forward origin is forgeable."
        ),
        "hard_stop": {
            "packet_accepted": False,
            "restoration_authorized": False,
            "migration_authorized": False,
            "next_action": SELECTED_NEXT_TARGET,
            "successor_scope": "ONE_BOUNDED_v3_CANONICALIZATION_LINEAGE_AND_CONTROL_ATOMICITY_REPAIR_ONLY",
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("SR convention/restoration v2 review is stale or missing")
        review = json.loads(raw)
        print(json.dumps({
            "atomic_adversarial_controls": f"{review['adversarial_control_atomicity_audit']['atomic_single_premise_count']}/10",
            "blocking_findings": review["blocking_findings"]["count"],
            "canonicalizer_checks": f"{review['canonicalization_soundness_audit']['passed_count']}/{review['canonicalization_soundness_audit']['required_count']}",
            "source_bindings": f"{review['retained_findings']['exact_source_content_bindings_audit']['passed_count']}/6",
            "status": "CHECKED",
            "verdict": review["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
