from __future__ import annotations

import argparse
import ast
import hashlib
import inspect
import itertools
import json
from dataclasses import FrozenInstanceError, replace
from pathlib import Path
from typing import Any

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_v3 as packet_v3,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = packet_v3.REPORT_RELATIVE_PATH
PACKET_TOOL_RELATIVE_PATH = (
    "formal/python/tools/"
    "sr_pillar_coordinate_convention_and_constant_restoration_packet_v3.py"
)
PACKET_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_v3.py"
)
REVIEW_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v3.py"
)
V1_PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v1.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v3.json"
)

CONSUMED_TARGET = (
    "review_sr_pillar_coordinate_convention_and_constant_restoration_packet_v3_result"
)
VERDICT = "BLOCKED_SR_RESTORATION_TOOLING_CONTRACT"
FIRST_DIAGNOSTIC = "ISSUED_PROVENANCE_TRACE_MUTATION_NOT_REVALIDATED"
SELECTED_NEXT_TARGET = (
    "select_next_high_leverage_scientific_obligation_from_full_toe_priority_map"
)

FROZEN_INPUT_HASHES = {
    PACKET_RELATIVE_PATH:
        "27f589084a1608d718c6a77136e40d96363190bcfdf0de09f1a4f0f0f92e1c66",
    PACKET_TOOL_RELATIVE_PATH:
        "f77c3ed95ae3344d696185656f9203ba8b675b6582268884d705acc806243e84",
    PACKET_TEST_RELATIVE_PATH:
        "1d783eb29e73afbb89df342d0cdbf61cbf8bcfabf8431ea8999bb1805d6caeb7",
}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _read_frozen_packet() -> tuple[dict[str, Any], list[dict[str, str]]]:
    bindings: list[dict[str, str]] = []
    for relative_path, expected_hash in FROZEN_INPUT_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"frozen v3 input hash mismatch: {relative_path}")
        bindings.append({"relative_path": relative_path, "sha256": observed})
    packet = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("v3 packet verdict mismatch")
    if packet.get("selected_next_target") != CONSUMED_TARGET:
        raise ValueError("v3 packet target mismatch")
    if packet["hard_stop"].get("automatic_v4_authorized") is not False:
        raise ValueError("v3 packet terminal boundary mismatch")
    return packet, bindings


def _json_pointer(payload: Any, pointer: str) -> Any:
    value = payload
    for part in pointer.lstrip("/").split("/"):
        token = part.replace("~1", "/").replace("~0", "~")
        value = value[int(token)] if isinstance(value, list) else value[token]
    return value


def _independent_source_binding_audit() -> dict[str, Any]:
    packet = json.loads((REPO_ROOT / V1_PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    rows: list[dict[str, Any]] = []
    for binding in packet["source_bindings"]["rows"]:
        raw = (REPO_ROOT / binding["artifact"]).read_bytes()
        artifact_hash_matches = _sha256(raw) == binding["artifact_sha256"]
        if binding["source_kind"] == "json_pointer":
            observed = _json_pointer(json.loads(raw.decode("utf-8")), binding["locator"])
        else:
            text = raw.decode("utf-8")
            observed = binding["exact_source_expression"] if binding["exact_source_expression"] in text else None
        exact_expression_matches = observed == binding["exact_source_expression"]
        exact_content_hash_matches = (
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
        passed = all((artifact_hash_matches, exact_expression_matches, exact_content_hash_matches, corroborating_matches))
        rows.append({
            "equation_id": binding["equation_id"],
            "artifact_hash_matches": artifact_hash_matches,
            "exact_expression_matches": exact_expression_matches,
            "exact_content_hash_matches": exact_content_hash_matches,
            "corroborating_matches": corroborating_matches,
            "claim_class_increased": False,
            "passed": passed,
        })
    return {
        "required_count": 6,
        "passed_count": sum(row["passed"] for row in rows),
        "rows": rows,
        "passed": len(rows) == 6 and all(row["passed"] for row in rows),
    }


def _operator_derivative_scalar_audit() -> dict[str, Any]:
    gamma = packet_v3.V("gamma", "SI", packet_v3.MU_U)
    dop = packet_v3.V("D", "SI", packet_v3.MU_D)
    aop = packet_v3.V("A", "probe", packet_v3.MU_U)
    bop = packet_v3.V("B", "probe", packet_v3.MU_D)
    psi = packet_v3.Symbol("psi", "probe")
    phi = packet_v3.Symbol("phi", "probe")
    chi = packet_v3.Symbol("chi", "probe")

    gamma_d = packet_v3.APP(packet_v3.OP(gamma, dop), psi)
    d_gamma = packet_v3.APP(packet_v3.OP(dop, gamma), psi)
    d_of_gamma_psi = packet_v3.APP(dop, packet_v3.APP(gamma, psi))
    gamma_of_d_psi = packet_v3.APP(gamma, packet_v3.APP(dop, psi))
    ab = packet_v3.APP(packet_v3.OP(aop, bop), psi)
    ba = packet_v3.APP(packet_v3.OP(bop, aop), psi)

    scalar_forms = {
        packet_v3.canonical(packet_v3.P(*permutation))
        for permutation in itertools.permutations((packet_v3.I, packet_v3.HBAR, packet_v3.C))
    }
    derivative_kinds = {
        kind: packet_v3.canonical(packet_v3.D(kind, packet_v3.MU_D, psi))
        for kind in ("partial", "nabla", "spin", "gauge")
    }
    derivative_scope_left = packet_v3.D("nabla", packet_v3.MU_D, packet_v3.P(phi, chi))
    derivative_scope_right = packet_v3.P(phi, packet_v3.D("nabla", packet_v3.MU_D, chi))
    scalar_operator_rejected = False
    try:
        packet_v3.canonical(packet_v3.ScalarProduct((gamma, dop)))
    except ValueError as error:
        scalar_operator_rejected = str(error) == "OPERATOR_IN_SCALAR_PRODUCT"

    checks = {
        "gamma_D_differs_from_D_gamma": packet_v3.canonical(gamma_d) != packet_v3.canonical(d_gamma),
        "gamma_D_differs_from_D_of_gamma_psi": packet_v3.canonical(gamma_d) != packet_v3.canonical(d_of_gamma_psi),
        "gamma_D_differs_from_gamma_of_D_psi": packet_v3.canonical(gamma_d) != packet_v3.canonical(gamma_of_d_psi),
        "generic_AB_differs_from_BA": packet_v3.canonical(ab) != packet_v3.canonical(ba),
        "all_i_hbar_c_permutations_equal": len(scalar_forms) == 1,
        "operator_objects_rejected_from_scalar_product": scalar_operator_rejected,
        "partial_nabla_spin_gauge_all_distinct": len(set(derivative_kinds.values())) == 4,
        "derivative_index_variance_preserved": packet_v3.canonical(packet_v3.D("nabla", packet_v3.MU_D, psi)) != packet_v3.canonical(packet_v3.D("nabla", packet_v3.MU_U, psi)),
        "derivative_operand_preserved": packet_v3.canonical(packet_v3.D("nabla", packet_v3.MU_D, psi)) != packet_v3.canonical(packet_v3.D("nabla", packet_v3.MU_D, phi)),
        "derivative_scope_preserved": packet_v3.canonical(derivative_scope_left) != packet_v3.canonical(derivative_scope_right),
    }
    return {
        "required_count": len(checks),
        "passed_count": sum(checks.values()),
        "checks": checks,
        "passed": all(checks.values()),
    }


def _oracle_and_six_path_audit() -> dict[str, Any]:
    packet_v3._reset_issuance_registry_for_packet_build()
    rows = packet_v3._valid_round_trips()
    all_six = len(rows) == 6 and all(row["semantic_round_trip_passed"] for row in rows)

    maxwell = packet_v3.CONTRACTS["SOURCED_MAXWELL"]
    state = dict(packet_v3.BASE_CONVENTION_STATE)
    baseline = packet_v3.restore(maxwell.equation_id, maxwell.source_ast, convention_state=state, binding_id=maxwell.binding_id)
    original_oracle = maxwell.expected_si_ast
    wrong_oracle = packet_v3.Eq(original_oracle.left, packet_v3.N(original_oracle.right))
    maxwell.expected_si_ast = wrong_oracle
    try:
        wrong = packet_v3.restore(maxwell.equation_id, maxwell.source_ast, convention_state=state, binding_id=maxwell.binding_id)
    finally:
        maxwell.expected_si_ast = original_oracle
    oracle_independent = (
        packet_v3.canonical(wrong.computed_ast) == packet_v3.canonical(baseline.computed_ast)
        and not wrong.passed
        and wrong.first_diagnostic == "EXPECTED_TARGET_MISMATCH"
    )
    return {
        "actual_functions_called": ["restore", "suppress", "canonical"],
        "six_path_required_count": 6,
        "six_path_passed_count": sum(row["semantic_round_trip_passed"] for row in rows),
        "all_inverse_inputs_are_issued_forward_objects": all(row["inverse_computed_from_forward_output"] for row in rows),
        "all_six_passed": all_six,
        "wrong_oracle_did_not_change_computed_ast": packet_v3.canonical(wrong.computed_ast) == packet_v3.canonical(baseline.computed_ast),
        "wrong_oracle_rejected": not wrong.passed and wrong.first_diagnostic == "EXPECTED_TARGET_MISMATCH",
        "oracle_independence_passed": oracle_independent,
    }


def _expect_suppression_diagnostic(
    result: packet_v3.TransformResult,
    *,
    state: dict[str, Any],
    binding_id: str,
) -> str:
    try:
        packet_v3.suppress(result, convention_state=state, binding_id=binding_id)
    except packet_v3.ProductionContractError as error:
        return error.diagnostic
    return "NO_DIAGNOSTIC"


def _lineage_audit() -> dict[str, Any]:
    packet_v3._reset_issuance_registry_for_packet_build()
    contract = packet_v3.CONTRACTS["SOURCED_MAXWELL"]
    state = dict(packet_v3.BASE_CONVENTION_STATE)

    valid = packet_v3.restore(contract.equation_id, contract.source_ast, convention_state=state, binding_id=contract.binding_id)
    exact_inverse = packet_v3.suppress(valid, convention_state=state, binding_id=contract.binding_id)

    manual = packet_v3.TransformResult(
        valid.equation_id, valid.direction, valid.computed_ast, valid.expected_ast,
        valid.applied_rule_ids, valid.provenance_trace, valid.binding_id,
        valid.adapter_id, valid.source_canonical_sha256,
        valid.computed_canonical_sha256, valid.lineage_id, valid.passed,
        valid.first_diagnostic, valid.untrusted_summary_ignored,
        valid._issuance_capability,
    )
    manual_diagnostic = _expect_suppression_diagnostic(manual, state=state, binding_id=contract.binding_id)
    wrong_binding_diagnostic = _expect_suppression_diagnostic(valid, state=state, binding_id="CURRENT_CONSERVATION")
    wrong_state = dict(state)
    wrong_state["partial_0"] = "partial_t"
    wrong_convention_diagnostic = _expect_suppression_diagnostic(valid, state=wrong_state, binding_id=contract.binding_id)

    wrong_ast = packet_v3.Eq(valid.computed_ast.left, packet_v3.N(valid.computed_ast.right))
    replaced_ast = replace(valid, computed_ast=wrong_ast)
    replaced_ast_diagnostic = _expect_suppression_diagnostic(replaced_ast, state=state, binding_id=contract.binding_id)
    replaced_trace = replace(valid, provenance_trace=valid.provenance_trace + ("FORGED_COPY_TRACE",))
    replaced_trace_diagnostic = _expect_suppression_diagnostic(replaced_trace, state=state, binding_id=contract.binding_id)

    normal_mutation_rejected = False
    try:
        valid.provenance_trace = valid.provenance_trace + ("NORMAL_MUTATION",)  # type: ignore[misc]
    except FrozenInstanceError:
        normal_mutation_rejected = True

    exact_object_for_trace_probe = packet_v3.restore(
        contract.equation_id,
        contract.source_ast,
        convention_state=state,
        binding_id=contract.binding_id,
    )
    original_trace = exact_object_for_trace_probe.provenance_trace
    object.__setattr__(
        exact_object_for_trace_probe,
        "provenance_trace",
        original_trace + ("FORGED_EXACT_OBJECT_TRACE",),
    )
    reflective_trace_diagnostic = _expect_suppression_diagnostic(
        exact_object_for_trace_probe,
        state=state,
        binding_id=contract.binding_id,
    )
    object.__setattr__(exact_object_for_trace_probe, "provenance_trace", original_trace)

    exact_object_for_ast_probe = packet_v3.restore(
        contract.equation_id,
        contract.source_ast,
        convention_state=state,
        binding_id=contract.binding_id,
    )
    original_ast = exact_object_for_ast_probe.computed_ast
    object.__setattr__(exact_object_for_ast_probe, "computed_ast", wrong_ast)
    reflective_ast_diagnostic = _expect_suppression_diagnostic(
        exact_object_for_ast_probe,
        state=state,
        binding_id=contract.binding_id,
    )
    object.__setattr__(exact_object_for_ast_probe, "computed_ast", original_ast)

    registry_source = inspect.getsource(packet_v3._register_forward_result)
    return {
        "result_dataclass_frozen": packet_v3.TransformResult.__dataclass_params__.frozen,
        "normal_public_assignment_rejected": normal_mutation_rejected,
        "valid_exact_issued_object_suppressed": exact_inverse.passed,
        "manual_visible_field_and_capability_copy_diagnostic": manual_diagnostic,
        "wrong_binding_diagnostic": wrong_binding_diagnostic,
        "wrong_convention_diagnostic": wrong_convention_diagnostic,
        "replaced_ast_copy_diagnostic": replaced_ast_diagnostic,
        "replaced_trace_copy_diagnostic": replaced_trace_diagnostic,
        "reflectively_modified_exact_object_ast_diagnostic": reflective_ast_diagnostic,
        "reflectively_modified_exact_object_trace_diagnostic": reflective_trace_diagnostic,
        "reflectively_modified_exact_object_trace_was_accepted": reflective_trace_diagnostic == "NO_DIAGNOSTIC",
        "issuance_registry_snapshots_provenance_trace": "provenance_trace" in registry_source,
        "bounded_conclusion": (
            "The frozen dataclass blocks ordinary assignment and the issuance registry rejects "
            "copies, binding/convention changes, and AST changes. The registry does not snapshot "
            "the provenance trace, so an altered trace on the exact issued object is accepted."
        ),
    }


def _control_path_and_atomicity_audit(packet: dict[str, Any]) -> dict[str, Any]:
    packet_v3._reset_issuance_registry_for_packet_build()
    positive = packet_v3._positive_controls()
    negative = packet_v3._production_adversarial_controls()
    convention = packet_v3._production_convention_controls()

    positive_path_rows = [
        {"control_id": "POS_UNCHANGED_SIX_PRODUCTION_PATHS", "uses_restore": True, "uses_suppress": True, "full_production_path": True},
        {"control_id": "POS_SAFE_SCALAR_CONSTANT_REORDERING", "uses_restore": False, "uses_suppress": False, "full_production_path": False},
        {"control_id": "POS_OPERATOR_ORDER_AND_SCOPE_REMAIN_DISTINCT", "uses_restore": False, "uses_suppress": False, "full_production_path": False},
    ]

    source = (REPO_ROOT / PACKET_TOOL_RELATIVE_PATH).read_text(encoding="utf-8")
    tree = ast.parse(source)
    function = next(
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "_production_adversarial_controls"
    )
    function_source = ast.get_source_segment(source, function) or ""
    map_control_changes_target_and_meaning = (
        "RewriteRule(original_rule.rule_id, original_rule.source, V(\"J\", \"SI\", NU_U), \"intentionally wrong J map\")"
        in function_source
    )
    atomic_rows: list[dict[str, Any]] = []
    for row in negative:
        actual = row["changed_premise_count"]
        changed_fields = ["registered_single_premise"]
        if row["mutation_id"] == "ADV_OBJECT_MAP_MUTATED" and map_control_changes_target_and_meaning:
            actual = 2
            changed_fields = ["RewriteRule.target", "RewriteRule.meaning"]
        atomic_rows.append({
            "mutation_id": row["mutation_id"],
            "reported_changed_premise_count": row["changed_premise_count"],
            "independently_observed_changed_field_count": actual,
            "changed_fields": changed_fields,
            "atomic_single_change": actual == 1,
            "exact_diagnostic_passed": row["passed"],
        })

    positive_full_count = sum(row["full_production_path"] for row in positive_path_rows)
    atomic_count = sum(row["atomic_single_change"] for row in atomic_rows)
    return {
        "positive_controls": {
            "reported_count": len(positive),
            "passed_count": sum(row["passed"] for row in positive),
            "full_production_path_count": positive_full_count,
            "rows": positive_path_rows,
            "all_use_full_production_path": positive_full_count == len(positive),
        },
        "atomic_negative_controls": {
            "reported_count": len(negative),
            "exact_diagnostic_passed_count": sum(row["passed"] for row in negative),
            "independently_atomic_count": atomic_count,
            "rows": atomic_rows,
            "all_single_change": atomic_count == len(negative),
        },
        "convention_controls": {
            "reported_count": len(convention),
            "passed_count": sum(row["passed"] for row in convention),
            "all_failed_before_output": all(not row["output_emitted_before_failure"] for row in convention),
        },
        "positive_control_source": inspect.getsource(packet_v3._positive_controls),
    }


def build_review() -> dict[str, Any]:
    packet, frozen_inputs = _read_frozen_packet()
    sources = _independent_source_binding_audit()
    semantics = _operator_derivative_scalar_audit()
    paths = _oracle_and_six_path_audit()
    lineage = _lineage_audit()
    controls = _control_path_and_atomicity_audit(packet)
    if not sources["passed"] or not semantics["passed"]:
        raise ValueError("retained v3 physical/semantic audit unexpectedly failed")
    if not paths["all_six_passed"] or not paths["oracle_independence_passed"]:
        raise ValueError("retained v3 production-path audit unexpectedly failed")

    findings = [
        {
            "finding_id": FIRST_DIAGNOSTIC,
            "confirmed": (
                lineage["reflectively_modified_exact_object_trace_was_accepted"]
                and not lineage["issuance_registry_snapshots_provenance_trace"]
            ),
            "materiality": "FOUNDATIONAL_BLOCKING",
            "evidence": lineage["bounded_conclusion"],
        },
        {
            "finding_id": "TWO_OF_THREE_POSITIVE_CONTROLS_BYPASS_FULL_PRODUCTION_PATH",
            "confirmed": controls["positive_controls"]["full_production_path_count"] == 1,
            "materiality": "BLOCKING",
            "evidence": (
                "Only POS_UNCHANGED_SIX_PRODUCTION_PATHS invokes restore and suppress; the "
                "scalar and operator positives call canonical directly and therefore do not "
                "exercise binding preflight, oracle comparison, issuance, or suppression."
            ),
        },
        {
            "finding_id": "OBJECT_MAP_NEGATIVE_CONTROL_CHANGES_TARGET_AND_MEANING_FIELDS",
            "confirmed": controls["atomic_negative_controls"]["independently_atomic_count"] == 13,
            "materiality": "BLOCKING",
            "evidence": (
                "ADV_OBJECT_MAP_MUTATED replaces both RewriteRule.target and RewriteRule.meaning "
                "while reporting one changed premise; only 13/14 rows are one-field mutations."
            ),
        },
    ]
    if not all(row["confirmed"] for row in findings):
        raise ValueError("expected terminal v3 review finding not reproduced")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / REVIEW_TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("v3 review test missing")
    return {
        "schema_id": "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v3",
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
        "retained_results": {
            "physical_convention": "x^0=c t; (+,-,-,-); SI",
            "physical_convention_reconsidered": False,
            "electromagnetic_quantum_stress_and_derivative_conventions_retained": True,
            "exact_source_content_bindings_audit": sources,
            "operator_derivative_and_scalar_audit": semantics,
            "oracle_and_six_path_audit": paths,
            "exact_T_psi_identity_retained": True,
            "authoritative_equations_unchanged": True,
        },
        "issued_lineage_audit": lineage,
        "control_path_and_atomicity_audit": controls,
        "blocking_findings": {
            "count": len(findings),
            "all_confirmed": all(row["confirmed"] for row in findings),
            "findings": findings,
        },
        "terminal_lane_closeout": {
            "lane": "SR_AUTOMATED_CONSTANT_RESTORATION_TOOLING",
            "status": "CLOSED",
            "classification": VERDICT,
            "physical_convention_policy_retained": True,
            "automated_restoration_deferred": True,
            "v4_prepared": False,
            "v4_automatically_authorized": False,
            "fresh_full_project_priority_decision_required_for_v4": True,
            "authority_returned_to_full_project_priority_map": True,
        },
        "scope_and_authorization": {
            "packet_v3_accepted": False,
            "bounded_six_surface_restoration_authorized": False,
            "authoritative_equation_restoration_executed": False,
            "scientific_equation_migration_executed": False,
            "historical_artifacts_modified": False,
            "repository_wide_migration_authorized": False,
            "physical_convention_reopened": False,
            "automatic_v4_authorized": False,
            "r13_reopened": False,
            "external_comparator_activated": False,
            "automation_created": False,
            "full_project_priority_selection_authorized": True,
        },
        "claim_ceiling": (
            "The selected SR-facing convention and the independently reproduced operator, "
            "derivative, scalar, source-binding, oracle, and six intended round-trip results "
            "are retained. V3 is not accepted because its issued provenance trace can be "
            "modified without rejection and its control-path/atomicity contract is incomplete."
        ),
        "hard_stop": {
            "v3_is_final_automatic_attempt": True,
            "lane_closed": True,
            "restoration_authorized": False,
            "migration_authorized": False,
            "automatic_successor_packet_authorized": False,
            "next_action": SELECTED_NEXT_TARGET,
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
            raise SystemExit("SR convention/restoration v3 review is stale or missing")
        review = json.loads(raw)
        print(json.dumps({
            "atomic_negative_controls": f"{review['control_path_and_atomicity_audit']['atomic_negative_controls']['independently_atomic_count']}/14",
            "blocking_findings": review["blocking_findings"]["count"],
            "operator_derivative_scalar": f"{review['retained_results']['operator_derivative_and_scalar_audit']['passed_count']}/{review['retained_results']['operator_derivative_and_scalar_audit']['required_count']}",
            "positive_full_production_paths": f"{review['control_path_and_atomicity_audit']['positive_controls']['full_production_path_count']}/3",
            "source_bindings": f"{review['retained_results']['exact_source_content_bindings_audit']['passed_count']}/6",
            "status": "CHECKED",
            "verdict": review["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
