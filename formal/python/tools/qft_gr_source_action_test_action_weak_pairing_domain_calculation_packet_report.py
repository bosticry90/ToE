from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.select_next_global_toe_work_target_from_mathematical_obligation_index_report import (
    DEFAULT_OUT as DEFAULT_SELECTION_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_SELECTION_OUTCOME,
    SCHEMA_ID as EXPECTED_SELECTION_SCHEMA_ID,
    SELECTION_ID as EXPECTED_SELECTION_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_"
    "20260616_v0"
)
PACKET_ID = "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_"
    "PREPARED_WITH_BLOCKED_WEAK_PAIRING_DOMAIN_AND_NO_SOURCE_ADMISSIBILITY_"
    "OR_QFT_GR_CLOSURE"
)
CALCULATION_RESULT = (
    "WEAK_PAIRING_DOMAIN_CALCULATION_BLOCKED_BY_MISSING_CANDIDATE_FUNCTIONAL_"
    "CONTRACT"
)
PACKET_CLASSIFICATION = (
    "qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_"
    "records_blocked_weak_pairing_domain_by_missing_candidate_functional_contract"
)
NEXT_TARGET = "review_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result"
NEXT_TARGET_KIND = "qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review"
FIRST_BREAK_ROW_ID = "source_action_test_action_and_weak_pairing_domain"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_"
        "PACKET_20260616_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceActionTestActionWeakPairingDomainCalculationPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _acceptance_outputs() -> dict[str, bool]:
    return {
        "definition_supplied": True,
        "lemma_or_proposition_stated": True,
        "symbolic_derivation_performed": False,
        "well_definedness_proof_attempted": True,
        "counterexample_or_obstruction_recorded": True,
        "calculation_blocked_by_missing_formal_input": True,
    }


def _calculation_progression() -> list[dict[str, Any]]:
    return [
        {
            "stage": "weak_pairing",
            "status": "blocked",
            "decision_field": "well_defined_pairing",
            "decision": "blocked",
            "reason": (
                "The current candidate is not accompanied by a continuous "
                "linear functional T : D -> R, a continuity/domain contract, "
                "or smooth/local-integrability data that would define the "
                "integral pairing."
            ),
        },
        {
            "stage": "action_derivability",
            "status": "NOT_REACHED",
            "decision_field": "source_is_action_derived",
            "decision": "not_reached",
            "reason": "Weak pairing is blocked.",
        },
        {
            "stage": "weak_conservation",
            "status": "NOT_REACHED",
            "decision_field": "weak_conservation_verified",
            "decision": "not_reached",
            "reason": "Source action and weak pairing are not licensed.",
        },
        {
            "stage": "bianchi_compatibility",
            "status": "NOT_REACHED",
            "decision_field": "bianchi_compatible_source",
            "decision": "not_reached",
            "reason": "Weak conservation is not reached.",
        },
        {
            "stage": "semiclassical_source_admissibility",
            "status": "NOT_REACHED",
            "decision_field": "semiclassical_source_admissible",
            "decision": "not_reached",
            "reason": "Bianchi-compatible source admissibility is not reached.",
        },
    ]


def _missing_mathematical_data() -> list[str]:
    return [
        "continuous_linear_functional_T_from_test_space_D_to_R_not_supplied",
        "continuity_topology_or_distribution_order_contract_not_supplied",
        "smooth_or_locally_integrable_tensor_density_representative_not_supplied",
        "source_action_functional_S_m_not_supplied",
        "metric_variation_delta_S_m_delta_g_contract_not_supplied",
        "allowed_test_action_or_allowed_metric_variation_class_not_supplied",
    ]


def build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet(
    *,
    selection_path: Path = DEFAULT_SELECTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selection = _read_json(selection_path)
    outputs = _acceptance_outputs()
    progression = _calculation_progression()
    missing_data = _missing_mathematical_data()
    acceptance_criteria = {
        "consumes_expected_selection": (
            selection.get("schema_id") == EXPECTED_SELECTION_SCHEMA_ID
            and selection.get("selection_id") == EXPECTED_SELECTION_ID
            and selection.get("outcome_id") == EXPECTED_SELECTION_OUTCOME
            and selection.get("selected_next_target") == CONSUMED_TARGET
        ),
        "mathematical_definition_supplied": outputs["definition_supplied"]
        and outputs["lemma_or_proposition_stated"],
        "well_definedness_attempt_records_blocker": (
            outputs["well_definedness_proof_attempted"]
            and outputs["counterexample_or_obstruction_recorded"]
            and outputs["calculation_blocked_by_missing_formal_input"]
            and len(missing_data) >= 4
        ),
        "weak_pairing_decision_is_blocked": progression[0]["stage"] == "weak_pairing"
        and progression[0]["decision"] == "blocked",
        "downstream_rows_not_reached": all(
            row["status"] == "NOT_REACHED" for row in progression[1:]
        ),
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = NEXT_TARGET if prepared else "REMEDIATE_QFT_GR_WEAK_PAIRING_CALCULATION_PACKET"
    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID if prepared else "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "first_break_row_id": FIRST_BREAK_ROW_ID,
        "calculation_result": CALCULATION_RESULT,
        "mathematical_context": {
            "working_spacetime_background": "Let (M, g) be the working spacetime background.",
            "test_space": "D = C_c^infty(M, Sym^2 T*M)",
            "test_object": "h_{mu nu} in C_c^infty(M, Sym^2 T*M)",
        },
        "weak_pairing_definition": {
            "distributional_requirement": "T must define a continuous linear functional T : D -> R.",
            "smooth_or_locally_integrable_template": (
                "<T, h> = integral_M T^{mu nu} h_{mu nu} dVol_g"
            ),
            "well_defined_pairing": "blocked",
        },
        "mathematical_acceptance_outputs": outputs,
        "mathematical_acceptance_output_count": sum(1 for value in outputs.values() if value),
        "proposition_stated": (
            "A QFT-GR source candidate is weakly pairable on D only if it "
            "supplies either a continuous linear functional T : D -> R or "
            "smooth/local-integrability data that defines the integral pairing."
        ),
        "well_definedness_proof_attempt": (
            "The criterion can be stated, but it cannot be discharged for the "
            "current candidate because the candidate packet does not supply "
            "the required functional/domain contract."
        ),
        "missing_mathematical_data": missing_data,
        "missing_mathematical_data_count": len(missing_data),
        "calculation_progression": progression,
        "well_defined_pairing": "blocked",
        "source_is_action_derived": "not_reached",
        "weak_conservation_verified": "not_reached",
        "bianchi_compatible_source": "not_reached",
        "semiclassical_source_admissible": "not_reached",
        "downstream_status_when_weak_pairing_blocked": "NOT_REACHED",
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "acceptance_criteria": acceptance_criteria,
        "validation_policy": {
            "bounded_focused_validation_only": True,
            "full_pytest_required": False,
            "full_governance_suite_required": False,
            "full_aggregate_lean_required": False,
            "full_ci_parity_required": False,
            "full_security_scan_required": False,
        },
        "non_claim_boundary": (
            "This calculation packet states the weak-pairing criterion and "
            "records that the current candidate is blocked by missing "
            "functional/domain data. It does not claim source admissibility, "
            "action derivability, conservation, Bianchi compatibility, "
            "semiclassical coupling, QFT-GR closure, empirical validation, "
            "public submission, or master-action promotion."
        ),
    }


def write_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet(
    *,
    selection_path: Path = DEFAULT_SELECTION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet(
        selection_path=selection_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QFT-GR weak-pairing calculation packet JSON.")
    parser.add_argument("--selection", type=Path, default=DEFAULT_SELECTION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    selection_path = ns.selection if ns.selection.is_absolute() else (REPO_ROOT / ns.selection)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet(
        selection_path=selection_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "prepared": payload["prepared"],
                "calculation_result": payload["calculation_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
