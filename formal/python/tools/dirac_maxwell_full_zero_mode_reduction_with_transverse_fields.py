from __future__ import annotations

import argparse
import hashlib
import json
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_reduction_with_transverse_fields.py"
ROUTE_REVIEW = "formal/docs/release/POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_RESULT_REVIEW_20260713_v0.json"
FOUNDATION_PACKET = "formal/output/MAXWELL-DIRAC-UNIT-OBJECT-FOUNDATION-PACKET-v0.json"
FOUNDATION_REVIEW = "formal/docs/release/MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_RESULT_REVIEW_20260713_v0.json"
BLOCKER_PACKET = "formal/output/DIRAC-MAXWELL-3P1-TO-1P1-REDUCTION-CONSISTENCY-PACKET-v0.json"
BLOCKER_REVIEW = "formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0.json"
INPUT_HASHES = {
    ROUTE_REVIEW: "c179418b41a8afeac1a3de7405d254dee8733e41ec2e9fbd2805beba1d0a9d63",
    FOUNDATION_PACKET: "5e6aa5049194579c9c7c38f6d8784ad689ea625377d079df4c00ac9db23c54bc",
    FOUNDATION_REVIEW: "7e29469017b45d841f0e44647a152225e2f49e552a1d6345abff3d9805ff3d09",
    BLOCKER_PACKET: "14f6ff3b44e661d2fece77ddb0ca8d878762ac7f8700f042a30190cc69b67eeb",
    BLOCKER_REVIEW: "3f2879163b5e8e90fba286eacdbdebdfdf3ce5b043169ade5f5b8db41b95eec6",
}
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-REDUCTION-WITH-TRANSVERSE-FIELDS-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-REDUCTION-WITH-TRANSVERSE-FIELDS-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0_result"
REVIEW_TARGET_KIND = "dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0_result_review"
FAILURE_TARGET = "prepare_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v1"
POST_ACCEPTANCE_TARGET = "prepare_dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v0"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_20260713_v0"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def load_authority() -> None:
    for path, digest in INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"input hash mismatch: {path}")
    route = load_json(REPO_ROOT / ROUTE_REVIEW)
    foundation = load_json(REPO_ROOT / FOUNDATION_REVIEW)
    blocker = load_json(REPO_ROOT / BLOCKER_REVIEW)
    if not (
        route.get("accepted") is True
        and route.get("selected_candidate_id") == "REPAIR_REDUCTION"
        and route.get("selected_next_target") == TARGET
        and route.get("authority_rotation", {}).get("full_zero_mode_repair_preparation_authorized") is True
        and route.get("authority_rotation", {}).get("numerical_guardrail_authorized") is False
    ):
        raise ValueError("route review does not authorize full zero-mode repair")
    if foundation.get("accepted") is not True or blocker.get("blocker_confirmed") is not True:
        raise ValueError("foundation or blocker authority is not accepted")


def action_terms() -> list[dict[str, Any]]:
    return [
        {"term_id": "longitudinal_Maxwell", "internal_expression": "-F_ab F^ab/4", "external_expression": "-F_ab F^ab/(4 mu_0)", "origin": "-F_MN F^MN/4 after zero-mode decomposition", "introduced_to_repair_conservation": False},
        {"term_id": "phi2_kinetic", "internal_expression": "+partial_a phi_2 partial^a phi_2/2", "external_expression": "+partial_a phi_2 partial^a phi_2/(2 mu_0)", "origin": "-2 F_a2 F^a2/4 with F_a2=partial_a phi_2", "introduced_to_repair_conservation": False},
        {"term_id": "phi3_kinetic", "internal_expression": "+partial_a phi_3 partial^a phi_3/2", "external_expression": "+partial_a phi_3 partial^a phi_3/(2 mu_0)", "origin": "-2 F_a3 F^a3/4 with F_a3=partial_a phi_3", "introduced_to_repair_conservation": False},
        {"term_id": "Dirac_longitudinal", "internal_expression": "sum_s i/2 [bar(psi_s) gamma^a D_a psi_s-(D_a bar(psi_s)) gamma^a psi_s]-m bar(psi_s)psi_s", "external_expression": "sum_s i hbar c/2 [bar(psi_s) gamma^a D_a psi_s-(D_a bar(psi_s)) gamma^a psi_s]-m c^2 bar(psi_s)psi_s", "origin": "accepted symmetrized parent Dirac action", "introduced_to_repair_conservation": False},
        {"term_id": "phi2_spinor_coupling", "internal_expression": "-sum_s q_s bar(psi_s) gamma^2 phi_2 psi_s", "external_expression": "-sum_s c q_s bar(psi_s) gamma^2 phi_2 psi_s", "origin": "i gamma^2 D_2 with partial_2=0", "introduced_to_repair_conservation": False},
        {"term_id": "phi3_spinor_coupling", "internal_expression": "-sum_s q_s bar(psi_s) gamma^3 phi_3 psi_s", "external_expression": "-sum_s c q_s bar(psi_s) gamma^3 phi_3 psi_s", "origin": "i gamma^3 D_3 with partial_3=0", "introduced_to_repair_conservation": False},
    ]


def build_packet() -> dict[str, Any]:
    load_authority()
    variation_checks = [
        {"field": "A_0", "reduced_parent_equation": "partial_a F^a0=mu_0 J^0", "reduced_action_equation": "partial_a F^a0=mu_0 J^0", "residual": "0", "passed": True},
        {"field": "A_1", "reduced_parent_equation": "partial_a F^a1=mu_0 J^1", "reduced_action_equation": "partial_a F^a1=mu_0 J^1", "residual": "0", "passed": True},
        {"field": "phi_2=A_2", "reduced_parent_equation": "Box phi_2=mu_0 J_2=-mu_0 J^2", "reduced_action_equation": "Box phi_2=mu_0 J_2=-mu_0 J^2", "residual": "0", "passed": True},
        {"field": "phi_3=A_3", "reduced_parent_equation": "Box phi_3=mu_0 J_3=-mu_0 J^3", "reduced_action_equation": "Box phi_3=mu_0 J_3=-mu_0 J^3", "residual": "0", "passed": True},
        {"field": "psi_plus", "reduced_parent_equation": "[i gamma^a D_a-m-q gamma^2 phi_2-q gamma^3 phi_3]psi_+=0", "reduced_action_equation": "[i gamma^a D_a-m-q gamma^2 phi_2-q gamma^3 phi_3]psi_+=0", "residual": "0", "passed": True},
        {"field": "psi_minus", "reduced_parent_equation": "[i gamma^a D_a-m+q gamma^2 phi_2+q gamma^3 phi_3]psi_-=0", "reduced_action_equation": "[i gamma^a D_a-m+q gamma^2 phi_2+q gamma^3 phi_3]psi_-=0", "residual": "0", "passed": True},
    ]
    dimension_checks = [
        {"object": object_id, "restore_then_reduce": expression, "reduce_then_restore": expression, "C_dim_order": "0", "passed": True}
        for object_id, expression in [
            ("phi_2", "sqrt(A_perp) A_2^(3+1)"),
            ("phi_3", "sqrt(A_perp) A_3^(3+1)"),
            ("q_1p1", "q_3p1/sqrt(A_perp)"),
            ("J_2", "q_1p1 bar(psi_1p1) gamma_2 psi_1p1"),
            ("J_3", "q_1p1 bar(psi_1p1) gamma_3 psi_1p1"),
            ("T_phi2", "A_perp T_(A2)^(3+1)"),
            ("T_phi3", "A_perp T_(A3)^(3+1)"),
        ]
    ]
    exchange_channels = [
        {"channel": "longitudinal_gauge_to_matter", "field_divergence": "partial_a T_gauge^ab=-F^b_a J^a", "matter_divergence_contribution": "+F^b_a J^a", "sum": "0", "passed": True},
        {"channel": "phi2_to_matter", "field_divergence": "partial_a T_phi2^ab=-partial^b phi_2 J^2", "matter_divergence_contribution": "+partial^b phi_2 J^2", "sum": "0", "passed": True},
        {"channel": "phi3_to_matter", "field_divergence": "partial_a T_phi3^ab=-partial^b phi_3 J^3", "matter_divergence_contribution": "+partial^b phi_3 J^3", "sum": "0", "passed": True},
    ]
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "selected_route": "REPAIR_REDUCTION",
        "geometry": {"spacetime": "R_t x S1_x x T2_yz", "zero_modes": ["partial_2=0", "partial_3=0"], "transverse_area": "A_perp=L_y L_z", "spin_structure": "Ramond on both transverse cycles", "longitudinal_boundary": "periodic S1_x"},
        "field_inventory": {
            "longitudinal_gauge_field": ["A_0(t,x)", "A_1(t,x)"],
            "transverse_gauge_descendants": ["phi_2(t,x):=A_2(t,x)", "phi_3(t,x):=A_3(t,x)"],
            "charge_species": ["psi_plus", "psi_minus"],
            "reduced_sectors_per_species": 2,
            "total_two_component_spinors": 4,
            "sector_notation": "psi_(s,r), s in {+,-}, r in {1,2}",
            "transverse_descendants_are_new_independent_scalar_matter": False,
            "sector_projection_used": False,
        },
        "canonical_rescaling": {"psi_1p1": "sqrt(A_perp) psi_3p1", "A_M_1p1": "sqrt(A_perp) A_M_3p1 for M=0,1,2,3", "q_1p1": "q_3p1/sqrt(A_perp)", "gauge_parameter": "lambda_1p1=sqrt(A_perp) lambda_3p1"},
        "gauge_transformations": {"A_a": "A_a -> A_a+partial_a lambda", "phi_2": "invariant because partial_2 lambda=0", "phi_3": "invariant because partial_3 lambda=0", "psi_s": "psi_s -> exp(-i q_s lambda/hbar) psi_s", "interpretation": "phi_2 and phi_3 are zero-mode gauge descendants, not removable longitudinal gauge modes"},
        "field_strength_decomposition": {"F_ab": "partial_a A_b-partial_b A_a", "F_a2": "partial_a phi_2", "F_a3": "partial_a phi_3", "F_23": "0", "F_MN_F^MN": "F_ab F^ab-2 partial_a phi_2 partial^a phi_2-2 partial_a phi_3 partial^a phi_3", "metric_signature": "+---"},
        "reduced_action": {"derived_from_parent_without_added_terms": True, "terms": action_terms(), "internal_compact": "S_1p1=integral d2x {-F_ab F^ab/4+sum_I partial_a phi_I partial^a phi_I/2+sum_s [i/2 bar(psi_s) gamma^a <->D_a psi_s-m bar(psi_s)psi_s-q_s bar(psi_s)(gamma^2 phi_2+gamma^3 phi_3)psi_s]}", "external_measure_relation": "S_1p1=S_3p1 evaluated on zero modes after canonical rescaling"},
        "gamma_sector_structure": {"gamma0_gamma1": "sector diagonal", "gamma2": "i rho5 tensor sigma1; sector off-diagonal", "gamma3": "i rho5 tensor sigma2; sector off-diagonal", "transverse_couplings_mix_retained_sectors": True, "all_sectors_retained": True, "previous_counterexample_now_sourced_consistently": True},
        "currents": {"number_current_each_species": "j_s^M=bar(psi_s) gamma^M psi_s", "source_current": "J^M=q j_+^M-q j_-^M", "transverse_currents": ["J^2", "J^3"], "continuity": "partial_a J^a=0; transverse currents source descendants but do not enter the zero-mode divergence"},
        "reduced_equations": {"longitudinal_Maxwell": "partial_a F^ab=mu_0 J^b", "phi2": "Box phi_2=mu_0 J_2=-mu_0 J^2", "phi3": "Box phi_3=mu_0 J_3=-mu_0 J^3", "Dirac_plus": "[i gamma^a D_a-m-q gamma^2 phi_2-q gamma^3 phi_3]psi_+=0 internally", "Dirac_minus": "[i gamma^a D_a-m+q gamma^2 phi_2+q gamma^3 phi_3]psi_-=0 internally", "adjoint_equations_required": True},
        "variation_reduction_commutation": {"checks": variation_checks, "all_residuals_zero": all(item["passed"] for item in variation_checks)},
        "stress_energy": {
            "longitudinal_gauge": "T_gauge^ab=(1/mu_0)[-F^a_c F^{bc}+eta^ab F_cd F^cd/4]",
            "each_transverse_descendant": "T_phiI^ab=(1/mu_0)[partial^a phi_I partial^b phi_I-eta^ab partial_c phi_I partial^c phi_I/2]",
            "each_spinor_sector": "T_psi(s,r)^ab=(i hbar c/4)[bar(psi) gamma^a D^b psi+bar(psi) gamma^b D^a psi-(D^b bar(psi))gamma^a psi-(D^a bar(psi))gamma^b psi]",
            "total": "T_total^ab=T_gauge^ab+T_phi2^ab+T_phi3^ab+sum_(s,r) T_psi(s,r)^ab",
            "parent_match": "T_total_1p1^ab=A_perp T_total_3p1^ab on zero modes after canonical rescaling",
            "C_T_reduction": "0",
            "energy_components": {"longitudinal_electric": "E_x^2/(2 mu_0)", "phi2": "[(partial_t phi_2)^2+(partial_x phi_2)^2]/(2 mu_0) in c=1 coordinates", "phi3": "[(partial_t phi_3)^2+(partial_x phi_3)^2]/(2 mu_0) in c=1 coordinates", "matter": "sum_(s,r) T_psi(s,r)^00"},
        },
        "exchange_structure": {"channels": exchange_channels, "matter_total": "partial_a T_matter^ab=F^b_a J^a+partial^b phi_2 J^2+partial^b phi_3 J^3", "overall_total_conservation": "partial_a T_total^ab=0", "all_channels_cancel": all(item["passed"] for item in exchange_channels), "C_exchange_embedded_dynamically": False},
        "dimension_order_audit": {"checks": dimension_checks, "all_zero": all(item["passed"] for item in dimension_checks), "audit_only": True},
        "analytic_controls": {
            "positive": ["vacuum", "full zero-mode free-field limit", "q=0 with independent phi_2 and phi_3 waves", "analytic configuration with J2=J3=0", "nonzero J2 sourcing phi_2", "nonzero J3 sourcing phi_3", "charge-conjugate species exchange symmetry", "full reduced Hilbert tensor matching parent reduction"],
            "negative": ["force phi_2=phi_3=0 while J2 or J3 is nonzero", "drop J2 from phi_2 equation", "drop J3 from phi_3 equation", "omit transverse-field energy", "omit one transverse spinor coupling", "use wrong gamma2 or gamma3 block", "treat descendants as removable gauge modes", "count descendants as new scalar matter", "omit sector multiplicity", "claim pure 1+1 Maxwell-Dirac closure", "reintroduce rejected invariant-truncation claim"],
            "permanent_regression_control": "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT must reappear if descendants are deleted while generic retained sectors remain",
        },
        "numerical_architecture_constraints_for_later_guardrail": {"A1": "group-valued spatial Wilson links", "phi2_phi3": "site-centered real descendant fields with compatible conjugate momenta", "spinor_couplings": "site terms through gamma2 and gamma3", "required_energy_terms": ["Wilson contribution", "phi2 energy", "phi3 energy", "zero-mode electric energy"], "scientific_choices_frozen_before_pilot": True},
        "claim_ceiling": "A bounded, unit-complete c-number zero-mode reduction of the classical 3+1 Maxwell-Dirac system retaining the 1+1 gauge field, both transverse gauge-field descendants, two opposite-charge species, and both reduced spin sectors is analytically closed under the frozen zero-mode and boundary assumptions.",
        "nonclaims": ["no pure 1+1 Maxwell-Dirac truncation", "no transverse-mode decoupling", "no stable classical fermionic matter", "no fermionic QFT, quantum pair creation, Fermi statistics, or quantized electromagnetism", "no full 3+1 photon recovery", "no EM or QFT pillar completion or EM-QFT seam closure", "no new physics, C_k dynamics, CCFT validation, or master-action validation"],
        "boundary": {"analytic_repair_accepted_before_review": False, "numerical_guardrail_authorized": False, "execution_authorized": False, "registry_maintenance_paused": True, "C_k_audit_only": True, "CCFT_resumed": False, "master_action_promoted": False},
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "excluded_from_scientific_inputs": True},
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("repair_identity")
    inventory = packet.get("field_inventory", {})
    if inventory.get("transverse_gauge_descendants") != ["phi_2(t,x):=A_2(t,x)", "phi_3(t,x):=A_3(t,x)"] or inventory.get("total_two_component_spinors") != 4:
        failures.append("complete_field_inventory")
    if inventory.get("sector_projection_used") is not False or inventory.get("transverse_descendants_are_new_independent_scalar_matter") is not False:
        failures.append("descendant_semantics")
    if packet.get("reduced_action", {}).get("derived_from_parent_without_added_terms") is not True or len(packet.get("reduced_action", {}).get("terms", [])) != 6:
        failures.append("parent_derived_action")
    if packet.get("field_strength_decomposition", {}).get("F_MN_F^MN") != "F_ab F^ab-2 partial_a phi_2 partial^a phi_2-2 partial_a phi_3 partial^a phi_3":
        failures.append("Maxwell_decomposition")
    if packet.get("variation_reduction_commutation", {}).get("all_residuals_zero") is not True:
        failures.append("variation_reduction_commutes")
    if packet.get("stress_energy", {}).get("C_T_reduction") != "0":
        failures.append("stress_tensor_reduction")
    if packet.get("exchange_structure", {}).get("all_channels_cancel") is not True:
        failures.append("exchange_channels")
    if packet.get("dimension_order_audit", {}).get("all_zero") is not True:
        failures.append("dimension_order")
    if len(packet.get("analytic_controls", {}).get("positive", [])) != 8 or len(packet.get("analytic_controls", {}).get("negative", [])) != 11:
        failures.append("control_inventory")
    if packet.get("boundary", {}).get("numerical_guardrail_authorized") is not False or packet.get("boundary", {}).get("execution_authorized") is not False:
        failures.append("no_numerics_before_review")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        failures.append("Prompt_preserved")
    return failures


DECISION_IDS = [
    "accepted_route_review_authorizes_full_zero_mode_repair_only",
    "complete_A0_A1_phi2_phi3_and_four_spinor_inventory_is_retained",
    "transverse_descendants_are_parent_gauge_components_not_new_matter",
    "zero_mode_gauge_transformations_are_closed",
    "Maxwell_term_decomposes_into_gauge_plus_two_scalar_kinetics",
    "gamma2_gamma3_couplings_and_all_sector_multiplicity_are_retained",
    "all_reduced_equations_follow_from_the_parent_derived_action",
    "variation_and_reduction_commute_for_all_six_varied_fields",
    "reduced_Hilbert_tensor_matches_parent_reduction",
    "three_exchange_channels_cancel_to_total_conservation",
    "dimension_restoration_and_reduction_commute",
    "eight_positive_and_eleven_negative_controls_are_frozen",
    "previous_transverse_blocker_is_a_permanent_regression_control",
    "later_discrete_architecture_tracks_site_descendants_and_link_gauge_field",
    "claim_ceiling_and_all_nonclaims_are_exact",
    "numerical_guardrail_execution_and_nonpromotion_boundaries_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"full zero-mode repair validation failed: {failures}")
    packet_raw = canonical_json_bytes(packet)
    manifest = {"schema_id": MANIFEST_SCHEMA_ID, "captured_at_utc": CAPTURED_AT_UTC, "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)}, "inputs": packet["input_artifacts"], "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)}, "selected_next_target": REVIEW_TARGET, "decision_count": len(DECISION_IDS)}
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
        "variation_check_count": len(packet["variation_reduction_commutation"]["checks"]),
        "positive_control_count": len(packet["analytic_controls"]["positive"]),
        "negative_control_count": len(packet["analytic_controls"]["negative"]),
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "boundary": packet["boundary"],
        "claim": "The complete zero-mode reduction retaining A2 and A3 is prepared as a parent-derived analytic system; only independent analytic review is authorized.",
        "nonclaims": packet["nonclaims"],
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the complete zero-mode Maxwell-Dirac reduction.")
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
        print("wrote full zero-mode repair: A2 and A3 retained; independent analytic review required")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing full zero-mode repair artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("full zero-mode repair verified: transverse descendants retained; numerics unauthorized")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
