from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import sys
import unicodedata
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as numerical


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail.py"
DESIGN_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_RESULT_REVIEW_20260713_v0.json"
DESIGN_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-PACKET-v0.json"
CANONICAL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json"
CANONICAL_PRIMARY_RELATIVE_PATH = "formal/output/canonical/dirac_maxwell_full_zero_mode_v0/CANONICAL_PRIMARY_N32_DT0P0015625.json"
NUMERICAL_IMPLEMENTATION_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"

PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v0_result"
REPAIR_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_packet_v0"
BLOCKER_CODE = "B-BLOCKED_F_PERP_NORMALIZATION_NOT_BOUNDED"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_20260713_v0"

INPUT_HASHES = {
    DESIGN_REVIEW_RELATIVE_PATH: "84140ac762b660a1f4ab86d9376a50bad256de1bf0f4faa9898195a5eb9fa0f9",
    DESIGN_PACKET_RELATIVE_PATH: "98a635b92d3a2b5479cc41aca80760a965a249fb3ae16c476b3a50aab6e10100",
    CANONICAL_REVIEW_RELATIVE_PATH: "9b518024fa8a13b73d19e01576375484d5acc24e4f5896adaa612b46f500e040",
    CANONICAL_PRIMARY_RELATIVE_PATH: "97b3fe6c4ed0cfee904158fcbf778a74b0501b40580dba33e0f9300ea7b28e7a",
    NUMERICAL_IMPLEMENTATION_RELATIVE_PATH: "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
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
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def load_authority() -> dict[str, dict[str, Any]]:
    sources: dict[str, dict[str, Any]] = {}
    for relative_path, digest in INPUT_HASHES.items():
        path = REPO_ROOT / relative_path
        if sha256_path(path) != digest:
            raise ValueError(f"input hash mismatch: {relative_path}")
        if path.suffix == ".json":
            sources[relative_path] = load_json(path)
    review = sources[DESIGN_REVIEW_RELATIVE_PATH]
    if not (
        review.get("accepted") is True
        and review.get("verdict") == "ACCEPT_SCIENTIFIC_DESIGN"
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("robustness_guardrail_preparation_authorized") is True
        and review.get("authority_rotation", {}).get("pilot_authorized") is False
        and review.get("authority_rotation", {}).get("canonical_robustness_execution_authorized") is False
    ):
        raise ValueError("accepted design review does not authorize this guardrail preparation")
    canonical = sources[CANONICAL_REVIEW_RELATIVE_PATH]
    if not (
        canonical.get("accepted") is True
        and canonical.get("accepted_claim_label") == "E-REPRO"
        and canonical.get("authority_rotation", {}).get("bounded_scientific_result_accepted") is True
    ):
        raise ValueError("accepted canonical E-REPRO result is not bound")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        raise ValueError("Prompt.txt changed")
    return sources


def _phase_audit_row(delta_theta: float) -> dict[str, Any]:
    n = 32
    state = numerical.initial_state("full_mixed", n, numerical.CHARGE)
    phase = complex(math.cos(delta_theta), math.sin(delta_theta))
    # GAMMA0/GAMMA1 preserve the [0,2] and [1,3] reduced sectors.  Applying
    # this phase to [1,3] realizes the accepted relative reduced-sector axis.
    for key in ("psi_plus", "psi_minus"):
        state[key][:, [1, 3]] *= phase
    energies = numerical.energy_components(state, numerical.LENGTH / n, numerical.CHARGE)
    transverse_energy = energies["phi2"] + energies["phi3"]
    total_energy = sum(energies.values())
    return {
        "delta_theta_psi_radians": delta_theta,
        "phase_label": {
            -math.pi / 2: "NEGATIVE_PI_OVER_TWO",
            0.0: "CANONICAL_ZERO",
            math.pi / 2: "POSITIVE_PI_OVER_TWO",
        }[delta_theta],
        "transverse_descendant_energy": transverse_energy,
        "registered_signed_total_energy": total_energy,
        "f_perp_initial": transverse_energy / total_energy,
        "within_declared_fraction_domain": 0.0 <= transverse_energy / total_energy <= 1.0,
    }


def normalization_audit() -> dict[str, Any]:
    canonical = load_json(REPO_ROOT / CANONICAL_PRIMARY_RELATIVE_PATH)
    series = canonical["registered_arrays"]["series"]
    canonical_numerator = float(series["energy_phi2"][0]) + float(series["energy_phi3"][0])
    canonical_denominator = float(series["total_energy"][0])
    rows = [_phase_audit_row(value) for value in (-math.pi / 2, 0.0, math.pi / 2)]
    return {
        "axis_id": "F_PERP_INITIAL",
        "accepted_definition": "(E_phi2(0)+E_phi3(0))/E_total(0)",
        "accepted_declared_domain": "0 <= f_perp_initial <= 1",
        "counterexample_uses_only_admitted_axes": True,
        "fixed_audit_inputs": {
            "grid_size": 32,
            "eta_q": numerical.CHARGE / numerical.MASS,
            "mu_mass_domain": numerical.MASS * numerical.LENGTH,
            "theta_W": 0.3,
            "descendant_initial_fields": "accepted canonical full_mixed fields",
            "varied_axis": "DELTA_THETA_PSI",
            "reduced_sector_phase_applied_to_components": [1, 3],
            "species_phase_application": ["psi_plus", "psi_minus"],
        },
        "canonical_output_anchor": {
            "source_path": CANONICAL_PRIMARY_RELATIVE_PATH,
            "energy_phi2_initial": float(series["energy_phi2"][0]),
            "energy_phi3_initial": float(series["energy_phi3"][0]),
            "registered_signed_total_energy_initial": canonical_denominator,
            "f_perp_initial": canonical_numerator / canonical_denominator,
        },
        "phase_rows": rows,
        "counterexample": next(row for row in rows if row["phase_label"] == "POSITIVE_PI_OVER_TWO"),
        "bounded_fraction_contract_satisfied": all(row["within_declared_fraction_domain"] for row in rows),
        "denominator_positive_definite_established": False,
        "scientific_reason": "The registered c-number Dirac energy is signed and not a positive-definite energy budget. Relative reduced-sector phase changes matter and interaction contributions while the positive descendant numerator is fixed.",
    }


def _base_contract(audit: dict[str, Any]) -> dict[str, Any]:
    return {
        "current_target": TARGET,
        "design_review_bound": True,
        "canonical_result_immutable": True,
        "axis_id": "F_PERP_INITIAL",
        "axis_formula": "(E_phi2(0)+E_phi3(0))/E_total(0)",
        "declared_domain": "0 <= f_perp_initial <= 1",
        "positive_pi_over_two_row_retained": True,
        "observed_counterexample_value": audit["counterexample"]["f_perp_initial"],
        "counterexample_acknowledged": True,
        "axis_silently_redefined": False,
        "exact_matrix_frozen": False,
        "pilot_authorized": False,
        "robustness_execution_authorized": False,
        "repair_candidate_auto_selected": False,
        "blocker_code": BLOCKER_CODE,
    }


def contract_diagnostics(contract: dict[str, Any]) -> list[str]:
    diagnostics: list[str] = []
    if contract.get("current_target") != TARGET:
        diagnostics.append("CURRENT_TARGET_MISMATCH")
    if contract.get("design_review_bound") is not True:
        diagnostics.append("ACCEPTED_DESIGN_NOT_BOUND")
    if contract.get("canonical_result_immutable") is not True:
        diagnostics.append("CANONICAL_RESULT_REOPENED")
    if contract.get("axis_formula") != "(E_phi2(0)+E_phi3(0))/E_total(0)":
        diagnostics.append("ACCEPTED_AXIS_FORMULA_CHANGED")
    if contract.get("declared_domain") != "0 <= f_perp_initial <= 1":
        diagnostics.append("ACCEPTED_AXIS_DOMAIN_CHANGED")
    if contract.get("positive_pi_over_two_row_retained") is not True:
        diagnostics.append("ADMITTED_PHASE_COUNTEREXAMPLE_REMOVED")
    value = contract.get("observed_counterexample_value")
    if not isinstance(value, (int, float)) or not value > 1.0:
        diagnostics.append("COUNTEREXAMPLE_NOT_REPRODUCED")
    if contract.get("counterexample_acknowledged") is not True:
        diagnostics.append("BOUNDEDNESS_VIOLATION_IGNORED")
    if contract.get("axis_silently_redefined") is not False:
        diagnostics.append("UNREVIEWED_AXIS_REDEFINITION")
    if contract.get("exact_matrix_frozen") is not False:
        diagnostics.append("MATRIX_FROZEN_DESPITE_AXIS_CONTRADICTION")
    if contract.get("pilot_authorized") is not False:
        diagnostics.append("PILOT_AUTHORIZED_DESPITE_GUARDRAIL_BLOCKER")
    if contract.get("robustness_execution_authorized") is not False:
        diagnostics.append("EXECUTION_AUTHORIZED_DESPITE_GUARDRAIL_BLOCKER")
    if contract.get("repair_candidate_auto_selected") is not False:
        diagnostics.append("NORMALIZATION_REPAIR_AUTO_SELECTED")
    if contract.get("blocker_code") != BLOCKER_CODE:
        diagnostics.append("BLOCKER_CODE_CHANGED")
    return diagnostics


def mutation_controls(audit: dict[str, Any]) -> list[dict[str, Any]]:
    baseline = _base_contract(audit)
    if contract_diagnostics(baseline):
        raise ValueError("unmutated guardrail blocker contract does not pass")
    mutations: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("M_CURRENT_TARGET", "CURRENT_TARGET_MISMATCH", lambda value: value.__setitem__("current_target", "wrong_target")),
        ("M_DESIGN_UNBOUND", "ACCEPTED_DESIGN_NOT_BOUND", lambda value: value.__setitem__("design_review_bound", False)),
        ("M_CANONICAL_REOPENED", "CANONICAL_RESULT_REOPENED", lambda value: value.__setitem__("canonical_result_immutable", False)),
        ("M_AXIS_FORMULA", "ACCEPTED_AXIS_FORMULA_CHANGED", lambda value: value.__setitem__("axis_formula", "E_perp/E_absolute")),
        ("M_AXIS_DOMAIN", "ACCEPTED_AXIS_DOMAIN_CHANGED", lambda value: value.__setitem__("declared_domain", "unbounded real")),
        ("M_PHASE_ROW_REMOVED", "ADMITTED_PHASE_COUNTEREXAMPLE_REMOVED", lambda value: value.__setitem__("positive_pi_over_two_row_retained", False)),
        ("M_COUNTEREXAMPLE_ERASED", "COUNTEREXAMPLE_NOT_REPRODUCED", lambda value: value.__setitem__("observed_counterexample_value", 1.0)),
        ("M_VIOLATION_IGNORED", "BOUNDEDNESS_VIOLATION_IGNORED", lambda value: value.__setitem__("counterexample_acknowledged", False)),
        ("M_SILENT_REDEFINITION", "UNREVIEWED_AXIS_REDEFINITION", lambda value: value.__setitem__("axis_silently_redefined", True)),
        ("M_MATRIX_FROZEN", "MATRIX_FROZEN_DESPITE_AXIS_CONTRADICTION", lambda value: value.__setitem__("exact_matrix_frozen", True)),
        ("M_PILOT_AUTHORIZED", "PILOT_AUTHORIZED_DESPITE_GUARDRAIL_BLOCKER", lambda value: value.__setitem__("pilot_authorized", True)),
        ("M_EXECUTION_AUTHORIZED", "EXECUTION_AUTHORIZED_DESPITE_GUARDRAIL_BLOCKER", lambda value: value.__setitem__("robustness_execution_authorized", True)),
        ("M_AUTO_REPAIR", "NORMALIZATION_REPAIR_AUTO_SELECTED", lambda value: value.__setitem__("repair_candidate_auto_selected", True)),
        ("M_BLOCKER_CODE", "BLOCKER_CODE_CHANGED", lambda value: value.__setitem__("blocker_code", "ACCEPT")),
    ]
    results: list[dict[str, Any]] = []
    for mutation_id, expected, mutate in mutations:
        fixture = copy.deepcopy(baseline)
        if contract_diagnostics(fixture):
            raise ValueError(f"fresh baseline failed before {mutation_id}")
        mutate(fixture)
        actual = contract_diagnostics(fixture)
        results.append({
            "mutation_id": mutation_id,
            "expected_diagnostic": expected,
            "actual_diagnostics": actual,
            "one_intended_premise_changed": True,
            "no_unrelated_earlier_failure": actual == [expected],
            "passed": actual == [expected],
        })
    return results


def build_packet() -> dict[str, Any]:
    load_authority()
    audit = normalization_audit()
    if audit["bounded_fraction_contract_satisfied"] is not False:
        raise ValueError("the required boundedness counterexample was not reproduced")
    controls = mutation_controls(audit)
    if not all(item["passed"] for item in controls):
        raise ValueError("guardrail blocker mutation suite failed")
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_BLOCKER_PENDING_INDEPENDENT_REVIEW",
        "blocker_code": BLOCKER_CODE,
        "blocker_statement": "The accepted F_PERP_INITIAL definition is not a bounded energy fraction over the admitted DELTA_THETA_PSI domain, so an exact 12-14-row matrix cannot be frozen without an unreviewed scientific-design change.",
        "accepted_design_reopened": False,
        "canonical_result_reopened": False,
        "normalization_audit": audit,
        "guardrail_completion": {
            "exact_axis_values_frozen": False,
            "scientific_parameter_matrix_frozen": False,
            "comparator_eligibility_matrix_frozen": False,
            "observable_thresholds_frozen": False,
            "control_run_roles_frozen": False,
            "pilot_subset_frozen": False,
            "reason": BLOCKER_CODE,
        },
        "repair_route_candidates_for_separate_review": [
            {"candidate_id": "POSITIVE_ABSOLUTE_ENERGY_INVENTORY_DENOMINATOR", "selected": False},
            {"candidate_id": "TRANSVERSE_TO_NONTRANSVERSE_ENERGY_ODDS", "selected": False},
            {"candidate_id": "DIRECT_DESCENDANT_AMPLITUDE_SCALE", "selected": False},
            {"candidate_id": "FIXED_POSITIVE_CANONICAL_ENERGY_BUDGET_NORMALIZATION", "selected": False},
        ],
        "repair_selection_policy": "No candidate is selected by this blocker packet. A versioned scientific-design repair must define, score, and independently review the replacement axis before guardrail work resumes.",
        "mutation_controls": controls,
        "authority_boundary": {
            "independent_blocker_review_authorized": True,
            "axis_normalization_repair_authorized_before_review": False,
            "pilot_authorized": False,
            "canonical_robustness_execution_authorized": False,
            "canonical_result_remains_accepted_E_REPRO": True,
            "pillar_completion_claimed": False,
            "seam_closure_claimed": False,
            "C_k_dynamics_claimed": False,
            "CCFT_validation_claimed": False,
            "master_action_promotion_claimed": False,
        },
        "selected_next_target": REVIEW_TARGET,
        "post_review_blocker_target_if_confirmed": REPAIR_TARGET,
        "input_hashes": INPUT_HASHES,
        "prompt_sha256": PROMPT_SHA256,
    }


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    packet_hash = sha256_bytes(canonical_json_bytes(packet))
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": packet["verdict"],
        "blocker_code": BLOCKER_CODE,
        "blocker_confirmed_by_preparation": True,
        "counterexample_f_perp_initial": packet["normalization_audit"]["counterexample"]["f_perp_initial"],
        "declared_upper_bound": 1.0,
        "matrix_frozen": False,
        "pilot_authorized": False,
        "mutation_controls_passed": sum(item["passed"] for item in packet["mutation_controls"]),
        "mutation_control_count": len(packet["mutation_controls"]),
        "packet_sha256": packet_hash,
        "selected_next_target": REVIEW_TARGET,
        "claim_ceiling": "Guardrail preparation found a bounded scientific-design contradiction; it does not alter the accepted canonical E-REPRO result or authorize robustness calibration or execution.",
    }
    report_hash = sha256_bytes(canonical_json_bytes(report))
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": [{"path": path, "sha256": digest} for path, digest in sorted(INPUT_HASHES.items())],
        "artifacts": [
            {"path": PACKET_RELATIVE_PATH, "sha256": packet_hash},
            {"path": REPORT_RELATIVE_PATH, "sha256": report_hash},
        ],
        "prompt": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "preserved": True},
    }
    return packet, manifest, report


def write_artifacts() -> None:
    packet, manifest, report = build_artifacts()
    for path, payload in ((PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(canonical_json_bytes(payload))


def check_artifacts() -> bool:
    packet, manifest, report = build_artifacts()
    return all(
        path.exists() and path.read_bytes() == canonical_json_bytes(payload)
        for path, payload in ((PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report))
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    if args.write:
        write_artifacts()
    if args.check and not check_artifacts():
        return 1
    if args.stdout:
        print(canonical_json_bytes(build_packet()).decode("utf-8"), end="")
    if not (args.write or args.check or args.stdout):
        parser.error("one of --write, --check, or --stdout is required")
    return 0


if __name__ == "__main__":
    sys.exit(main())
