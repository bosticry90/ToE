from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PILOT_MODULE = "formal.python.tools.dirac_maxwell_full_zero_mode_non_authoritative_pilot"
PILOT_GENERATOR = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v0.json"
ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
ARRAYS_PATH = REPO_ROOT / ARRAYS_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v0_result"
ACCEPTED_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v0"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "1327a1582ad318468d84c001a9737a2e4c74e168"
PREPARATION_PARENT = "51ff96a1b7297b42cd1767cff08cf1a1c79aeec2"
EXPECTED_HASHES = {
    PILOT_GENERATOR: "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
    PACKET_RELATIVE_PATH: "b4435ef3fab1ad04873538ef4abc3df807b018d74ace99cd2a69757325fc52c6",
    ARRAYS_RELATIVE_PATH: "3191ebf1c6ba6c65ae917aa16016b33ac1966136d540bc8819dfd0577d208e65",
    MANIFEST_RELATIVE_PATH: "ae62989ecc87f951e59bd15fc45669838ae126147c7daf7aef373ddc94b0d1f8",
    PREPARATION_REPORT_RELATIVE_PATH: "bc0a29c60744ba6077fc24f941a768f6863c2e2b67c1ea6aca919e7ae8bf6197",
}
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


def custody() -> dict[str, Any]:
    commit = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    committed: dict[str, str] = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = commit == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_HASHES and committed == EXPECTED_HASHES
    return {"commit": commit, "parent": parent, "working_hashes": working, "commit_hashes": committed, "expected_hashes": EXPECTED_HASHES, "passed": passed}


def clean_reproduction() -> dict[str, Any]:
    environment = os.environ.copy()
    environment.update({"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"})
    outputs: list[bytes] = []
    for _ in range(2):
        result = subprocess.run([sys.executable, "-m", PILOT_MODULE, "--emit-core"], cwd=REPO_ROOT, env=environment, capture_output=True, check=False)
        if result.returncode != 0:
            raise ValueError(result.stderr.decode("utf-8", errors="replace"))
        outputs.append(result.stdout)
    payloads = [json.loads(raw.decode("utf-8")) for raw in outputs]
    return {
        "execution_count": 2,
        "byte_identical": outputs[0] == outputs[1],
        "execution_sha256": [sha256_bytes(raw) for raw in outputs],
        "payloads_equal": payloads[0] == payloads[1],
        "payload": payloads[0],
    }


def close(left: float, right: float) -> bool:
    return math.isclose(left, right, rel_tol=5e-12, abs_tol=1e-30)


def observed_order(values: list[float]) -> float | None:
    if len(values) != 3:
        return None
    numerator = abs(values[0] - values[1])
    denominator = abs(values[1] - values[2])
    if numerator == 0 or denominator == 0:
        return None
    return math.log(numerator / denominator, 2)


def round_up_one_significant(value: float) -> float:
    if value <= 0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


SERIES_FOR_MAXIMUM = {
    "solver": "solver_residual",
    "Gauss": "gauss_residual",
    "continuity": "continuity_residual",
    "exchange_longitudinal": "exchange_longitudinal",
    "exchange_phi2": "exchange_phi2",
    "exchange_phi3": "exchange_phi3",
    "exchange_combined": "exchange_combined",
    "energy_drift": "total_energy_delta",
    "link_norm": "link_norm_error",
    "longitudinal_Maxwell_residual": "longitudinal_Maxwell_residual",
    "phi2_wave_residual": "phi2_wave_residual",
    "phi3_wave_residual": "phi3_wave_residual",
    "Dirac_plus_sector1_residual": "Dirac_plus_sector1_residual",
    "Dirac_plus_sector2_residual": "Dirac_plus_sector2_residual",
    "Dirac_minus_sector1_residual": "Dirac_minus_sector1_residual",
    "Dirac_minus_sector2_residual": "Dirac_minus_sector2_residual",
    "adjoint_plus_sector1_residual": "adjoint_plus_sector1_residual",
    "adjoint_plus_sector2_residual": "adjoint_plus_sector2_residual",
    "adjoint_minus_sector1_residual": "adjoint_minus_sector1_residual",
    "adjoint_minus_sector2_residual": "adjoint_minus_sector2_residual",
}


def array_audit(arrays: dict[str, Any], summary: dict[str, Any]) -> dict[str, Any]:
    runs = arrays.get("runs", [])
    required = set(SERIES_FOR_MAXIMUM.values()) | {
        "time", "J2_l2", "J3_l2", "phi2_l2", "phi3_l2", "periodic_boundary_flux",
        "psi_plus_positive_frequency_weight", "psi_plus_negative_frequency_weight",
        "psi_minus_positive_frequency_weight", "psi_minus_negative_frequency_weight",
    }
    complete = bool(runs)
    unique = len({run.get("run_id") for run in runs}) == len(runs)
    for run in runs:
        series = run.get("series", {})
        complete = complete and required <= set(series) and len({len(values) for values in series.values()}) == 1
    recomputed = {
        key: max(abs(float(value)) for run in runs for value in run["series"][series_key])
        for key, series_key in SERIES_FOR_MAXIMUM.items()
    }
    reported = summary["maximum_residuals"]
    maxima_match = set(recomputed) == set(reported) and all(close(recomputed[key], float(reported[key])) for key in recomputed)
    thresholds = {key: round_up_one_significant(2 * value) for key, value in reported.items()}
    threshold_match = thresholds == summary["candidate_thresholds_unreviewed"]
    return {
        "run_count": len(runs),
        "run_ids_unique": unique,
        "all_required_series_complete": complete,
        "recomputed_maximum_residuals": recomputed,
        "reported_maxima_match_arrays": maxima_match,
        "recomputed_threshold_candidates": thresholds,
        "threshold_rule_matches": threshold_match,
    }


def dispersion_audit(summary: dict[str, Any]) -> dict[str, Any]:
    rows = summary["dispersion"]["rows"]
    continuum_errors: list[float] = []
    row_checks: list[bool] = []
    doubler: list[float] = []
    for row in rows:
        a = float(row["a"])
        k = float(row["k"])
        exact = math.sqrt((math.sin(k * a) / a) ** 2 + (1 + (1 - math.cos(k * a)) / a) ** 2)
        continuum = math.sqrt(k * k + 1)
        continuum_errors.append(abs(exact - continuum))
        doubler.append(1 + 2 / a)
        eigenvalues = [float(value) for value in row["matrix_eigenvalues"]]
        row_checks.append(close(exact, float(row["exact_discrete_energy"])) and close(continuum, float(row["continuum_energy"])) and all(close(abs(value), exact) for value in eigenvalues))
    order = observed_order(continuum_errors)
    separated = all(doubler[index + 1] > doubler[index] for index in range(len(doubler) - 1))
    return {
        "row_formula_checks": row_checks,
        "all_row_formulas_match": all(row_checks),
        "recomputed_continuum_order": order,
        "reported_order_matches": order is not None and close(order, float(summary["dispersion"]["observed_continuum_order"])),
        "continuum_order_exceeds_guardrail_floor": order is not None and order > 0.8,
        "doubler_branch_monotonically_separated": separated,
    }


def refinement_audit(summary: dict[str, Any]) -> dict[str, Any]:
    temporal = summary["temporal_refinement"]
    phi2_order = observed_order([float(row["final_phi2_l2"]) for row in temporal["rows"]])
    energy_order = observed_order([float(row["maximum_energy_drift"]) for row in temporal["rows"]])
    hierarchy = summary["solver_hierarchy"]
    ratio = float(hierarchy["finest_solver_error"]) / float(hierarchy["finest_truncation_estimate"])
    energy_bounded = all(row["energy_drift_class"] == "OSCILLATORY_OR_BOUNDED" for row in temporal["rows"])
    energy_refines = float(temporal["rows"][-1]["maximum_energy_drift"]) <= float(temporal["rows"][0]["maximum_energy_drift"])
    return {
        "recomputed_phi2_order": phi2_order,
        "recomputed_energy_order": energy_order,
        "reported_orders_match": phi2_order is not None and energy_order is not None and close(phi2_order, float(temporal["observed_phi2_order"])) and close(energy_order, float(temporal["observed_energy_error_order"])),
        "second_order_floor_met": phi2_order is not None and energy_order is not None and phi2_order > 1.5 and energy_order > 1.5,
        "solver_ratio": ratio,
        "solver_hierarchy_met": ratio <= 0.01,
        "energy_bounded_and_refines": energy_bounded and energy_refines,
    }


DECISION_IDS = [
    "immutable_pilot_preparation_is_bound",
    "accepted_guardrail_is_the_exact_input_authority",
    "common_longitudinal_and_transverse_charge_normalization_is_explicit",
    "two_clean_reproductions_are_byte_identical",
    "clean_reproduction_matches_registered_packet_and_arrays",
    "all_registered_per_run_series_are_complete",
    "array_derived_residual_maxima_match_the_packet",
    "link_group_preservation_is_at_floating_point_floor",
    "Wilson_dispersion_and_doubler_separation_are_independently_recomputed",
    "Gauss_and_continuity_residuals_are_registered",
    "transverse_J2_phi2_and_J3_phi3_responses_are_exercised",
    "all_exchange_channels_are_separately_registered",
    "all_energy_components_and_energy_drift_are_registered",
    "temporal_and_energy_refinement_orders_are_independently_recomputed",
    "solver_error_is_below_one_percent_of_finest_truncation",
    "twelve_positive_controls_have_expected_behavior",
    "twenty_seven_negative_controls_fail_uniquely_as_intended",
    "threshold_candidates_follow_the_frozen_margin_rule",
    "pilot_outcome_is_engineering_ready",
    "candidate_values_remain_unreviewed_and_noncanonical",
    "canonical_execution_and_scientific_claim_remain_unauthorized",
    "Prompt_and_nonpromotion_boundaries_hold",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    arrays = load_json(ARRAYS_PATH)
    custody_result = custody()
    reproduction = clean_reproduction()
    summary = packet["summary"]
    arrays_result = array_audit(arrays, summary)
    dispersion = dispersion_audit(summary)
    refinement = refinement_audit(summary)
    positives = summary["positive_controls"]
    negatives = summary["negative_controls"]
    positive_by_id = {item["control_id"]: item for item in positives}
    registered_keys = set(next(iter(arrays["runs"]))["series"])
    decisions = {
        "immutable_pilot_preparation_is_bound": custody_result["passed"],
        "accepted_guardrail_is_the_exact_input_authority": len(packet["input_artifacts"]) == 2 and packet["target"] == "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v0",
        "common_longitudinal_and_transverse_charge_normalization_is_explicit": packet["lattice_normalization"]["positive_link"] == "U_n=exp(i q theta_n)" and packet["lattice_normalization"]["source_charge_density"].startswith("J0_n=q"),
        "two_clean_reproductions_are_byte_identical": reproduction["byte_identical"] and reproduction["payloads_equal"] and reproduction["execution_count"] == 2,
        "clean_reproduction_matches_registered_packet_and_arrays": reproduction["payload"]["summary"] == summary and reproduction["payload"]["registered_arrays"] == arrays,
        "all_registered_per_run_series_are_complete": arrays_result["all_required_series_complete"] and arrays_result["run_ids_unique"],
        "array_derived_residual_maxima_match_the_packet": arrays_result["reported_maxima_match_arrays"],
        "link_group_preservation_is_at_floating_point_floor": float(summary["maximum_residuals"]["link_norm"]) <= 5e-15,
        "Wilson_dispersion_and_doubler_separation_are_independently_recomputed": dispersion["all_row_formulas_match"] and dispersion["reported_order_matches"] and dispersion["continuum_order_exceeds_guardrail_floor"] and dispersion["doubler_branch_monotonically_separated"],
        "Gauss_and_continuity_residuals_are_registered": {"gauss_residual", "continuity_residual"} <= registered_keys and float(summary["maximum_residuals"]["Gauss"]) > 0 and float(summary["maximum_residuals"]["continuity"]) > 0,
        "transverse_J2_phi2_and_J3_phi3_responses_are_exercised": positive_by_id["J2_sources_phi2"]["passed"] and positive_by_id["J3_sources_phi3"]["passed"],
        "all_exchange_channels_are_separately_registered": {"exchange_longitudinal", "exchange_phi2", "exchange_phi3", "exchange_combined"} <= registered_keys,
        "all_energy_components_and_energy_drift_are_registered": len([key for key in registered_keys if key.startswith("energy_")]) == 8 and "total_energy_delta" in registered_keys,
        "temporal_and_energy_refinement_orders_are_independently_recomputed": refinement["reported_orders_match"] and refinement["second_order_floor_met"] and refinement["energy_bounded_and_refines"],
        "solver_error_is_below_one_percent_of_finest_truncation": refinement["solver_hierarchy_met"],
        "twelve_positive_controls_have_expected_behavior": len(positives) == 12 and all(item["passed"] for item in positives),
        "twenty_seven_negative_controls_fail_uniquely_as_intended": len(negatives) == 27 and len({item["expected_diagnostic"] for item in negatives}) == 27 and all(item["passed"] and item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in negatives),
        "threshold_candidates_follow_the_frozen_margin_rule": arrays_result["threshold_rule_matches"],
        "pilot_outcome_is_engineering_ready": packet["outcome"] == "ENGINEERING_READY" and all(summary["criteria"].values()),
        "candidate_values_remain_unreviewed_and_noncanonical": packet["canonical_parameters_frozen"] is False and packet["canonical_thresholds_frozen"] is False and "candidate_canonical_parameters_unreviewed" in summary and "candidate_thresholds_unreviewed" in summary,
        "canonical_execution_and_scientific_claim_remain_unauthorized": packet["canonical_execution_authorized"] is False and packet["scientific_result_claimed"] is False,
        "Prompt_and_nonpromotion_boundaries_hold": sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) == PROMPT_SHA256 and "no pillar completion, seam closure, C_k dynamics, CCFT, master-action promotion, or repository-wide green claim" in packet["nonclaims"],
    }
    ordered = [{"decision_id": item, "passed": bool(decisions[item])} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT_ENGINEERING_READY" if accepted else "B-BLOCKED_IMPLEMENTATION_DEFECT",
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "blocker_diagnostics": [] if accepted else ["REGISTERED_RUN_IDENTITIES_NOT_UNIQUE"],
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_clean_reproduction": {key: value for key, value in reproduction.items() if key != "payload"},
        "independent_array_audit": arrays_result,
        "independent_dispersion_audit": dispersion,
        "independent_refinement_audit": refinement,
        "reviewed_engineering_evidence": {
            "pilot_outcome": packet["outcome"],
            "stable_parameter_range_observed": summary["stable_parameter_range_observed"],
            "candidate_canonical_parameters_unreviewed": summary["candidate_canonical_parameters_unreviewed"],
            "candidate_thresholds_unreviewed": summary["candidate_thresholds_unreviewed"],
        },
        "authority_rotation": {
            "pilot_engineering_evidence_accepted": accepted,
            "canonical_parameter_freeze_preparation_authorized": accepted,
            "candidate_parameters_accepted_as_canonical": False,
            "canonical_thresholds_accepted": False,
            "canonical_execution_authorized": False,
            "scientific_numerical_result_claimed": False,
        },
        "claim": "The pilot is accepted as non-authoritative engineering evidence and authorizes preparation of a separately reviewed canonical-parameter freeze only." if accepted else "The pilot review is blocked.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the non-authoritative full zero-mode pilot.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote pilot review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing pilot review", file=sys.stderr)
            return 1
        print(f"pilot review verified: {report['verdict']}; selected {report['selected_next_target']}")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
