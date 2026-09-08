from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as numerical


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_result_review.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_20260713_v0.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail.py"
PREPARATION_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessGuardrailPacket.lean"
NUMERICAL_IMPLEMENTATION_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v0_result"
SELECTED_NEXT_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_packet_v0"
BLOCKER_CODE = "B-BLOCKED_F_PERP_NORMALIZATION_NOT_BOUNDED"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "a38e1884bb05851cb96e37f748129cacccb38c8d"
PREPARATION_PARENT = "88e054232edf8f93c9b765e60d15748145f5747d"
EXPECTED_PREPARATION_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "04c9683fb363d273507abb96a6cc67c9154984a3dfd92e33662638e163476157",
    PACKET_RELATIVE_PATH: "48f4657fbfb93730678774e56ebdf13f3bfbb039b49e1941a40ab9e5ab718fef",
    MANIFEST_RELATIVE_PATH: "b5227816910494b5f81bfd69a4a87ba99fb8d5c2b0f2cf2d24e862dafead07d5",
    PREPARATION_REPORT_RELATIVE_PATH: "bdcc24e71d447c2cd176f0450ec8cfe151cf553b821841f5d0a26476e043ef17",
    PREPARATION_LEAN_RELATIVE_PATH: "b17334cab717476b0cb8942fb253f66e1c46aee244e14077a35abeb1661b18f5",
}
NUMERICAL_IMPLEMENTATION_SHA256 = "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1"
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


def git_output(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT)


def bind_preparation() -> dict[str, Any]:
    if git_output("rev-parse", f"{PREPARATION_COMMIT}^").decode().strip() != PREPARATION_PARENT:
        raise ValueError("preparation parent mismatch")
    if subprocess.run(["git", "merge-base", "--is-ancestor", PREPARATION_COMMIT, "HEAD"], cwd=REPO_ROOT).returncode != 0:
        raise ValueError("preparation commit is not an ancestor of HEAD")
    for relative_path, digest in EXPECTED_PREPARATION_HASHES.items():
        committed = git_output("show", f"{PREPARATION_COMMIT}:{relative_path}")
        if sha256_bytes(committed) != digest:
            raise ValueError(f"committed preparation hash mismatch: {relative_path}")
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"working preparation hash mismatch: {relative_path}")
    if sha256_path(REPO_ROOT / NUMERICAL_IMPLEMENTATION_RELATIVE_PATH) != NUMERICAL_IMPLEMENTATION_SHA256:
        raise ValueError("accepted numerical implementation hash mismatch")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        raise ValueError("Prompt.txt changed")
    return {
        "preparation_commit": PREPARATION_COMMIT,
        "preparation_parent": PREPARATION_PARENT,
        "preparation_paths": EXPECTED_PREPARATION_HASHES,
    }


def independent_phase_counterexample() -> dict[str, Any]:
    n = 32
    delta = math.pi / 2
    state = numerical.initial_state("full_mixed", n, numerical.CHARGE)
    phase = complex(math.cos(delta), math.sin(delta))
    for species in ("psi_plus", "psi_minus"):
        state[species][:, [1, 3]] *= phase
    energies = numerical.energy_components(state, numerical.LENGTH / n, numerical.CHARGE)
    numerator = energies["phi2"] + energies["phi3"]
    denominator = sum(energies.values())
    value = numerator / denominator
    return {
        "grid_size": n,
        "delta_theta_psi_radians": delta,
        "transverse_descendant_energy": numerator,
        "registered_signed_total_energy": denominator,
        "f_perp_initial": value,
        "exceeds_declared_upper_bound": value > 1.0,
        "calculation_imports_preparation_generator": False,
    }


def reconstruct_decisions(packet: dict[str, Any], report: dict[str, Any], counterexample: dict[str, Any]) -> dict[str, bool]:
    audit = packet.get("normalization_audit", {})
    boundary = packet.get("authority_boundary", {})
    completion = packet.get("guardrail_completion", {})
    candidates = packet.get("repair_route_candidates_for_separate_review", [])
    return {
        "preparation_target_exact": packet.get("target") == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v0",
        "preparation_reports_blocker_pending_review": packet.get("verdict") == "PREPARED_BLOCKER_PENDING_INDEPENDENT_REVIEW",
        "blocker_code_exact": packet.get("blocker_code") == BLOCKER_CODE and report.get("blocker_code") == BLOCKER_CODE,
        "accepted_axis_formula_preserved": audit.get("accepted_definition") == "(E_phi2(0)+E_phi3(0))/E_total(0)",
        "accepted_fraction_domain_preserved": audit.get("accepted_declared_domain") == "0 <= f_perp_initial <= 1",
        "counterexample_independently_exceeds_one": counterexample["exceeds_declared_upper_bound"] is True,
        "counterexample_value_agrees": math.isclose(counterexample["f_perp_initial"], audit.get("counterexample", {}).get("f_perp_initial", math.nan), rel_tol=0.0, abs_tol=1e-15),
        "only_admitted_phase_axis_varied": audit.get("counterexample_uses_only_admitted_axes") is True and audit.get("fixed_audit_inputs", {}).get("varied_axis") == "DELTA_THETA_PSI",
        "signed_denominator_not_declared_positive_definite": audit.get("denominator_positive_definite_established") is False,
        "bounded_fraction_contract_fails": audit.get("bounded_fraction_contract_satisfied") is False,
        "matrix_and_thresholds_unfrozen": all(completion.get(key) is False for key in ("exact_axis_values_frozen", "scientific_parameter_matrix_frozen", "comparator_eligibility_matrix_frozen", "observable_thresholds_frozen", "control_run_roles_frozen", "pilot_subset_frozen")),
        "pilot_and_execution_unauthorized": boundary.get("pilot_authorized") is False and boundary.get("canonical_robustness_execution_authorized") is False,
        "canonical_result_not_reopened": packet.get("canonical_result_reopened") is False and boundary.get("canonical_result_remains_accepted_E_REPRO") is True,
        "no_repair_method_auto_selected": len(candidates) == 4 and not any(item.get("selected") for item in candidates),
        "all_preparation_mutations_discriminate": len(packet.get("mutation_controls", [])) == 14 and all(item.get("passed") is True and item.get("actual_diagnostics") == [item.get("expected_diagnostic")] for item in packet["mutation_controls"]),
        "claim_nonpromotion_preserved": all(boundary.get(key) is False for key in ("pillar_completion_claimed", "seam_closure_claimed", "C_k_dynamics_claimed", "CCFT_validation_claimed", "master_action_promotion_claimed")),
    }


def build_review() -> dict[str, Any]:
    binding = bind_preparation()
    packet = load_json(REPO_ROOT / PACKET_RELATIVE_PATH)
    preparation_report = load_json(REPO_ROOT / PREPARATION_REPORT_RELATIVE_PATH)
    counterexample = independent_phase_counterexample()
    decisions = reconstruct_decisions(packet, preparation_report, counterexample)
    accepted = all(decisions.values())
    if not accepted:
        raise ValueError(f"independent blocker review failed: {[key for key, value in decisions.items() if not value]}")
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": True,
        "verdict": BLOCKER_CODE,
        "blocker_confirmed": True,
        "blocker_statement": "F_PERP_INITIAL cannot be frozen as a bounded [0,1] fraction because its accepted denominator is the signed registered c-number Dirac total energy; an admitted +pi/2 sector-phase row gives f_perp_initial > 1.",
        "independent_counterexample": counterexample,
        "review_decisions": decisions,
        "preparation_binding": binding,
        "preparation_generator_imported": False,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET,
        "authority_rotation": {
            "guardrail_blocker_accepted": True,
            "axis_normalization_repair_preparation_authorized": True,
            "robustness_guardrail_accepted": False,
            "exact_parameter_matrix_frozen": False,
            "robustness_pilot_authorized": False,
            "canonical_robustness_execution_authorized": False,
            "canonical_E_REPRO_result_remains_accepted": True,
            "accepted_scientific_design_rewritten": False,
            "repair_method_selected": False,
            "pillar_completion_authorized": False,
            "seam_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_validation_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "claim_ceiling": "An independent review confirms a normalization contradiction in the unexecuted robustness guardrail. The accepted canonical E-REPRO result remains immutable; no robustness matrix, calibration, or execution is authorized.",
        "prompt_sha256": PROMPT_SHA256,
    }


def write_review() -> None:
    REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REVIEW_REPORT_PATH.write_bytes(canonical_json_bytes(build_review()))


def check_review() -> bool:
    return REVIEW_REPORT_PATH.exists() and REVIEW_REPORT_PATH.read_bytes() == canonical_json_bytes(build_review())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    if args.write:
        write_review()
    if args.check and not check_review():
        return 1
    if args.stdout:
        print(canonical_json_bytes(build_review()).decode("utf-8"), end="")
    if not (args.write or args.check or args.stdout):
        parser.error("one of --write, --check, or --stdout is required")
    return 0


if __name__ == "__main__":
    sys.exit(main())
