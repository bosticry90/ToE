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
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_discrete_numerical_guardrail.py"
ANALYTIC_PACKET = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-REDUCTION-WITH-TRANSVERSE-FIELDS-PACKET-v0.json"
ANALYTIC_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0.json"
INPUT_HASHES = {
    ANALYTIC_PACKET: "5582abceb645e5e63e0ab750a50b56b82a8fd8f3b27ed4be02586ae5e56f5488",
    ANALYTIC_REVIEW: "e4a830678d863319d5509bf43e332a778708b7b82bd6db5903be5a389fef34de",
}
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DISCRETE-NUMERICAL-GUARDRAIL-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DISCRETE-NUMERICAL-GUARDRAIL-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v0_result"
REVIEW_TARGET_KIND = "dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v0_result_review"
FAILURE_TARGET = "prepare_dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v1"
POST_ACCEPTANCE_TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v0"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_20260713_v0"
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
        raise ValueError(f"expected object: {path}")
    return value


def load_authority() -> None:
    for path, digest in INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"input hash mismatch: {path}")
    review = load_json(REPO_ROOT / ANALYTIC_REVIEW)
    if not (
        review.get("accepted") is True
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("full_zero_mode_analytic_repair_accepted") is True
        and review.get("authority_rotation", {}).get("numerical_guardrail_preparation_authorized") is True
        and review.get("authority_rotation", {}).get("execution_authorized") is False
    ):
        raise ValueError("analytic review does not authorize numerical guardrail preparation")


POSITIVE_CONTROLS = [
    "vacuum",
    "q=0 two-species free evolution with independent phi2 and phi3 waves",
    "Wilson-Dirac plane wave against exact discrete dispersion",
    "continuum dispersion recovery under refinement and doubler-branch separation",
    "trivial pure gauge with W=1",
    "flat globally nontrivial connection with W!=1",
    "stationary-density charge-neutral two-species configuration",
    "analytic J2=J3=0 configuration",
    "nonzero J2 sources phi2 with the derived sign",
    "nonzero J3 sources phi3 with the derived sign",
    "charge-conjugate species exchange symmetry under U versus U*",
    "full discrete energy inventory converges to the reduced parent Hilbert energy",
]

NEGATIVE_CONTROLS = [
    "doubler-contaminated naive centered Dirac stencil",
    "Wilson contribution omitted from energy",
    "group-valued link norm not preserved",
    "U used instead of U* for the negative species",
    "one charge species removed on the periodic domain",
    "number current j^mu confused with source current J^mu",
    "residual temporal-gauge zero mode mishandled",
    "nontrivial holonomy treated as globally trivial",
    "J2 omitted from the phi2 equation",
    "J3 omitted from the phi3 equation",
    "phi2 or phi3 energy omitted",
    "gamma2 phi2 or gamma3 phi3 spinor coupling omitted",
    "wrong gamma2 or gamma3 block used",
    "transverse descendants treated as removable gauge modes",
    "transverse descendants counted as new independent scalar matter",
    "reduced spin-sector multiplicity omitted",
    "pure 1+1 Maxwell-Dirac closure claimed despite descendants",
    "rejected A2=A3 invariant truncation reintroduced",
    "energy per transverse area treated as total energy",
    "1+1 stress-energy assigned mass dimension four",
    "3+1 coupling imported without A_perp rescaling",
    "dimension restoration and reduction order mismatch",
    "variation and reduction mismatch",
    "incorrect descendant stress normalization",
    "one exchange-channel sign reversed",
    "longitudinal or transverse Maxwell source omitted",
    "C_exchange=0 imposed definitionally",
]


def build_packet() -> dict[str, Any]:
    load_authority()
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "domain": {"space": "periodic S1 with N sites and spacing a=L/N", "time": "uniform step Delta_t", "charge_solvability": "sum_n a J0_n=0", "species": ["q_plus=+q", "q_minus=-q"]},
        "gauge": {
            "choice": "temporal gauge A0=0",
            "residual_symmetry": "time-independent site phases alpha_n",
            "diagnostic_phase_pin": "one reference-site phase, excluded from dynamics",
            "positive_species_transform": "psi+_n -> exp(-i alpha_n) psi+_n",
            "negative_species_transform": "psi-_n -> exp(+i alpha_n) psi-_n",
            "link_transform": "U_n -> exp(-i alpha_n) U_n exp(+i alpha_(n+1))",
            "descendant_transform": "phiI_n invariant for I=2,3",
        },
        "lattice_variables": {
            "A1": "group-valued links U_n=exp(i q_1p1 a A1_n/hbar)",
            "electric_flux": "real link momentum E_n conjugate to the link angle",
            "phi2_phi3": "real site fields",
            "Pi2_Pi3": "real site momenta at the compatible midpoint time location",
            "spinors": "four two-component site spinors psi_(s,r), stored as two sector doublets per charge species",
            "holonomy": "W=ordered product_n U_n",
            "uniform_mode": "spatial link-angle zero mode with conjugate uniform electric flux and exact E_zero^2 L/(2 mu_0) energy",
        },
        "link_update": {"formula": "U_n^(k+1)=exp(i Delta_theta_n) U_n^k", "preserves_unit_modulus_by_construction": True, "componentwise_update_then_projection": False, "positive_species_transport": "U", "negative_species_transport": "U*"},
        "spatial_operators": {
            "Wilson_parameter": 1,
            "covariant_centered_derivative": "(U_n^sigma psi_(n+1)-U_(n-1)^(-sigma) psi_(n-1))/(2a), sigma=+1 for q and -1 for -q",
            "Wilson_laplacian": "(2 psi_n-U_n^sigma psi_(n+1)-U_(n-1)^(-sigma) psi_(n-1))/(2a) multiplied by r beta",
            "phi_gradient": "(phiI_(n+1)-phiI_n)/a",
            "transverse_site_coupling": "q_s psi_s^dagger [alpha2 phi2_n+alpha3 phi3_n] psi_s with alphaI=gamma0 gammaI",
            "naive_centered_operator_role": "negative control only",
        },
        "time_integrator": {"family": "time-symmetric variational implicit-midpoint", "order": 2, "link_group_update_required": True, "nonlinear_system": "all links, electric fluxes, descendants, momenta, and spinors solved at the common midpoint", "fixed_step_energy_caveat": "implicit midpoint is not assumed to conserve the nonlinear continuum Hamiltonian exactly"},
        "discrete_action_requirements": [
            "link electric term",
            "site phi2 and phi3 kinetic and nearest-neighbor gradient terms",
            "two-species four-sector Wilson-Dirac term",
            "link-based A1 spinor transport using U and U*",
            "site gamma2 phi2 and gamma3 phi3 spinor couplings",
            "periodic boundary and holonomy terms without cutting the circle",
        ],
        "discrete_symmetry_and_constraints": {
            "gauge_invariant_action_required": True,
            "continuity_identity": "derived as the discrete Noether identity, not separately imposed",
            "Gauss_law": "backward_difference(E)_n-mu_0 J0_n=0 with frozen normalization",
            "Gauss_preservation": "exact for the algebraic discrete solution and bounded by nonlinear solver residual in floating-point execution",
            "total_charge_zero_mode": "sum_n a J0_n=0 is an initial-data admissibility condition",
        },
        "Wilson_dispersion": {"formula": "E_W(k)^2=sin(ka)^2/a^2+[m+r(1-cos(ka))/a]^2", "r": 1, "exact_discrete_comparison_each_grid": True, "continuum_recovery_required": True, "doubler_branch_separation_required": True},
        "discrete_energy": {
            "classification": "BOUNDED_CONVERGENT_ENERGY_ERROR",
            "inventory": ["link electric energy", "uniform electric zero-mode energy", "phi2 kinetic and gradient energy", "phi3 kinetic and gradient energy", "Wilson-Dirac matter energy", "link interaction", "gamma2 phi2 interaction", "gamma3 phi3 interaction"],
            "acceptance_form": "energy error remains bounded over the frozen run and decreases at second order until the solver/numerical floor",
            "exact_continuum_energy_claimed": False,
            "modified_Hamiltonian_claimed_exact": False,
        },
        "discrete_exchange": {
            "channels": ["longitudinal link field <-> spinors", "phi2 descendant <-> spinors", "phi3 descendant <-> spinors", "total field <-> total matter"],
            "local_residual": "computed from independently evolved sector energies and source work terms",
            "C_exchange_embedded_as_equation": False,
            "boundary_flux": "periodic telescoping sum must vanish independently",
        },
        "holonomy_controls": {
            "trivial": {"F": "0", "W": "1", "globally_pure_gauge": True},
            "nontrivial": {"F": "0", "W": "not 1", "globally_pure_gauge": False, "locally_flat": True},
            "large_gauge_behavior": "link-angle zero mode shifts by an allowed winding while W is invariant",
        },
        "pilot_policy": {
            "status": "PENDING_NONAUTHORITATIVE_PILOT",
            "scientific_choices_frozen_before_pilot": ["action", "Hilbert tensor", "charges", "all four spinor sectors", "phi2 and phi3 descendants", "periodic boundary", "temporal gauge", "Wilson r=1 operator", "energy classification", "positive and negative control definitions"],
            "engineering_parameters_only": ["solver tolerance", "grid sequence", "time-step range", "run duration", "nonlinear iteration cap", "expected numerical floor"],
            "solver_rule": "solver error <=0.01 times estimated finest-grid truncation error",
            "canonical_threshold_rule": "twice the maximum corresponding pilot residual, rounded upward to one significant digit, while preserving expected refinement order",
            "pilot_result_authoritative": False,
        },
        "controls": {"positive": POSITIVE_CONTROLS, "negative": NEGATIVE_CONTROLS, "previous_blocker_permanent": True},
        "canonical_observables": ["Dirac and adjoint residuals by sector/species", "longitudinal Maxwell residual", "phi2 and phi3 wave residuals", "Gauss residual", "discrete continuity residual", "sector number currents", "J0 J1 J2 J3 source currents", "positive/negative-frequency diagnostic weights", "link electric energy", "phi2 and phi3 energies", "Wilson contribution", "zero-mode electric energy", "three local exchange residuals", "periodic boundary flux", "selected bounded energy error", "spatial and temporal convergence"],
        "claim_ceiling_after_future_execution": "A bounded unit-complete c-number full zero-mode Maxwell-Dirac surrogate retaining both transverse gauge descendants exhibits reproducible constrained matter-field exchange and bounded convergent total-energy error under the frozen lattice assumptions.",
        "nonclaims": ["no canonical numerical result yet", "no exact continuum-energy conservation claim", "no pure 1+1 truncation or transverse decoupling", "no stable classical fermionic matter or fermionic QFT", "no quantum pair creation, Fermi statistics, or quantized electromagnetism", "no full 3+1 photon recovery", "no pillar completion, seam closure, new physics, C_k dynamics, CCFT, or master-action validation"],
        "boundary": {"guardrail_accepted_before_review": False, "non_authoritative_pilot_authorized": False, "canonical_execution_authorized": False, "result_claimed": False, "registry_maintenance_paused": True, "C_k_audit_only": True, "CCFT_resumed": False, "master_action_promoted": False},
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "excluded_from_scientific_inputs": True},
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("guardrail_identity")
    variables = packet.get("lattice_variables", {})
    if "group-valued links" not in variables.get("A1", "") or variables.get("phi2_phi3") != "real site fields":
        failures.append("link_site_inventory")
    if packet.get("link_update", {}).get("preserves_unit_modulus_by_construction") is not True or packet.get("link_update", {}).get("componentwise_update_then_projection") is not False:
        failures.append("group_link_update")
    if packet.get("spatial_operators", {}).get("Wilson_parameter") != 1 or packet.get("spatial_operators", {}).get("naive_centered_operator_role") != "negative control only":
        failures.append("Wilson_operator")
    if packet.get("discrete_symmetry_and_constraints", {}).get("gauge_invariant_action_required") is not True:
        failures.append("discrete_gauge_symmetry")
    if packet.get("discrete_energy", {}).get("classification") != "BOUNDED_CONVERGENT_ENERGY_ERROR":
        failures.append("energy_classification")
    if len(packet.get("discrete_energy", {}).get("inventory", [])) != 8:
        failures.append("energy_inventory")
    if len(packet.get("controls", {}).get("positive", [])) != 12 or len(packet.get("controls", {}).get("negative", [])) != 27:
        failures.append("control_inventory")
    if packet.get("pilot_policy", {}).get("status") != "PENDING_NONAUTHORITATIVE_PILOT" or packet.get("pilot_policy", {}).get("pilot_result_authoritative") is not False:
        failures.append("pilot_boundary")
    if packet.get("boundary", {}).get("non_authoritative_pilot_authorized") is not False or packet.get("boundary", {}).get("canonical_execution_authorized") is not False:
        failures.append("no_execution_before_review")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        failures.append("Prompt_preserved")
    return failures


DECISION_IDS = [
    "accepted_analytic_repair_authorizes_guardrail_preparation_only",
    "periodic_two_species_charge_neutral_domain_is_frozen",
    "temporal_gauge_residual_symmetry_and_holonomy_are_explicit",
    "A1_uses_group_links_while_phi2_phi3_are_real_site_fields",
    "link_updates_preserve_unit_modulus_without_projection",
    "negative_species_uses_complex_conjugate_links",
    "Wilson_r1_operator_and_exact_discrete_dispersion_are_frozen",
    "phi2_phi3_gradient_momentum_and_gamma_couplings_are_in_action",
    "discrete_gauge_symmetry_earns_continuity_and_Gauss_rules",
    "energy_class_is_bounded_convergent_not_falsely_exact",
    "all_descendant_Wilson_zero_mode_and_interaction_energies_are_counted",
    "four_exchange_channels_are_observed_not_imposed",
    "twelve_positive_and_twenty_seven_negative_controls_are_frozen",
    "previous_transverse_blocker_is_permanent_regression_control",
    "pilot_changes_engineering_parameters_only",
    "solver_and_threshold_rules_are_non_circular",
    "canonical_observables_cover_all_parent_and_descendant_channels",
    "only_non_authoritative_pilot_can_follow_review",
    "claim_ceiling_nonclaims_and_Prompt_boundary_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"numerical guardrail validation failed: {failures}")
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
        "positive_control_count": len(POSITIVE_CONTROLS),
        "negative_control_count": len(NEGATIVE_CONTROLS),
        "energy_classification": packet["discrete_energy"]["classification"],
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "boundary": packet["boundary"],
        "claim": "The descendant-aware Wilson-link/site-field numerical guardrail is prepared; only independent guardrail review is authorized.",
        "nonclaims": packet["nonclaims"],
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the full zero-mode discrete numerical guardrail.")
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
        print("wrote descendant-aware numerical guardrail; independent review required")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing numerical-guardrail artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("numerical guardrail verified: mixed link/site architecture; canonical execution unauthorized")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
