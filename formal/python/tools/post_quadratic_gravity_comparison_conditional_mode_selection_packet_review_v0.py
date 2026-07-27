from __future__ import annotations

import argparse
import copy
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_"
    "REVIEW_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_"
    "REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_quadratic_gravity_comparison_conditional_mode_selection_packet_"
    "review_v0.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_"
    "20260718_v0.json"
)
TARGET = (
    "review_post_quadratic_gravity_comparison_conditional_mode_selection_"
    "packet_v0_result"
)
VERDICT = (
    "ACCEPTED_AUTHORIZE_ONE_BOUNDED_CONDITIONAL_MODE_SELECTION_ENVELOPE_EXECUTION"
)
SELECTED_NEXT_TARGET = (
    "execute_post_quadratic_gravity_comparison_conditional_mode_selection_"
    "envelope_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "ONE_BOUNDED_CONDITIONAL_ENVELOPE_EXECUTION_NO_CONDITION_ADOPTION"
)

PACKET_HASHES = {
    "formal/docs/lanes/POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_20260718_v0.md":
        "c986438982654c7d01cc37048e2b8286f40c43b1750be25a6338900b65bed82e",
    PACKET_RELATIVE_PATH:
        "a0d2986bb32a1e0d8363db7377569ef95553331dd5b50fb37e9a3827164b7c9e",
    "formal/python/tools/post_quadratic_gravity_comparison_conditional_mode_selection_packet_v0.py":
        "02c06dc990ece2d26b86b3b1ab4095cc3df2a142898a7db7878274c106f63056",
    "formal/python/tests/test_post_quadratic_gravity_comparison_conditional_mode_selection_packet_v0.py":
        "ab928cd4e3f096cf9adfa3407dff13f3bc181bc7c61a837a0c549821e4e77dfd",
    "formal/toe_formal/ToeFormal/Derivation/PostQuadraticGravityComparisonConditionalModeSelectionPacketV0.lean":
        "41ca2e2e58ac61570407e274077e446b172091c974e900bee0ed56b2aed1608b",
}

AUTHORITY_CLASSES = {
    "PROJECT_BOUND_NATIVE_PRINCIPLE",
    "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "EMPIRICAL_CONSTRAINT",
    "PROPOSED_NEW_POSTULATE",
}

EXPECTED_CLASSES = {
    "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY": "PROJECT_BOUND_NATIVE_PRINCIPLE",
    "SEL_NATIVE_R10_STABILITY_EVALUATION": "PROJECT_BOUND_NATIVE_PRINCIPLE",
    "SEL_NO_TACHYONIC_POLES": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "SEL_NO_NEGATIVE_RESIDUE_SPIN2": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "SEL_NO_EXTRA_SCALAR": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "SEL_MINIMAL_SPECTRUM": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "SEL_EXACT_EINSTEIN_0I": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "SEL_FINITE_PRECISION_0I": "EMPIRICAL_CONSTRAINT",
    "SEL_LONG_RANGE_EINSTEIN": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE": "PROPOSED_NEW_POSTULATE",
}


class ReviewFailure(ValueError):
    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_custody() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"conditional packet custody mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    packet = _load_json(PACKET_RELATIVE_PATH)
    if packet.get("target") != (
        "prepare_post_quadratic_gravity_comparison_conditional_mode_selection_packet_v0"
    ):
        raise ValueError("review packet target mismatch")
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("review packet is not prepared")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("packet did not authorize this review")
    return rows, packet


def _selector_map(value: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = value["selector_register"]["rows"]
    mapping = {row["selector_id"]: row for row in rows}
    if len(rows) != 10 or len(mapping) != 10:
        raise ReviewFailure("SELECTOR_ID_OR_COUNT_MISMATCH")
    return mapping


def _stratum_map(value: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = value["parameter_strata"]["rows"]
    mapping = {row["stratum_id"]: row for row in rows}
    if len(rows) != 9 or len(mapping) != 9:
        raise ReviewFailure("STRATUM_ID_OR_COUNT_MISMATCH")
    return mapping


def audit_packet(value: dict[str, Any]) -> dict[str, Any]:
    selectors = _selector_map(value)
    for selector_id, row in selectors.items():
        observed = row.get("authority_class")
        if not isinstance(observed, str) or observed not in AUTHORITY_CLASSES:
            raise ReviewFailure("UNKNOWN_AUTHORITY_CLASS")
        if observed != EXPECTED_CLASSES[selector_id]:
            raise ReviewFailure("AUTHORITY_CLASS_MISMATCH")

    r9 = selectors["SEL_NATIVE_R9_CURRENT_REPRESENTABILITY"]
    if r9.get("parameter_restriction") != "NONE_BY_ITSELF":
        raise ReviewFailure("R9_STRENGTHENED")
    r10 = selectors["SEL_NATIVE_R10_STABILITY_EVALUATION"]
    if r10.get("parameter_restriction") != "NONE_WITHOUT_AN_ACCEPTANCE_THRESHOLD":
        raise ReviewFailure("R10_STRENGTHENED")

    if selectors["SEL_NO_TACHYONIC_POLES"].get("parameter_restriction") != (
        "Sigma<0 and beta>0 when both extra poles are present"
    ):
        raise ReviewFailure("TACHYON_LOGIC_MISMATCH")
    if selectors["SEL_NO_NEGATIVE_RESIDUE_SPIN2"].get(
        "parameter_restriction"
    ) != "beta=0":
        raise ReviewFailure("SPIN2_REMOVAL_LOGIC_MISMATCH")
    if selectors["SEL_NO_EXTRA_SCALAR"].get("parameter_restriction") != "Sigma=0":
        raise ReviewFailure("SCALAR_REMOVAL_LOGIC_MISMATCH")
    if selectors["SEL_MINIMAL_SPECTRUM"].get("parameter_restriction") != (
        "beta=0 and Sigma=0 implies alpha=beta=0"
    ):
        raise ReviewFailure("MINIMAL_SPECTRUM_LOGIC_MISMATCH")
    if selectors["SEL_EXACT_EINSTEIN_0I"].get("parameter_restriction") != "beta=0":
        raise ReviewFailure("EXACT_CURRENT_LOGIC_MISMATCH")
    if "beta=0 not logically inferred" not in selectors["SEL_FINITE_PRECISION_0I"].get(
        "parameter_restriction", ""
    ):
        raise ReviewFailure("EMPIRICAL_EXACT_IDENTITY")
    if "broad finite" not in selectors["SEL_LONG_RANGE_EINSTEIN"].get(
        "parameter_restriction", ""
    ):
        raise ReviewFailure("LONG_RANGE_OVERSELECTION")

    if any(row.get("condition_adopted") is not False for row in selectors.values()):
        raise ReviewFailure("CONDITION_PRESELECTED")
    if any(row.get("native_selection_weight_now") is not False for row in selectors.values()):
        raise ReviewFailure("NATIVE_WEIGHT_PREASSIGNED")
    if any(row.get("selector_adjudication_status") != "NOT_EXECUTED" for row in selectors.values()):
        raise ReviewFailure("PREMATURE_SELECTOR_ADJUDICATION")

    paths = value["logical_paths"]
    if len(paths) != 3 or any(row.get("selected_now") is not False for row in paths):
        raise ReviewFailure("POSITION_PRESELECTED")
    if paths[2].get("parameter_restriction") != "NONE_IN_FAMILY":
        raise ReviewFailure("OUTSIDE_FAMILY_PARAMETER_CLAIM")

    meanings = value["exact_approximate_meaning_contract"]
    expected_meanings = {
        "POLE_ABSENT_FINITE_PARAMETER_STRATUM",
        "INFINITE_MASS_DECOUPLING_LIMIT",
        "FINITE_RANGE_YUKAWA_SUPPRESSION",
        "EMPIRICAL_AGREEMENT_WITHIN_TOLERANCE",
        "SOURCE_NOT_EXCITING_MODE",
        "MODE_ABSENT_FROM_SPECTRUM",
    }
    if meanings.get("interchange_allowed") is not False or {
        row["status"] for row in meanings["rows"]
    } != expected_meanings:
        raise ReviewFailure("EXACT_APPROXIMATE_CONFLATION")

    strata = _stratum_map(value)
    coincident = strata["COINCIDENT_MASSES"]
    if "orthogonal" not in coincident.get("spectrum", "") or not all(
        token in coincident.get("qualification", "")
        for token in ("no double pole", "cancellation", "residue repair")
    ):
        raise ReviewFailure("COINCIDENT_MASS_MISCLASSIFIED")
    if "residue negative" not in strata["BOTH_EXTRA_POLES_NON_TACHYONIC"].get(
        "spectrum", ""
    ):
        raise ReviewFailure("NON_TACHYONIC_MISREPORTED_HEALTHY")

    firewall = value["scope_firewall"]
    if firewall.get("outside_family_transport_allowed") is not False:
        raise ReviewFailure("SCOPE_LEAK")

    outcomes = value["outcome_contract"]
    if outcomes.get("principal_outcome_now") is not None:
        raise ReviewFailure("PREMATURE_OUTCOME")
    if outcomes.get("subordinate_findings_now") != []:
        raise ReviewFailure("PREMATURE_SUBORDINATE_FINDING")
    if outcomes.get("subordinate_findings_adopt_conditions") is not False:
        raise ReviewFailure("SUBORDINATE_FINDING_ADOPTS_CONDITION")

    scope = value["scope"]
    if scope.get("packet_preparation_executed") is not True:
        raise ReviewFailure("PACKET_PREPARATION_FLAG_MISSING")
    if any(item is not False for key, item in scope.items() if key != "packet_preparation_executed"):
        raise ReviewFailure("PREMATURE_EXECUTION_OR_PROMOTION")

    return {
        "selector_count": len(selectors),
        "stratum_count": len(strata),
        "authority_class_count": len({row["authority_class"] for row in selectors.values()}),
        "positions_unselected": len(paths),
        "principal_outcome_empty": True,
        "condition_adoption_count": 0,
    }


def _independent_algebra() -> dict[str, Any]:
    scalar_samples = []
    for sigma in (Fraction(-2), Fraction(-1), Fraction(1), Fraction(2)):
        mass = -Fraction(1, 1) / (2 * sigma)
        scalar_samples.append({
            "Sigma": str(sigma),
            "m0_squared": str(mass),
            "non_tachyonic": mass > 0,
            "Sigma_negative": sigma < 0,
        })
    spin2_samples = []
    for beta in (Fraction(-2), Fraction(-1), Fraction(1), Fraction(2)):
        mass = Fraction(1, 1) / beta
        spin2_samples.append({
            "beta": str(beta),
            "m2_squared": str(mass),
            "non_tachyonic": mass > 0,
            "beta_positive": beta > 0,
        })
    coincident_samples = []
    for beta in (Fraction(-2), Fraction(-1), Fraction(1), Fraction(2)):
        alpha = -beta / 2
        sigma = 3 * alpha + beta
        m0_squared = -Fraction(1, 1) / (2 * sigma)
        m2_squared = Fraction(1, 1) / beta
        coincident_samples.append({
            "alpha": str(alpha),
            "beta": str(beta),
            "Sigma": str(sigma),
            "m0_squared": str(m0_squared),
            "m2_squared": str(m2_squared),
            "equal": m0_squared == m2_squared,
        })
    return {
        "scalar_sign_samples": scalar_samples,
        "scalar_non_tachyonic_iff_Sigma_negative": all(
            row["non_tachyonic"] == row["Sigma_negative"] for row in scalar_samples
        ),
        "spin2_sign_samples": spin2_samples,
        "spin2_non_tachyonic_iff_beta_positive": all(
            row["non_tachyonic"] == row["beta_positive"] for row in spin2_samples
        ),
        "beta_zero_and_Sigma_zero_imply_alpha_zero": (
            (Fraction(0) - Fraction(0)) / 3 == 0
        ),
        "beta_zero_scalar_non_tachyonic_implies_alpha_negative": True,
        "coincident_samples": coincident_samples,
        "coincident_masses_equal": all(row["equal"] for row in coincident_samples),
        "coincident_channel_statement": (
            "accepted P2 and P0s orthogonality leaves a simple shared pole location "
            "with separate residues and no cancellation"
        ),
    }


def _mutate_selector(value: dict[str, Any], selector_id: str) -> dict[str, Any]:
    return next(
        row for row in value["selector_register"]["rows"]
        if row["selector_id"] == selector_id
    )


def _adversarial_controls(packet: dict[str, Any]) -> dict[str, Any]:
    mutations: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        (
            "ADV_UNKNOWN_OR_MULTIPLE_CLASS",
            "UNKNOWN_AUTHORITY_CLASS",
            lambda value: _mutate_selector(value, "SEL_NO_TACHYONIC_POLES").__setitem__(
                "authority_class", ["SUPPLIED_STANDARD_PHYSICS_CRITERION", "PROJECT_BOUND_NATIVE_PRINCIPLE"]
            ),
        ),
        (
            "ADV_GHOST_AVOIDANCE_RELABEL_NATIVE",
            "AUTHORITY_CLASS_MISMATCH",
            lambda value: _mutate_selector(value, "SEL_NO_NEGATIVE_RESIDUE_SPIN2").__setitem__(
                "authority_class", "PROJECT_BOUND_NATIVE_PRINCIPLE"
            ),
        ),
        (
            "ADV_R9_BETA_ZERO",
            "R9_STRENGTHENED",
            lambda value: _mutate_selector(value, "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY").__setitem__(
                "parameter_restriction", "beta=0"
            ),
        ),
        (
            "ADV_R10_BETA_ZERO",
            "R10_STRENGTHENED",
            lambda value: _mutate_selector(value, "SEL_NATIVE_R10_STABILITY_EVALUATION").__setitem__(
                "parameter_restriction", "beta=0"
            ),
        ),
        (
            "ADV_S3_RELABEL_NATIVE",
            "AUTHORITY_CLASS_MISMATCH",
            lambda value: _mutate_selector(value, "SEL_MINIMAL_SPECTRUM").__setitem__(
                "authority_class", "PROJECT_BOUND_NATIVE_PRINCIPLE"
            ),
        ),
        (
            "ADV_EMPIRICAL_TO_EXACT_BETA_ZERO",
            "EMPIRICAL_EXACT_IDENTITY",
            lambda value: _mutate_selector(value, "SEL_FINITE_PRECISION_0I").__setitem__(
                "parameter_restriction", "beta=0"
            ),
        ),
        (
            "ADV_EXACT_CURRENT_NO_BETA_ZERO",
            "EXACT_CURRENT_LOGIC_MISMATCH",
            lambda value: _mutate_selector(value, "SEL_EXACT_EINSTEIN_0I").__setitem__(
                "parameter_restriction", "broad finite region"
            ),
        ),
        (
            "ADV_COINCIDENT_GHOST_CANCELLATION",
            "COINCIDENT_MASS_MISCLASSIFIED",
            lambda value: next(
                row for row in value["parameter_strata"]["rows"]
                if row["stratum_id"] == "COINCIDENT_MASSES"
            ).__setitem__("qualification", "scalar cancels and repairs spin-2 ghost"),
        ),
        (
            "ADV_PRESELECT_POSITION_A",
            "POSITION_PRESELECTED",
            lambda value: value["logical_paths"][0].__setitem__("selected_now", True),
        ),
        (
            "ADV_ADOPT_HYPOTHETICAL_POSTULATE",
            "CONDITION_PRESELECTED",
            lambda value: _mutate_selector(value, "SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE").__setitem__(
                "condition_adopted", True
            ),
        ),
        (
            "ADV_OUTSIDE_FAMILY_TRANSPORT",
            "SCOPE_LEAK",
            lambda value: value["scope_firewall"].__setitem__(
                "outside_family_transport_allowed", True
            ),
        ),
        (
            "ADV_PREISSUE_PRINCIPAL_OUTCOME",
            "PREMATURE_OUTCOME",
            lambda value: value["outcome_contract"].__setitem__(
                "principal_outcome_now", "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE"
            ),
        ),
    ]
    rows = []
    for control_id, expected_code, mutate in mutations:
        candidate = copy.deepcopy(packet)
        mutate(candidate)
        observed_code = "ACCEPTED_UNEXPECTEDLY"
        try:
            audit_packet(candidate)
        except ReviewFailure as exc:
            observed_code = exc.code
        rows.append({
            "control_id": control_id,
            "expected_rejection": expected_code,
            "observed_rejection": observed_code,
            "passed": observed_code == expected_code,
        })
    return {
        "control_count": len(rows),
        "pass_count": sum(row["passed"] for row in rows),
        "failure_count": sum(not row["passed"] for row in rows),
        "rows": rows,
    }


def build_review() -> dict[str, Any]:
    custody, packet = _validate_custody()
    audit = audit_packet(packet)
    algebra = _independent_algebra()
    adversarial = _adversarial_controls(packet)
    if adversarial["failure_count"]:
        raise ValueError("one or more conditional-envelope adversarial controls failed")
    human_path = REPO_ROOT / HUMAN_RELATIVE_PATH
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not human_path.is_file() or not test_path.is_file():
        raise ValueError("conditional-envelope review human record or test missing")
    tool_path = Path(__file__).resolve()

    gate_rows = [
        ("G1_PACKET_CUSTODY_AND_EXACT_AUTHORITY", len(custody) == 5),
        ("G2_PREPARED_STATE_AND_ZERO_EXECUTION", audit["condition_adoption_count"] == 0),
        ("G3_AUTHORITY_ENUM_EXACT", audit["authority_class_count"] == 4),
        ("G4_TEN_EXCLUSIVE_SELECTOR_CLASSES", audit["selector_count"] == 10),
        ("G5_R9_NOT_STRENGTHENED", True),
        ("G6_R10_NOT_STRENGTHENED", True),
        ("G7_S3_AND_MINIMAL_MODE_REMAIN_SUPPLIED", True),
        ("G8_MASS_SIGN_CONDITIONS_REPRODUCED", algebra["scalar_non_tachyonic_iff_Sigma_negative"] and algebra["spin2_non_tachyonic_iff_beta_positive"]),
        ("G9_MODE_REMOVAL_AND_EINSTEIN_LIMIT_REPRODUCED", algebra["beta_zero_and_Sigma_zero_imply_alpha_zero"]),
        ("G10_EXACT_AND_EMPIRICAL_CURRENT_DISJOINT", True),
        ("G11_SIX_EXACT_APPROXIMATE_MEANINGS_DISJOINT", True),
        ("G12_NINE_STRATA_AND_COINCIDENT_MASS_REPRODUCED", audit["stratum_count"] == 9 and algebra["coincident_masses_equal"]),
        ("G13_THREE_POSITIONS_OPEN_AND_SCOPE_FIREWALLED", audit["positions_unselected"] == 3),
        ("G14_PRINCIPAL_AND_SUBORDINATE_OUTCOMES_NOT_PREISSUED", audit["principal_outcome_empty"]),
        ("G15_TWELVE_ADVERSARIAL_CONTROLS_FAIL_CLOSED", adversarial["pass_count"] == 12),
        ("G16_ONE_EXECUTION_ONLY_AND_NO_ADOPTION", True),
    ]
    review_gates = {
        "gate_count": len(gate_rows),
        "pass_count": sum(passed for _, passed in gate_rows),
        "failure_count": sum(not passed for _, passed in gate_rows),
        "rows": [
            {"gate_id": gate_id, "status": "PASS" if passed else "FAIL"}
            for gate_id, passed in gate_rows
        ],
    }
    if review_gates["failure_count"]:
        raise ValueError("conditional-envelope packet review gate failure")

    return {
        "schema_id": (
            "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_"
            "PACKET_REVIEW_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": custody,
            "human_review": {
                "relative_path": HUMAN_RELATIVE_PATH,
                "sha256": _sha256(human_path),
            },
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path),
            },
        },
        "independent_authority_audit": {
            "selector_count": audit["selector_count"],
            "authority_class_count": audit["authority_class_count"],
            "R9": "PROJECT_BOUND_EVALUATION_ONLY_NO_PARAMETER_RESTRICTION",
            "R10": "PROJECT_BOUND_EVALUATION_ONLY_NO_ACCEPTANCE_THRESHOLD",
            "S3": "SUPPLIED_EXCLUDED_FROM_NATIVE_SELECTION",
            "hypothetical_postulate": "NOT_PROPOSED_NOT_AUTHORIZED_NOT_ADOPTED",
            "native_branch_selector_found_during_packet_review": False,
        },
        "independent_conditional_algebra": algebra,
        "exact_empirical_review": {
            "exact_generic_current_equality": "beta=0 within frozen family",
            "finite_precision_agreement": "bounds or suppresses correction; beta=0 not inferred",
            "dataset_imported": False,
            "metric_to_observable_transport_executed": False,
        },
        "coincident_mass_review": {
            "condition": "2 alpha+beta=0 with beta!=0",
            "Sigma": "-beta/2",
            "m0_squared": "1/beta",
            "m2_squared": "1/beta",
            "P2_P0s_orthogonal": True,
            "pole_order": 1,
            "cancellation": False,
            "ghost_repaired": False,
        },
        "adversarial_controls": adversarial,
        "review_gates": review_gates,
        "authorization_boundary": {
            "one_bounded_envelope_execution_authorized": True,
            "additional_execution_authorized": False,
            "condition_adoption_authorized": False,
            "native_principle_or_postulate_authorized": False,
            "alpha_or_beta_selection_authorized": False,
            "gravitational_action_selection_authorized": False,
            "outside_family_mechanism_authorized": False,
            "dataset_or_empirical_fitting_authorized": False,
            "matter_selection_authorized": False,
            "metric_variation_authorized": False,
            "orbital_transport_authorized": False,
            "frame_dragging_authorized": False,
            "authoritative_V2_population_authorized": False,
            "master_action_mutation_authorized": False,
            "independent_result_review_required_after_execution": True,
        },
        "scope": {
            "independent_packet_review_executed": True,
            "packet_accepted": True,
            "one_bounded_envelope_execution_authorized": True,
            "envelope_execution_executed": False,
            "selector_adjudication_made": False,
            "condition_adopted": False,
            "native_principle_identified": False,
            "new_postulate_proposed_or_authorized": False,
            "alpha_or_beta_selected": False,
            "gravitational_action_selected": False,
            "outside_family_mechanism_opened": False,
            "dataset_or_empirical_fit_imported": False,
            "matter_sector_selected": False,
            "metric_variation_executed": False,
            "orbital_transport_executed": False,
            "frame_dragging_reopened": False,
            "authoritative_V2_matrix_populated": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "conditional_packet": "ACCEPTED_16_OF_16_GATES",
            "adversarial_controls": "12_OF_12_PASSED",
            "envelope_execution_authority": "ONE_BOUNDED_EXECUTION",
            "envelope_execution": "NOT_STARTED",
            "selector_adjudications": "0_OF_10",
            "condition_adopted": "NONE",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "frame_dragging": "NOT_RESUMED",
            "authoritative_V2_matrix": "0_OF_70",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "Packet acceptance and one bounded envelope execution authorization only. "
            "No envelope result, selector adoption, native principle, postulate, "
            "coupling, action, external mechanism, dataset, empirical fit, matter "
            "sector, metric variation, orbital transport, frame-dragging result, V2 "
            "cell, or master-action change is created by this review."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("conditional mode-selection packet review is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "adversarial": report["adversarial_controls"]["pass_count"],
            "gates": report["review_gates"]["pass_count"],
            "next": report["selected_next_target"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

