from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_toe_matter_sector_candidate_selection_packet_report import (
    DEFAULT_OUT as TOE_MATTER_SELECTION_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_TOE_MATTER_SELECTION_OUTCOME,
    REAL_SCALAR_ACTION_FORM,
    SCHEMA_ID as EXPECTED_TOE_MATTER_SELECTION_SCHEMA_ID,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_KNOWN_MATTER_MODEL,
    SELECTED_LAGRANGIAN_DENSITY,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    TOE_NATIVE_MATTER_SECTOR_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_ACTION_DERIVABILITY_RETRY_WITH_PROVISIONAL_MATTER_SECTOR_"
    "20260616_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_ACTION_DERIVABILITY_RETRY_WITH_PROVISIONAL_MATTER_SECTOR_v0"
ACTION_DERIVABILITY_RESULT = (
    "ACTION_DERIVABILITY_CONSTRUCTED_FOR_PROVISIONAL_REAL_SCALAR_TEST_SECTOR_"
    "NO_TOE_NATIVE_MATTER_DERIVATION"
)
OUTCOME_ID = (
    "QFT_GR_ACTION_DERIVABILITY_RETRY_WITH_PROVISIONAL_MATTER_SECTOR_"
    "PREPARED_WITH_ACTION_DERIVABILITY_CONSTRUCTED_FOR_PROVISIONAL_REAL_"
    "SCALAR_TEST_SECTOR_NO_TOE_NATIVE_MATTER_DERIVATION_AND_NO_SOURCE_"
    "ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_action_derivability_retry_with_provisional_matter_sector_constructs_"
    "scalar_stress_energy_variation_nonpromotionally"
)
NEXT_TARGET = "prepare_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source"
NEXT_TARGET_KIND = (
    "qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_"
    "preparation"
)
AUTHORIZED_BY_TOE_MATTER_SELECTION_COMMIT = "80a73e37"

METRIC_VARIATION_CONVENTION = (
    "Vary the inverse metric with compactly supported symmetric contravariant "
    "test k^{mu nu} = delta g^{mu nu}, hold phi fixed, and use "
    "delta(dVol_g) = -1/2 g_{mu nu} k^{mu nu} dVol_g."
)
SCALAR_ACTION = REAL_SCALAR_ACTION_FORM
SCALAR_LAGRANGIAN = SELECTED_LAGRANGIAN_DENSITY
STRESS_ENERGY_COVARIANT_EXPRESSION = (
    "T_{mu nu} = partial_mu phi partial_nu phi - 1/2 g_{mu nu} "
    "g^{alpha beta} partial_alpha phi partial_beta phi - g_{mu nu} V(phi)"
)
STRESS_ENERGY_CONTRAVARIANT_EXPRESSION = (
    "T^{mu nu} = g^{mu alpha} g^{nu beta} T_{alpha beta}"
)
COVARIANT_VARIATION_FORM = (
    "delta S_m[g, phi](k) = -1/2 integral_M T_{mu nu} k^{mu nu} dVol_g"
)
PRIOR_CONTRACT_PAIRING_FORM = (
    "<T, h> = integral_M T^{mu nu} h_{mu nu} dVol_g"
)
INDEX_BRIDGE = (
    "For the prior covariant test convention h_{mu nu}, set "
    "T^{mu nu} = g^{mu alpha} g^{nu beta} T_{alpha beta}; equivalently "
    "h_{mu nu} = g_{mu alpha} g_{nu beta} k^{alpha beta} maps the inverse-metric "
    "variation k^{alpha beta} into the covariant-test pairing."
)
WEAK_PAIRING_TRANSLATION = (
    COVARIANT_VARIATION_FORM
    + "; "
    + PRIOR_CONTRACT_PAIRING_FORM
    + " after raising the scalar stress-energy indices."
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_ACTION_DERIVABILITY_RETRY_WITH_PROVISIONAL_MATTER_SECTOR_"
    "20260616_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRActionDerivabilityRetryWithProvisionalMatterSector.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _derivation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "state_action",
            "mathematical_content": SCALAR_ACTION,
            "claim": "scalar action stated for provisional calculation sandbox",
        },
        {
            "step_id": "state_variation_convention",
            "mathematical_content": METRIC_VARIATION_CONVENTION,
            "claim": "inverse-metric variation convention fixed",
        },
        {
            "step_id": "vary_lagrangian",
            "mathematical_content": (
                "delta L_m = -1/2 partial_mu phi partial_nu phi k^{mu nu}"
            ),
            "claim": "field phi held fixed under metric variation",
        },
        {
            "step_id": "vary_volume",
            "mathematical_content": (
                "delta(dVol_g) = -1/2 g_{mu nu} k^{mu nu} dVol_g"
            ),
            "claim": "inverse-metric volume variation contribution recorded",
        },
        {
            "step_id": "combine_variation",
            "mathematical_content": COVARIANT_VARIATION_FORM,
            "claim": "weak variational action-derivability form constructed",
        },
        {
            "step_id": "read_stress_energy",
            "mathematical_content": STRESS_ENERGY_COVARIANT_EXPRESSION,
            "claim": "covariant scalar stress-energy expression recorded",
        },
        {
            "step_id": "translate_to_prior_pairing",
            "mathematical_content": WEAK_PAIRING_TRANSLATION,
            "claim": "pairing convention made explicit",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_action_derivability_retry_with_provisional_matter_sector",
        "bounded_focused_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "release_index_path_not_freshly_lean_validated": True,
    }


def build_qft_gr_action_derivability_retry_with_provisional_matter_sector(
    *,
    toe_matter_selection_packet_path: Path = TOE_MATTER_SELECTION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selection_packet = _read_json(toe_matter_selection_packet_path)
    derivation_steps = _derivation_steps()
    acceptance_criteria = {
        "consumes_expected_toe_matter_selection_packet": (
            selection_packet.get("schema_id") == EXPECTED_TOE_MATTER_SELECTION_SCHEMA_ID
            and selection_packet.get("outcome_id") == EXPECTED_TOE_MATTER_SELECTION_OUTCOME
            and selection_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "provisional_real_scalar_sector_selected": (
            selection_packet.get("selected_provisional_matter_sector_id")
            == SELECTED_PROVISIONAL_MATTER_SECTOR_ID
            and selection_packet.get("known_matter_model_imported_as_provisional_test_sector")
            is True
        ),
        "scalar_action_stated": SCALAR_ACTION == REAL_SCALAR_ACTION_FORM,
        "field_content_stated": SELECTED_FIELD_CONTENT == "real scalar field phi",
        "lagrangian_stated": SCALAR_LAGRANGIAN == SELECTED_LAGRANGIAN_DENSITY,
        "metric_variation_convention_stated": "inverse metric" in METRIC_VARIATION_CONVENTION,
        "stress_energy_expression_recorded": "T_{mu nu}" in STRESS_ENERGY_COVARIANT_EXPRESSION,
        "weak_pairing_translation_stated": (
            COVARIANT_VARIATION_FORM in WEAK_PAIRING_TRANSLATION
            and PRIOR_CONTRACT_PAIRING_FORM in WEAK_PAIRING_TRANSLATION
        ),
        "toe_native_matter_derivation_false": (
            selection_packet.get("toe_native_matter_sector_defined") is False
            and selection_packet.get("toe_matter_model_derived") is False
        ),
        "arbitrary_distributional_source_not_promoted": (
            selection_packet.get("arbitrary_distributional_source_action_derived_claimed")
            is False
        ),
        "source_admissibility_not_claimed": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_ACTION_DERIVABILITY_RETRY_WITH_PROVISIONAL_MATTER_SECTOR"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_ACTION_DERIVABILITY_RETRY_WITH_PROVISIONAL_MATTER_SECTOR_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_toe_matter_selection_artifact_id": selection_packet.get("schema_id"),
        "authorized_by_toe_matter_selection_commit": (
            AUTHORIZED_BY_TOE_MATTER_SELECTION_COMMIT
        ),
        "action_derivability_result": ACTION_DERIVABILITY_RESULT,
        "selected_provisional_matter_sector_id": SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        "selected_known_matter_model": SELECTED_KNOWN_MATTER_MODEL,
        "selected_action_generated_source_subclass_id": (
            SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
        ),
        "field_content": SELECTED_FIELD_CONTENT,
        "scalar_action": SCALAR_ACTION,
        "lagrangian_density": SCALAR_LAGRANGIAN,
        "metric_variation_convention": METRIC_VARIATION_CONVENTION,
        "variation_variable": "k^{mu nu} = delta g^{mu nu}",
        "field_variation_policy": "phi is held fixed during metric variation",
        "stress_energy_covariant_expression": STRESS_ENERGY_COVARIANT_EXPRESSION,
        "stress_energy_contravariant_expression": STRESS_ENERGY_CONTRAVARIANT_EXPRESSION,
        "covariant_variation_form": COVARIANT_VARIATION_FORM,
        "prior_contract_pairing_form": PRIOR_CONTRACT_PAIRING_FORM,
        "index_bridge": INDEX_BRIDGE,
        "weak_pairing_translation": WEAK_PAIRING_TRANSLATION,
        "derivation_steps": derivation_steps,
        "action_derivability_constructed": True,
        "action_derivability_constructed_scope": (
            "provisional real-scalar calculation sandbox only"
        ),
        "toe_native_matter_sector_result": TOE_NATIVE_MATTER_SECTOR_RESULT,
        "toe_native_matter_sector_defined": False,
        "toe_matter_model_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "arbitrary_distributional_source_action_derived_claimed": False,
        "arbitrary_distributional_source_promoted": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "weak_conservation_claimed": False,
        "conservation_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "downstream_progression": [
            {
                "stage": "action_derivability_retry",
                "status": "CONSTRUCTED_FOR_PROVISIONAL_SCALAR_TEST_SECTOR",
                "decision": ACTION_DERIVABILITY_RESULT,
                "reason": "Metric variation of the provisional scalar action yields the scalar stress-energy expression.",
            },
            {
                "stage": "weak_pairing_translation",
                "status": "CONSTRUCTED_WITH_INDEX_CONVENTION",
                "decision": "covariant_variation_and_prior_pairing_conventions_linked",
                "reason": "The packet distinguishes inverse-metric variation k^{mu nu} from covariant test tensors h_{mu nu}.",
            },
            {
                "stage": "weak_conservation",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": "Conservation must be tested separately, likely using the scalar field equation.",
            },
            {
                "stage": "bianchi_compatibility",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Bianchi compatibility remains downstream of weak conservation.",
            },
            {
                "stage": "semiclassical_source_admissibility",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Semiclassical coupling remains downstream of source-admissibility checks.",
            },
        ],
        "mathematical_statement": (
            "For the provisional scalar sandbox S_m[g, phi] = integral_M "
            "[-1/2 g^{mu nu} partial_mu phi partial_nu phi - V(phi)] dVol_g, "
            "inverse-metric variation with phi fixed gives "
            + COVARIANT_VARIATION_FORM
            + " where "
            + STRESS_ENERGY_COVARIANT_EXPRESSION
            + ". This constructs action derivability only for the provisional "
            "scalar stress-energy subclass and does not derive the ToE-native "
            "matter sector."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet constructs action derivability only for the imported "
            "provisional real-scalar calculation sandbox. It does not derive a "
            "ToE-native matter sector, does not prove an arbitrary "
            "distributional source is action-derived, and does not claim source "
            "admissibility, conservation, Bianchi compatibility, semiclassical "
            "coupling, QFT-GR closure, empirical validation, public submission, "
            "or master-action promotion."
        ),
    }


def write_qft_gr_action_derivability_retry_with_provisional_matter_sector(
    *,
    toe_matter_selection_packet_path: Path = TOE_MATTER_SELECTION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_action_derivability_retry_with_provisional_matter_sector(
        toe_matter_selection_packet_path=toe_matter_selection_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR action-derivability retry packet for the "
            "provisional matter sector."
        )
    )
    parser.add_argument(
        "--toe-matter-selection-packet",
        type=Path,
        default=TOE_MATTER_SELECTION_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    toe_matter_selection_packet_path = (
        ns.toe_matter_selection_packet
        if ns.toe_matter_selection_packet.is_absolute()
        else (REPO_ROOT / ns.toe_matter_selection_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_action_derivability_retry_with_provisional_matter_sector(
        toe_matter_selection_packet_path=toe_matter_selection_packet_path,
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
                "action_derivability_result": payload["action_derivability_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
