from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_toe_expert_translation_bounded_target_selection_report import (
    DEFAULT_OUT as POST_TRANSLATION_SELECTION_PATH,
    SELECTED_NEXT_TARGET as PACKET_TARGET,
    SELECTION_ID as POST_TRANSLATION_SELECTION_ID,
)
from formal.python.tools.qft_gr_post_mr_assump004_governed_maturation_reports import (
    ACCEPTED_MR_ROWS,
    CAPTURED_AT_UTC,
    COMPLETED_FAMILIES_AFTER_MR,
    MINIMAL_MODEL_PATH,
    NONCLAIMS,
)


REPO_ROOT = find_repo_root(Path(__file__))

SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_20260610_v0"
PACKET_ID = "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_PREPARED_WITH_NO_"
    "SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_working_model_demonstration_packet_prepared_no_execution_"
    "source_admissibility_or_seam_closure"
)
REVIEW_TARGET = "review_qft_gr_minimal_working_model_demonstration_packet_result"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_DEMONSTRATION_PACKET_20260610_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required text file: {path}")
    return path.read_text(encoding="utf-8")


def _selected_targets(rows: list[dict[str, Any]]) -> list[str]:
    return [str(row["target"]) for row in rows if row.get("decision") == "selected"]


def build_packet(
    *,
    selection_path: Path = POST_TRANSLATION_SELECTION_PATH,
    minimal_model_path: Path = MINIMAL_MODEL_PATH,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selection = _read_json(selection_path)
    minimal_model = _read_text(minimal_model_path)
    candidate_next_targets = [
        {
            "target": REVIEW_TARGET,
            "decision": "selected",
            "reason": "Packet preparation must be result-reviewed before any model execution.",
        },
        {
            "target": "execute_qft_gr_minimal_working_model_demonstration",
            "decision": "not_authorized_until_packet_result_review",
            "reason": "This artifact prepares the packet only; it does not execute the model.",
        },
        {
            "target": "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized",
            "reason": "The packet defines an admissibility candidate only and does not open this family.",
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains outside this packet-preparation target.",
        },
        {
            "target": "claim_qft_gr_source_admissibility_or_seam_closure",
            "decision": "forbidden",
            "reason": "The packet does not construct a source-admissibility proof or close QFT-GR.",
        },
    ]
    selected_targets = _selected_targets(candidate_next_targets)
    acceptance_criteria = {
        "consumes_post_translation_selection": selection.get("selection_id")
        == POST_TRANSLATION_SELECTION_ID,
        "post_translation_selection_selected_packet": selection.get("selected_next_target")
        == PACKET_TARGET,
        "minimal_model_program_available": "QFT-GR Minimal Working Model Program v0"
        in minimal_model,
        "imports_completed_assumption_families": COMPLETED_FAMILIES_AFTER_MR
        == [
            "operator_domain_assumptions",
            "renormalization_assumptions",
            "state_domain_assumptions",
            "mathematical_regularity_assumptions",
        ],
        "imports_mathematical_regularity_rows": ACCEPTED_MR_ROWS
        == [
            "MR-ASSUMP-001-derivative_exchange_regular_boundary",
            "MR-ASSUMP-002-weak_strong_conservation_comparison_scope",
            "MR-ASSUMP-003-distributional_pairing_regular_domain",
            "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        ],
        "selects_exactly_one_next_target": selected_targets == [REVIEW_TARGET],
        "packet_preparation_only": True,
        "no_model_execution": True,
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_target": PACKET_TARGET,
        "consumes_post_translation_selection": selection.get("selection_id"),
        "consumes_post_translation_selection_pointer": _ptr(selection_path),
        "minimal_model_program_pointer": _ptr(minimal_model_path),
        "outcome_id": OUTCOME_ID,
        "packet_classification": PACKET_CLASSIFICATION,
        "claim_level": "Level 3 packet-preparation target",
        "claim_ceiling": "minimal working model demonstration packet only",
        "scientific_role": "prepare the first bounded toy-model source test",
        "minimal_model_scope": {
            "model_class": "free scalar-field stress-energy-like candidate",
            "scope": "fixed controlled background with no backreaction",
            "purpose": (
                "prepare a bounded demonstration question that may either produce "
                "a source-like candidate or expose a precise obstruction"
            ),
        },
        "toy_source_candidate": {
            "candidate": (
                "regularized or renormalized expectation of a stress-energy-like "
                "tensor for the simplified field/state setup"
            ),
            "status": "candidate_only_not_source_admissibility",
            "source_admissibility_claimed": False,
        },
        "simplified_field_state_setup": {
            "field_object": "real scalar field placeholder on the controlled background",
            "state_object": "bounded state or expectation functional placeholder",
            "expectation_object": "finite expectation candidate under imported domain conditions",
        },
        "background_geometry_assumptions": {
            "geometry": "fixed smooth or distributionally controlled background",
            "connection": "background-compatible derivative operator for weak tests",
            "exclusions": [
                "no backreaction",
                "no semiclassical Einstein equation",
                "no Bianchi compatibility claim",
            ],
        },
        "source_like_object_criteria": [
            "pairs with the selected distributional test domain",
            "is finite under the selected regularization or renormalization scope",
            "has indexed tensor-like slots suitable for later geometric source tests",
            "does not by itself imply physical source admissibility",
        ],
        "admissibility_candidate_only": {
            "candidate_definition": (
                "an object eligible for later source-admissibility review if weak "
                "conservation and domain compatibility tests are satisfied"
            ),
            "admissibility_claimed": False,
            "source_map_closure_claimed": False,
        },
        "imported_assumption_families": COMPLETED_FAMILIES_AFTER_MR,
        "imported_regularities": ACCEPTED_MR_ROWS,
        "conservation_test_target": {
            "target": "weak tested divergence vanishing or explicit obstruction",
            "test_form": (
                "evaluate the candidate against compactly supported test fields "
                "and record whether the weak conservation target is met"
            ),
            "conservation_proved": False,
            "conservation_witness_constructed": False,
        },
        "failure_modes": [
            "field/state setup cannot produce a finite expectation candidate",
            "regularization or renormalization scope is incompatible with the test domain",
            "distributional pairing fails",
            "derivative or limit-interchange assumptions remain insufficient in the model",
            "weak conservation test fails",
            "source-like object criteria fail",
            "the route requires a new exact missing condition family named by review",
            "countermodel or scope rewrite is required",
        ],
        "countermodel_hooks": [
            "QFT_GR_COUNTERMODEL_001_RESIDUAL_ZERO_NOT_ADMISSIBLE",
            "QFT_GR_COUNTERMODEL_002_EXPECTATION_NOT_CONSERVED",
            "QFT_GR_COUNTERMODEL_003_PAIRING_WITHOUT_DERIVATIVE_EXCHANGE",
        ],
        "falsifier_hooks": [
            "QFT-GR source admissibility falsifier",
            "QFT-GR weak/strong conservation falsifier",
            "QFT-GR derivative/limit interchange falsifier",
        ],
        "packet_preparation_only": True,
        "model_execution_authorized": False,
        "selected_next_target": REVIEW_TARGET,
        "candidate_next_targets": candidate_next_targets,
        "selection_count": len(selected_targets),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def write_report(path: Path = DEFAULT_OUT) -> dict[str, Any]:
    payload = build_packet()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the QFT-GR minimal working model demonstration packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    payload = write_report(args.out)
    print(
        "qft_gr_minimal_working_model_demonstration_packet_report: "
        f"selected={payload['selected_next_target']} out={_ptr(args.out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
