from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_covariant_derivative_operator_domain_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_OPERATOR_DOMAIN_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_OPERATOR_DOMAIN_REVIEW_OUTCOME,
    PRIMARY_BLOCKER,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_OPERATOR_DOMAIN_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_OPERATOR_DOMAIN_REVIEW_ID,
    SCHEMA_ID as EXPECTED_OPERATOR_DOMAIN_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_conservation_statement_with_operator_domain_packet_prepared_"
    "no_conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "review_qft_gr_covariant_conservation_statement_with_operator_domain_packet_result"
SCIENTIFIC_QUESTION = (
    "Given the prepared covariant derivative/operator-domain structure, can "
    "the repo formulate a bounded covariant conservation statement for the "
    "candidate QFT-GR stress-energy source?"
)
STATEMENT_FORM = (
    "bounded_covariant_divergence_zero_statement_for_candidate_renormalized_"
    "stress_energy_source_on_prepared_operator_domain"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _statement_components() -> list[dict[str, str]]:
    rows = [
        (
            "candidate_stress_energy_source",
            "candidate renormalized QFT stress-energy expectation/source object",
            "object must lie in the prepared source codomain",
        ),
        (
            "covariant_derivative_operator",
            "operator selected by the operator-domain packet",
            "operator use remains bounded to the prepared metric/background scope",
        ),
        (
            "operator_domain",
            "domain on which the derivative/divergence is meaningful",
            "domain membership is prerequisite, not proof of conservation",
        ),
        (
            "conservation_form",
            "covariant divergence-zero statement on the bounded domain",
            "statement may later be refined into strong or weak/distributional form",
        ),
        (
            "source_admissibility_link",
            "later bridge from conservation statement to GR-source admissibility",
            "link is recorded as dependency only; admissibility is not claimed",
        ),
        (
            "bianchi_compatibility_link",
            "later bridge from conservation statement to Bianchi compatibility",
            "link is recorded as dependency only; compatibility is not claimed",
        ),
    ]
    return [
        {
            "component_id": row[0],
            "prepared_statement_role": row[1],
            "bounded_condition": row[2],
            "claim_ceiling": "statement_packet_only_no_conservation_witness",
        }
        for row in rows
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The formulated statement packet must be reviewed before any bounded witness attempt.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_statement_with_operator_domain_attempt",
            "decision": "deferred",
            "reason": "Execution requires a later statement-packet result review.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Expectation-domain refinement is not selected by this statement-preparation packet.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Statement preparation does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this packet.",
        },
    ]


def build_qft_gr_covariant_conservation_statement_with_operator_domain_packet(
    *,
    operator_domain_review_path: Path = DEFAULT_OPERATOR_DOMAIN_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(operator_domain_review_path)
    components = _statement_components()
    candidate_next_targets = _candidate_next_targets()
    acceptance_criteria = {
        "consumes_expected_operator_domain_review": review.get("review_id")
        == EXPECTED_OPERATOR_DOMAIN_REVIEW_ID,
        "operator_domain_review_schema_expected": review.get("schema_id")
        == EXPECTED_OPERATOR_DOMAIN_REVIEW_SCHEMA_ID,
        "operator_domain_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_OPERATOR_DOMAIN_REVIEW_OUTCOME,
        "operator_domain_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_OPERATOR_DOMAIN_REVIEW_CLASSIFICATION,
        "operator_domain_review_selected_this_packet": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "primary_blocker_addressed_at_preparation_level": review.get(
            "primary_blocker"
        )
        == PRIMARY_BLOCKER
        and review.get("operator_domain_preparation_only_confirmed") is True,
        "statement_components_complete": len(components) == 6
        and all(
            {
                "component_id",
                "prepared_statement_role",
                "bounded_condition",
                "claim_ceiling",
            }
            <= set(row)
            for row in components
        ),
        "no_conservation_witness_constructed": review.get(
            "conservation_witness_constructed"
        )
        is False
        and review.get("covariant_conservation_statement_witness_constructed")
        is False,
        "no_source_or_bianchi_claim": review.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and review.get("Bianchi_compatibility_claimed") is False,
        "no_einstein_or_qft_gr_closure": review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False
        and review.get("qft_gr_seam_closed") is False,
        "no_empirical_master_release_or_public_submission": review.get(
            "empirical_validation_claimed"
        )
        is False
        and review.get("master_action_promoted") is False
        and review.get("release_assembly_authorized") is False
        and review.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    prepared = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_derivative_operator_domain_packet_result_review": EXPECTED_OPERATOR_DOMAIN_REVIEW_ID,
        "consumes_qft_gr_covariant_derivative_operator_domain_packet_result_review_pointer": _ptr(
            operator_domain_review_path
        ),
        "consumed_operator_domain_review_outcome_id": review.get("outcome_id"),
        "consumed_operator_domain_review_classification": review.get(
            "result_review_classification"
        ),
        "primary_blocker": PRIMARY_BLOCKER,
        "primary_blocker_addressed_at_preparation_level": True,
        "scientific_question": SCIENTIFIC_QUESTION,
        "covariant_conservation_statement_form": STATEMENT_FORM,
        "statement_components": components,
        "statement_component_count": len(components),
        "covariant_conservation_statement_prepared": prepared,
        "covariant_conservation_statement_formulated": prepared,
        "covariant_conservation_statement_attempted": False,
        "covariant_conservation_statement_proved": False,
        "covariant_conservation_statement_witness_constructed": False,
        "conservation_witness_constructed": False,
        "stress_energy_source_admissibility_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_statement_with_operator_domain_packet_result_review"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_RESULT_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares and formulates only a bounded covariant "
            "conservation statement under the accepted operator-domain "
            "preparation. It does not prove conservation, construct a witness, "
            "claim stress-energy source admissibility or Bianchi compatibility, "
            "derive the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_statement_with_operator_domain_packet(
    *,
    operator_domain_review_path: Path = DEFAULT_OPERATOR_DOMAIN_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_statement_with_operator_domain_packet(
        operator_domain_review_path=operator_domain_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation statement with operator-domain packet."
    )
    parser.add_argument(
        "--operator-domain-review",
        type=Path,
        default=DEFAULT_OPERATOR_DOMAIN_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    operator_domain_review_path = (
        ns.operator_domain_review
        if ns.operator_domain_review.is_absolute()
        else (REPO_ROOT / ns.operator_domain_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_statement_with_operator_domain_packet(
        operator_domain_review_path=operator_domain_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_statement_with_operator_domain_packet_report: "
        f"prepared={payload['prepared']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
