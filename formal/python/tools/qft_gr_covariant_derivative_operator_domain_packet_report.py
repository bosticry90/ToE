from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_obstruction_refinement_packet_report import (
    DEFAULT_OUT as DEFAULT_REFINEMENT_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_REFINEMENT_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_REFINEMENT_CLASSIFICATION,
    PACKET_ID as EXPECTED_REFINEMENT_PACKET_ID,
    PRIMARY_MISSING_CONDITION,
    SCHEMA_ID as EXPECTED_REFINEMENT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_derivative_operator_domain_packet_prepared_no_"
    "conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "review_qft_gr_covariant_derivative_operator_domain_packet_result"
SCIENTIFIC_QUESTION = (
    "What covariant derivative/operator-domain structure is required before "
    "the repo can even formulate or attempt the QFT-GR stress-energy "
    "conservation witness?"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _domain_requirements() -> list[dict[str, str]]:
    rows = [
        (
            "connection_or_derivative_operator",
            "select the covariant derivative or divergence operator used by the conservation statement",
            "formal operator symbol and action surface for the candidate tensor/source object",
            "without an operator, divergence-zero is not a defined proposition",
        ),
        (
            "operator_domain",
            "specify the bounded domain on which the operator may act",
            "domain predicate covering the candidate renormalized stress-energy expectation",
            "without a domain, the conservation statement may be ill-typed or overbroad",
        ),
        (
            "candidate_source_codomain",
            "fix the tensor/source codomain expected of the renormalized stress-energy object",
            "source-object type or structure compatible with the selected derivative",
            "without codomain structure, source admissibility remains unstated",
        ),
        (
            "regularity_or_distributional_scope",
            "separate strong smooth/tensor conservation from weak or distributional conservation",
            "regularity or test-function scope sufficient for the selected form",
            "weak-vs-strong ambiguity blocks later proof checking",
        ),
        (
            "state_expectation_domain_link",
            "bind the renormalized expectation/state domain to the operator domain",
            "bridge obligation connecting expectation semantics to the derivative domain",
            "the operator may not apply to the candidate expectation",
        ),
        (
            "metric_or_background_scope",
            "state the metric/background structure required to define the covariant derivative",
            "bounded background assumptions under which the derivative is meaningful",
            "the conservation operator lacks geometric semantics",
        ),
    ]
    return [
        {
            "requirement_id": row[0],
            "required_structure": row[1],
            "required_future_surface": row[2],
            "failure_mode_if_missing": row[3],
            "claim_ceiling": "operator_domain_packet_only_no_conservation_witness",
        }
        for row in rows
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The operator-domain packet must be reviewed before a conservation statement packet can use it.",
        },
        {
            "target": "prepare_qft_gr_covariant_conservation_statement_with_operator_domain_packet",
            "decision": "deferred",
            "reason": "Statement preparation requires acceptance of this operator-domain packet.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Expectation-domain refinement may follow after the operator-domain review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Operator-domain packet preparation does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this packet.",
        },
    ]


def build_qft_gr_covariant_derivative_operator_domain_packet(
    *,
    refinement_path: Path = DEFAULT_REFINEMENT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    refinement = _read_json(refinement_path)
    requirements = _domain_requirements()
    candidate_next_targets = _candidate_next_targets()
    acceptance_criteria = {
        "consumes_expected_refinement_packet": refinement.get("packet_id")
        == EXPECTED_REFINEMENT_PACKET_ID,
        "refinement_schema_expected": refinement.get("schema_id")
        == EXPECTED_REFINEMENT_SCHEMA_ID,
        "refinement_outcome_expected": refinement.get("outcome_id")
        == EXPECTED_REFINEMENT_OUTCOME,
        "refinement_classification_expected": refinement.get("packet_classification")
        == EXPECTED_REFINEMENT_CLASSIFICATION,
        "refinement_selected_this_packet": refinement.get("selected_next_target")
        == CONSUMED_TARGET,
        "primary_blocker_preserved": refinement.get("primary_missing_condition")
        == PRIMARY_MISSING_CONDITION,
        "operator_domain_requirements_complete": len(requirements) == 6
        and all(
            {
                "requirement_id",
                "required_structure",
                "required_future_surface",
                "failure_mode_if_missing",
                "claim_ceiling",
            }
            <= set(row)
            for row in requirements
        ),
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
        else "QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_conservation_statement_obstruction_refinement_packet": EXPECTED_REFINEMENT_PACKET_ID,
        "consumes_qft_gr_covariant_conservation_statement_obstruction_refinement_packet_pointer": _ptr(
            refinement_path
        ),
        "primary_blocker": PRIMARY_MISSING_CONDITION,
        "scientific_question": SCIENTIFIC_QUESTION,
        "operator_domain_structure_prepared": prepared,
        "operator_domain_requirements": requirements,
        "operator_domain_requirement_count": len(requirements),
        "covariant_conservation_statement_formulated": False,
        "covariant_conservation_statement_attempted": False,
        "covariant_conservation_statement_witness_constructed": False,
        "conservation_witness_constructed": False,
        "stress_energy_source_admissibility_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "qft_gr_seam_closed": False,
        "semiclassical_einstein_equation_derived": False,
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
        else "REMEDIATE_QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET",
        "selected_next_target_kind": "qft_gr_covariant_derivative_operator_domain_packet_result_review",
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_RESULT_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only the covariant derivative/operator-domain "
            "structure required to formulate a later conservation witness. It "
            "does not formulate or prove conservation, construct a witness, "
            "claim stress-energy source admissibility or Bianchi compatibility, "
            "derive the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_covariant_derivative_operator_domain_packet(
    *,
    refinement_path: Path = DEFAULT_REFINEMENT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_derivative_operator_domain_packet(
        refinement_path=refinement_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant derivative/operator-domain packet."
    )
    parser.add_argument("--refinement", type=Path, default=DEFAULT_REFINEMENT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    refinement_path = (
        ns.refinement if ns.refinement.is_absolute() else (REPO_ROOT / ns.refinement)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_derivative_operator_domain_packet(
        refinement_path=refinement_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_derivative_operator_domain_packet_report: "
        f"prepared={payload['prepared']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
