from __future__ import annotations

"""Narrow v2 successor for the reconciliation decision contract.

V2 reuses the two v1 historical reductions and frozen classifier logic.  It
adds only explicit rankings, role-winner gates, exhaustive ULP bins, and the
two-valued terminal classification.  Actual payload access remains blocked
until an independent v2 packet-review anchor accepts the exact source bytes.
"""

import hashlib
import json
import math
from collections import OrderedDict
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any, NoReturn

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v1
    as predecessor_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as raw_v3,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_v2"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_v2.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_20260716_v2.json"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_REVIEW_20260716_v2.json"
)
RESULT_OUTPUT_ROOT_RELATIVE_PATH = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_observable_"
    "semantics_reconciliation_v2"
)
RESULT_RELATIVE_PATH = f"{RESULT_OUTPUT_ROOT_RELATIVE_PATH}/RECONCILIATION-RESULT.json"
EXPECTED_REVIEW_VERDICT = "ACCEPT_OBSERVABLE_SEMANTICS_RECONCILIATION_PACKET_V2"
EXPECTED_REVIEW_NEXT_TARGET = (
    "calculate_dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_v2_once"
)
EXPECTED_PREDECESSOR_TOOL_SHA256 = (
    "a907de5c2ae9a278da78f24f352281fd1e5b14533106dfcfd14138dbf9dd4f0a"
)
EXPECTED_V1_REVIEW_SHA256 = (
    "4507b60f85572b212a341367fdc6331fd100bbbdd5fda16aba27a8002f15579c"
)
V1_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_REVIEW_20260716_v1.json"
)
EXPECTED_SOURCE_OUTPUT_TREE_SHA256 = predecessor_v1.EXPECTED_SOURCE_OUTPUT_TREE_SHA256
EXPECTED_FIELD_COUNT = 1792
EXPECTED_RECORD_COUNT = 224
EXPECTED_ROLE_COUNT = 3
TERMINAL_PREDICATE_INVARIANT = "PREDICATE_INVARIANT"
TERMINAL_DECISION_INSTABILITY = "BLOCKED_OBSERVABLE_DECISION_INSTABILITY"
TERMINAL_CLASSIFICATIONS = (
    TERMINAL_PREDICATE_INVARIANT,
    TERMINAL_DECISION_INSTABILITY,
)
INVARIANCE_GATE_IDS = (
    "per_record_winners_identical",
    "role_winners_identical",
    "decision_relevant_orderings_identical",
    "threshold_decisions_identical",
    "hypothesis_predicates_identical",
    "supported_mechanism_sets_identical",
    "candidate_aggregate_results_identical",
)


class ReconciliationV2Error(RuntimeError):
    def __init__(self, diagnostic: str, detail: str = "") -> None:
        self.diagnostic = diagnostic
        self.detail = detail
        super().__init__(f"{diagnostic}: {detail}" if detail else diagnostic)


def _fail(diagnostic: str, detail: str = "") -> NoReturn:
    raise ReconciliationV2Error(diagnostic, detail)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _load_json(path: Path, diagnostic: str) -> dict[str, Any]:
    if not path.is_file():
        _fail(diagnostic, path.as_posix())
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        _fail(diagnostic, f"{type(error).__name__}:{error}")
    if not isinstance(value, dict):
        _fail(diagnostic, "expected JSON object")
    return value


def ordered_ranking(share_by_block: Mapping[str, Any]) -> list[list[str]]:
    """Return descending exact-tie groups in the frozen eight-block order.

    Ranking compares the derived binary64 share values.  Numeric equality forms
    an exact tie; +0.0 and -0.0 are equal for ranking.  Tie members retain the
    frozen block order, which is representation only and does not break the tie.
    """

    if set(share_by_block) != set(raw_v3.BLOCK_IDS):
        raise ValueError("ranking input must contain exactly eight frozen blocks")
    order_index = {block_id: index for index, block_id in enumerate(raw_v3.BLOCK_IDS)}
    values: dict[str, float] = {}
    for block_id in raw_v3.BLOCK_IDS:
        value = float(share_by_block[block_id])
        if not math.isfinite(value) or value < 0.0 or value > 1.0:
            raise ValueError(f"INVALID_RANKING_SHARE:{block_id}")
        values[block_id] = 0.0 if value == 0.0 else value
    sorted_ids = sorted(
        raw_v3.BLOCK_IDS,
        key=lambda block_id: (-values[block_id], order_index[block_id]),
    )
    groups: list[list[str]] = []
    for block_id in sorted_ids:
        if not groups or values[groups[-1][0]] != values[block_id]:
            groups.append([block_id])
        else:
            groups[-1].append(block_id)
    return groups


def ulp_histogram(field_rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    bins = {
        "exact_matches": 0,
        "one_ulp_differences": 0,
        "two_ulp_differences": 0,
        "greater_than_two_ulp_differences": 0,
    }
    for row in field_rows:
        distance = row.get("ulp_distance")
        if isinstance(distance, bool) or not isinstance(distance, int) or distance < 0:
            raise ValueError("ULP_DISTANCE_INVALID")
        if distance == 0:
            bins["exact_matches"] += 1
        elif distance == 1:
            bins["one_ulp_differences"] += 1
        elif distance == 2:
            bins["two_ulp_differences"] += 1
        else:
            bins["greater_than_two_ulp_differences"] += 1
    if sum(bins.values()) != len(field_rows):
        raise ValueError("ULP_HISTOGRAM_NOT_EXHAUSTIVE")
    return bins


def compare_record_rankings(
    field_rows: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    grouped: OrderedDict[tuple[Any, ...], list[Mapping[str, Any]]] = OrderedDict()
    for row in field_rows:
        identity = (
            row.get("run_id"),
            row.get("event_family"),
            row.get("step"),
            row.get("iteration"),
        )
        grouped.setdefault(identity, []).append(row)
    comparisons = []
    for identity, rows in grouped.items():
        if len(rows) != len(raw_v3.BLOCK_IDS) or {
            row.get("block_id") for row in rows
        } != set(raw_v3.BLOCK_IDS):
            raise ValueError("RECORD_BLOCK_IDENTITY_CLOSURE_MISMATCH")
        by_block = {str(row["block_id"]): row for row in rows}
        producer = {
            block_id: float(by_block[block_id]["producer_share"])
            for block_id in raw_v3.BLOCK_IDS
        }
        verifier = {
            block_id: float(by_block[block_id]["verifier_share"])
            for block_id in raw_v3.BLOCK_IDS
        }
        producer_ranking = ordered_ranking(producer)
        verifier_ranking = ordered_ranking(verifier)
        comparisons.append(
            {
                "run_id": identity[0],
                "event_family": identity[1],
                "step": identity[2],
                "iteration": identity[3],
                "producer_ranking": producer_ranking,
                "verifier_ranking": verifier_ranking,
                "producer_winner_group": producer_ranking[0],
                "verifier_winner_group": verifier_ranking[0],
                "winner_changed": producer_ranking[0] != verifier_ranking[0],
                "ordering_changed": producer_ranking != verifier_ranking,
            }
        )
    return {
        "record_count": len(comparisons),
        "per_record_winner_change_count": sum(
            row["winner_changed"] for row in comparisons
        ),
        "per_record_ordering_change_count": sum(
            row["ordering_changed"] for row in comparisons
        ),
        "records": comparisons,
    }


def compare_role_rankings(
    producer_metrics: Mapping[str, Any], verifier_metrics: Mapping[str, Any]
) -> dict[str, Any]:
    if set(producer_metrics) != set(verifier_metrics) or len(producer_metrics) != 3:
        raise ValueError("ROLE_METRIC_IDENTITY_CLOSURE_MISMATCH")
    comparisons = []
    for role_id in sorted(producer_metrics):
        producer = producer_metrics[role_id]
        verifier = verifier_metrics[role_id]
        if not isinstance(producer, Mapping) or not isinstance(verifier, Mapping):
            raise ValueError("ROLE_METRIC_SCHEMA_INVALID")
        producer_winner = str(producer.get("dominant_block_id"))
        verifier_winner = str(verifier.get("dominant_block_id"))
        if producer_winner not in raw_v3.BLOCK_IDS or verifier_winner not in raw_v3.BLOCK_IDS:
            raise ValueError("ROLE_DOMINANT_BLOCK_ID_INVALID")
        producer_shares = producer.get("median_share_by_block")
        verifier_shares = verifier.get("median_share_by_block")
        if not isinstance(producer_shares, Mapping) or not isinstance(
            verifier_shares, Mapping
        ):
            raise ValueError("ROLE_MEDIAN_SHARE_MAPPING_MISSING")
        producer_ranking = ordered_ranking(producer_shares)
        verifier_ranking = ordered_ranking(verifier_shares)
        if producer_winner not in producer_ranking[0] or verifier_winner not in verifier_ranking[0]:
            raise ValueError("ROLE_WINNER_AND_RANKING_INCONSISTENT")
        comparisons.append(
            {
                "role_id": role_id,
                "numpy_role_dominant_block": producer_winner,
                "python_role_dominant_block": verifier_winner,
                "role_dominant_block_changed": producer_winner != verifier_winner,
                "producer_role_ranking": producer_ranking,
                "verifier_role_ranking": verifier_ranking,
                "role_ordering_changed": producer_ranking != verifier_ranking,
            }
        )
    return {
        "role_count": len(comparisons),
        "role_level_dominant_block_change_count": sum(
            row["role_dominant_block_changed"] for row in comparisons
        ),
        "role_ordering_change_count": sum(
            row["role_ordering_changed"] for row in comparisons
        ),
        "roles": comparisons,
    }


def terminal_classification(gates: Mapping[str, Any]) -> str:
    if set(gates) != set(INVARIANCE_GATE_IDS):
        raise ValueError("INVARIANCE_GATE_CLOSURE_MISMATCH")
    if any(type(gates[gate_id]) is not bool for gate_id in INVARIANCE_GATE_IDS):
        raise ValueError("INVARIANCE_GATE_NOT_BOOLEAN")
    return (
        TERMINAL_PREDICATE_INVARIANT
        if all(gates[gate_id] for gate_id in INVARIANCE_GATE_IDS)
        else TERMINAL_DECISION_INSTABILITY
    )


def compare_decision_contract(
    producer_candidate: Mapping[str, Any],
    verifier_candidate: Mapping[str, Any],
    record_comparison: Mapping[str, Any],
) -> dict[str, Any]:
    old_predicates = predecessor_v1._predicate_comparison(
        producer_candidate, verifier_candidate
    )
    roles = compare_role_rankings(
        producer_candidate["block_dominance_metrics"],
        verifier_candidate["block_dominance_metrics"],
    )
    per_record_winner_change_count = int(
        record_comparison["per_record_winner_change_count"]
    )
    per_record_ordering_change_count = int(
        record_comparison["per_record_ordering_change_count"]
    )
    role_winner_change_count = int(
        roles["role_level_dominant_block_change_count"]
    )
    role_ordering_change_count = int(roles["role_ordering_change_count"])
    ordering_change_count = (
        per_record_ordering_change_count + role_ordering_change_count
    )
    supported_set_changed = (
        producer_candidate["supported_mechanism_ids"]
        != verifier_candidate["supported_mechanism_ids"]
    )
    aggregate_changed = (
        producer_candidate["aggregate_mechanism_result"]
        != verifier_candidate["aggregate_mechanism_result"]
    )
    gates = {
        "per_record_winners_identical": per_record_winner_change_count == 0,
        "role_winners_identical": role_winner_change_count == 0,
        "decision_relevant_orderings_identical": ordering_change_count == 0,
        "threshold_decisions_identical": old_predicates[
            "threshold_decision_change_count"
        ]
        == 0,
        "hypothesis_predicates_identical": old_predicates[
            "hypothesis_predicate_change_count"
        ]
        == 0,
        "supported_mechanism_sets_identical": not supported_set_changed,
        "candidate_aggregate_results_identical": not aggregate_changed,
    }
    terminal = terminal_classification(gates)
    return {
        "per_record_winner_change_count": per_record_winner_change_count,
        "role_level_dominant_block_change_count": role_winner_change_count,
        "per_record_ordering_change_count": per_record_ordering_change_count,
        "role_ordering_change_count": role_ordering_change_count,
        "ordering_change_count": ordering_change_count,
        "threshold_decision_change_count": old_predicates[
            "threshold_decision_change_count"
        ],
        "hypothesis_predicate_change_count": old_predicates[
            "hypothesis_predicate_change_count"
        ],
        "supported_mechanism_set_changed": supported_set_changed,
        "candidate_aggregate_result_changed": aggregate_changed,
        "gates": gates,
        "terminal_classification": terminal,
        "terminal_classification_is_exactly_one_registered_value": terminal
        in TERMINAL_CLASSIFICATIONS,
        "role_comparison": roles,
        "hypothesis_comparison": old_predicates["hypotheses"],
    }


def augment_field_comparison(base: Mapping[str, Any]) -> dict[str, Any]:
    fields = base.get("field_comparisons")
    if not isinstance(fields, list):
        raise ValueError("FIELD_COMPARISON_ROWS_MISSING")
    if len(fields) != EXPECTED_FIELD_COUNT:
        raise ValueError("FIELD_COUNT_NOT_1792")
    histogram = ulp_histogram(fields)
    records = compare_record_rankings(fields)
    if records["record_count"] != EXPECTED_RECORD_COUNT:
        raise ValueError("RECORD_COUNT_NOT_224")
    return {
        **base,
        "ulp_histogram": histogram,
        "record_ranking_comparison": records,
        "ulp_histogram_exhaustive": sum(histogram.values()) == len(fields),
    }


def self_validate() -> dict[str, bool]:
    base_shares = {
        block_id: float(8 - index) / 36.0
        for index, block_id in enumerate(raw_v3.BLOCK_IDS)
    }
    lower_swap = dict(base_shares)
    lower_swap[raw_v3.BLOCK_IDS[5]], lower_swap[raw_v3.BLOCK_IDS[6]] = (
        lower_swap[raw_v3.BLOCK_IDS[6]],
        lower_swap[raw_v3.BLOCK_IDS[5]],
    )
    ranking_detected = ordered_ranking(base_shares) != ordered_ranking(lower_swap)
    all_true = {gate_id: True for gate_id in INVARIANCE_GATE_IDS}
    one_false = dict(all_true)
    one_false["role_winners_identical"] = False
    bins = ulp_histogram(
        [
            {"ulp_distance": 0},
            {"ulp_distance": 1},
            {"ulp_distance": 2},
            {"ulp_distance": 3},
        ]
    )
    return {
        "exact_two_terminal_classifications": set(TERMINAL_CLASSIFICATIONS)
        == {
            "PREDICATE_INVARIANT",
            "BLOCKED_OBSERVABLE_DECISION_INSTABILITY",
        },
        "all_true_reaches_invariant": terminal_classification(all_true)
        == TERMINAL_PREDICATE_INVARIANT,
        "one_false_reaches_instability": terminal_classification(one_false)
        == TERMINAL_DECISION_INSTABILITY,
        "lower_rank_swap_detected_with_same_winner": ranking_detected
        and ordered_ranking(base_shares)[0] == ordered_ranking(lower_swap)[0],
        "four_ulp_bins_are_exhaustive": bins
        == {
            "exact_matches": 1,
            "one_ulp_differences": 1,
            "two_ulp_differences": 1,
            "greater_than_two_ulp_differences": 1,
        },
        "predecessor_semantics_count_unchanged": len(predecessor_v1.SEMANTICS_IDS)
        == 2,
    }


def preflight_authorized_calculation(repo_root: str | Path) -> dict[str, Any]:
    root = Path(repo_root).resolve()
    review_path = root / REVIEW_RELATIVE_PATH
    if not review_path.is_file():
        _fail("RECONCILIATION_V2_REVIEW_ANCHOR_MISSING", REVIEW_RELATIVE_PATH)
    packet_path = root / PACKET_RELATIVE_PATH
    packet = _load_json(packet_path, "RECONCILIATION_V2_PACKET_MISSING_OR_INVALID")
    review = _load_json(review_path, "RECONCILIATION_V2_REVIEW_ANCHOR_INVALID")
    tool_sha = _sha256((root / SCRIPT_RELATIVE_PATH).read_bytes())
    predecessor_sha = _sha256(
        (root / predecessor_v1.SCRIPT_RELATIVE_PATH).read_bytes()
    )
    packet_sha = _sha256(packet_path.read_bytes())
    if (
        review.get("verdict") != EXPECTED_REVIEW_VERDICT
        or review.get("selected_next_target") != EXPECTED_REVIEW_NEXT_TARGET
    ):
        _fail("RECONCILIATION_V2_REVIEW_NOT_ACCEPTED")
    accepted = review.get("accepted_calculation_authority")
    if not isinstance(accepted, Mapping):
        _fail("RECONCILIATION_V2_REVIEW_AUTHORITY_MISSING")
    expected = {
        "packet_sha256": packet_sha,
        "tool_sha256": tool_sha,
        "predecessor_tool_sha256": EXPECTED_PREDECESSOR_TOOL_SHA256,
        "source_output_tree_sha256": EXPECTED_SOURCE_OUTPUT_TREE_SHA256,
        "one_read_only_calculation_only": True,
        "simulation_authorized": False,
        "H_A_through_H_E_acceptance_authorized": False,
    }
    if any(accepted.get(key) != value for key, value in expected.items()):
        _fail("RECONCILIATION_V2_REVIEW_AUTHORITY_MISMATCH")
    if predecessor_sha != EXPECTED_PREDECESSOR_TOOL_SHA256:
        _fail("PREDECESSOR_RECONCILIATION_TOOL_IDENTITY_MISMATCH")
    if (
        packet.get("calculation_tool", {}).get("sha256") != tool_sha
        or packet.get("calculation_tool", {}).get("predecessor_tool_sha256")
        != predecessor_sha
    ):
        _fail("RECONCILIATION_V2_TOOL_IDENTITY_MISMATCH")
    v1_review_path = root / V1_REVIEW_RELATIVE_PATH
    if (
        not v1_review_path.is_file()
        or _sha256(v1_review_path.read_bytes()) != EXPECTED_V1_REVIEW_SHA256
    ):
        _fail("V1_BLOCKING_REVIEW_IDENTITY_MISMATCH")
    source_root = (
        root / "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
    )
    if (
        implementation_v0.directory_tree_sha256(source_root)
        != EXPECTED_SOURCE_OUTPUT_TREE_SHA256
    ):
        _fail("SOURCE_OUTPUT_TREE_IDENTITY_MISMATCH")
    result_root = root / RESULT_OUTPUT_ROOT_RELATIVE_PATH
    if result_root.exists():
        _fail("RECONCILIATION_V2_RESULT_ROOT_ALREADY_EXISTS")
    return {
        "review_anchor_sha256": _sha256(review_path.read_bytes()),
        "packet_sha256": packet_sha,
        "tool_sha256": tool_sha,
        "predecessor_tool_sha256": predecessor_sha,
        "source_output_tree_sha256": EXPECTED_SOURCE_OUTPUT_TREE_SHA256,
        "result_root_absent": True,
        "simulation_authorized": False,
        "H_A_through_H_E_acceptance_authorized": False,
    }


def build_authorized_comparison(repo_root: str | Path) -> dict[str, Any]:
    root = Path(repo_root).resolve()
    authority = preflight_authorized_calculation(root)
    source_root = (
        root / "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
    )
    source_tree_before = implementation_v0.directory_tree_sha256(source_root)
    payloads = predecessor_v1._load_payloads(root)
    base_fields = predecessor_v1._compare_all_fields(payloads)
    fields = augment_field_comparison(base_fields)
    producer = predecessor_v1._candidate_result(
        root, predecessor_v1.PRODUCER_SEMANTICS
    )
    verifier = predecessor_v1._candidate_result(
        root, predecessor_v1.VERIFIER_SEMANTICS
    )
    decision = compare_decision_contract(
        producer,
        verifier,
        fields["record_ranking_comparison"],
    )
    source_tree_after = implementation_v0.directory_tree_sha256(source_root)
    if (
        source_tree_before != EXPECTED_SOURCE_OUTPUT_TREE_SHA256
        or source_tree_after != EXPECTED_SOURCE_OUTPUT_TREE_SHA256
    ):
        _fail("SOURCE_OUTPUT_TREE_CHANGED_DURING_RECONCILIATION_V2")
    return {
        "schema_id": f"{TOOL_ID}_RESULT",
        "tool_id": TOOL_ID,
        "authority": authority,
        "source_output_tree_sha256_before": source_tree_before,
        "source_output_tree_sha256_after": source_tree_after,
        "historical_semantics": list(predecessor_v1.SEMANTICS_IDS),
        "field_comparison": fields,
        "producer_candidate": producer,
        "verifier_candidate": verifier,
        "decision_comparison": decision,
        "terminal_classification": decision["terminal_classification"],
        "authority_boundary": {
            "candidate_results_are_authoritative": False,
            "H_A_through_H_E_accepted": False,
            "canonical_semantics_selected": False,
            "independent_result_review_required": True,
            "simulation_invoked": False,
            "historical_outputs_modified": False,
        },
    }


def write_authorized_comparison_once(repo_root: str | Path) -> dict[str, Any]:
    root = Path(repo_root).resolve()
    report = build_authorized_comparison(root)
    result_root = root / RESULT_OUTPUT_ROOT_RELATIVE_PATH
    try:
        result_root.mkdir(parents=False, exist_ok=False)
        with (root / RESULT_RELATIVE_PATH).open("xb") as stream:
            stream.write(_canonical_json_bytes(report))
    except OSError as error:
        _fail("RECONCILIATION_V2_RESULT_EXCLUSIVE_WRITE_FAILED", str(error))
    return report


__all__ = [
    "INVARIANCE_GATE_IDS",
    "ReconciliationV2Error",
    "TERMINAL_CLASSIFICATIONS",
    "TERMINAL_DECISION_INSTABILITY",
    "TERMINAL_PREDICATE_INVARIANT",
    "TOOL_ID",
    "augment_field_comparison",
    "build_authorized_comparison",
    "compare_decision_contract",
    "compare_record_rankings",
    "compare_role_rankings",
    "ordered_ranking",
    "preflight_authorized_calculation",
    "self_validate",
    "terminal_classification",
    "ulp_histogram",
    "write_authorized_comparison_once",
]
