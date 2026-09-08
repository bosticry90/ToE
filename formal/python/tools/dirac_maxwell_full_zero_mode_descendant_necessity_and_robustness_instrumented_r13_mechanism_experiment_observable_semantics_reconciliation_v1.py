from __future__ import annotations

"""Bounded, read-only comparison of the two historical share reductions.

The pure arithmetic helpers are available for preparation tests.  Access to
the preserved experiment outputs is fail-closed until an independent packet
review anchor accepts this exact tool and packet.  The authorized calculation
will compare candidate predicates; it will not accept H_A--H_E or modify any
historical artifact.
"""

import hashlib
import json
import math
import struct
import threading
from collections.abc import Mapping, Sequence
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator, NoReturn

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v3
    as classifier_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v3
    as custody_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as raw_v3,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_v1"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_v1.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_20260716_v1.json"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_PACKET_REVIEW_20260716_v1.json"
)
RESULT_OUTPUT_ROOT_RELATIVE_PATH = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_observable_"
    "semantics_reconciliation_v1"
)
RESULT_RELATIVE_PATH = f"{RESULT_OUTPUT_ROOT_RELATIVE_PATH}/RECONCILIATION-RESULT.json"
EXPECTED_REVIEW_VERDICT = "ACCEPT_OBSERVABLE_SEMANTICS_RECONCILIATION_PACKET"
EXPECTED_REVIEW_NEXT_TARGET = (
    "calculate_dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_v1_once"
)
EXPECTED_SOURCE_OUTPUT_TREE_SHA256 = (
    "95c8209137bfb60796f53d943c99dbef6f6b80e29fad0899d36a775404d34f51"
)
EXPECTED_RESULT_REVIEW_SHA256 = (
    "473d8cd3a8fca2f22fcb189700255b2262a080a8c9396a527286865789e563b7"
)
RESULT_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RESULT_REVIEW_"
    "20260716_v0.json"
)
PRODUCER_SEMANTICS = "NUMPY_ORDERED_FLOAT64_AXIS0_SUM_PLUS_GAMMA64_v0"
VERIFIER_SEMANTICS = "PYTHON_LEFT_TO_RIGHT_SCALAR_SUM_PLUS_GAMMA64_v0"
SEMANTICS_IDS = (PRODUCER_SEMANTICS, VERIFIER_SEMANTICS)

_PATCH_LOCK = threading.Lock()


class ReconciliationError(RuntimeError):
    def __init__(self, diagnostic: str, detail: str = "") -> None:
        self.diagnostic = diagnostic
        self.detail = detail
        super().__init__(f"{diagnostic}: {detail}" if detail else diagnostic)


def _fail(diagnostic: str, detail: str = "") -> NoReturn:
    raise ReconciliationError(diagnostic, detail)


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


def _float_bits(value: float) -> int:
    return struct.unpack(">Q", struct.pack(">d", float(value)))[0]


def ulp_distance(left: float, right: float) -> int:
    """Return the binary64 representable-step distance for nonnegative values."""

    left_value = float(left)
    right_value = float(right)
    if (
        not math.isfinite(left_value)
        or not math.isfinite(right_value)
        or left_value < 0.0
        or right_value < 0.0
    ):
        raise ValueError("ULP inputs must be finite and nonnegative")
    return abs(_float_bits(left_value) - _float_bits(right_value))


def _ordered_normalized_values(
    normalized_by_block: Mapping[str, Any],
) -> tuple[float, ...]:
    if set(normalized_by_block) != set(raw_v3.BLOCK_IDS):
        raise ValueError("normalized vector must contain exactly eight frozen blocks")
    values: list[float] = []
    for block_id in raw_v3.BLOCK_IDS:
        value = float(normalized_by_block[block_id])
        if not math.isfinite(value):
            raise ValueError(f"NONFINITE_NORMALIZED_VALUE:{block_id}")
        if value < 0.0:
            raise ValueError(f"NEGATIVE_NORMALIZED_VALUE:{block_id}")
        if value == 0.0 and np.signbit(np.float64(value)):
            raise ValueError(f"NEGATIVE_ZERO_NORMALIZED_VALUE:{block_id}")
        values.append(value)
    return tuple(values)


def numpy_producer_shares(
    normalized_by_block: Mapping[str, Any],
) -> dict[str, float]:
    """Reconstruct the producer's ordered binary64 axis-0 reduction."""

    values = _ordered_normalized_values(normalized_by_block)
    stacked = np.stack(
        [np.asarray([value], dtype=np.float64) for value in values], axis=0
    )
    denominator = float(np.sum(stacked, axis=0)[0] + raw_v3.GAMMA64)
    if not math.isfinite(denominator) or denominator <= 0.0:
        raise ValueError("INVALID_PRODUCER_DENOMINATOR")
    return {
        block_id: float(value / denominator)
        for block_id, value in zip(raw_v3.BLOCK_IDS, values, strict=True)
    }


def python_verifier_shares(
    normalized_by_block: Mapping[str, Any],
) -> dict[str, float]:
    """Reconstruct the verifier's left-to-right Python scalar reduction."""

    values = _ordered_normalized_values(normalized_by_block)
    denominator = float(sum(values) + raw_v3.GAMMA64)
    if not math.isfinite(denominator) or denominator <= 0.0:
        raise ValueError("INVALID_VERIFIER_DENOMINATOR")
    return {
        block_id: float(value / denominator)
        for block_id, value in zip(raw_v3.BLOCK_IDS, values, strict=True)
    }


def compare_normalized_vector(
    normalized_by_block: Mapping[str, Any],
) -> dict[str, Any]:
    """Compare exactly the two historical semantics for one ordered vector."""

    values = _ordered_normalized_values(normalized_by_block)
    producer = numpy_producer_shares(normalized_by_block)
    verifier = python_verifier_shares(normalized_by_block)
    producer_values = np.asarray(
        [producer[block_id] for block_id in raw_v3.BLOCK_IDS], dtype=np.float64
    )
    verifier_values = np.asarray(
        [verifier[block_id] for block_id in raw_v3.BLOCK_IDS], dtype=np.float64
    )
    rows: list[dict[str, Any]] = []
    for block_id in raw_v3.BLOCK_IDS:
        left = producer[block_id]
        right = verifier[block_id]
        absolute = abs(left - right)
        scale = max(abs(left), abs(right))
        rows.append(
            {
                "block_id": block_id,
                "normalized_input": normalized_by_block[block_id],
                "producer_share": left,
                "verifier_share": right,
                "exact_bit_match": _float_bits(left) == _float_bits(right),
                "absolute_difference": absolute,
                "relative_difference": absolute / scale if scale > 0.0 else 0.0,
                "ulp_distance": ulp_distance(left, right),
            }
        )
    producer_winner = int(np.argmax(producer_values))
    verifier_winner = int(np.argmax(verifier_values))
    return {
        "block_order": list(raw_v3.BLOCK_IDS),
        "ordered_normalized_inputs": list(values),
        "producer_semantics": PRODUCER_SEMANTICS,
        "verifier_semantics": VERIFIER_SEMANTICS,
        "producer_denominator": float(
            np.sum(
                np.stack(
                    [np.asarray([value], dtype=np.float64) for value in values],
                    axis=0,
                ),
                axis=0,
            )[0]
            + raw_v3.GAMMA64
        ),
        "verifier_denominator": float(sum(values) + raw_v3.GAMMA64),
        "fields": rows,
        "exact_match_count": sum(row["exact_bit_match"] for row in rows),
        "mismatch_count": sum(not row["exact_bit_match"] for row in rows),
        "maximum_ulp_distance": max(row["ulp_distance"] for row in rows),
        "producer_dominant_block_id": raw_v3.BLOCK_IDS[producer_winner],
        "verifier_dominant_block_id": raw_v3.BLOCK_IDS[verifier_winner],
        "dominant_block_changed": producer_winner != verifier_winner,
    }


def self_validate() -> dict[str, bool]:
    synthetic = {
        block_id: value
        for block_id, value in zip(
            raw_v3.BLOCK_IDS,
            (1.0e16, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0),
            strict=True,
        )
    }
    comparison = compare_normalized_vector(synthetic)
    zero = {block_id: 0.0 for block_id in raw_v3.BLOCK_IDS}
    zero_comparison = compare_normalized_vector(zero)
    return {
        "exact_eight_block_order": len(raw_v3.BLOCK_IDS) == 8,
        "historical_reductions_diverge_on_bounded_fixture": (
            comparison["mismatch_count"] > 0
        ),
        "dominant_block_fixture_invariant": (
            comparison["dominant_block_changed"] is False
        ),
        "all_zero_vector_is_defined_by_gamma64": (
            zero_comparison["mismatch_count"] == 0
            and zero_comparison["producer_denominator"] == raw_v3.GAMMA64
            and zero_comparison["verifier_denominator"] == raw_v3.GAMMA64
        ),
        "only_two_historical_semantics_registered": len(SEMANTICS_IDS) == 2,
    }


def preflight_authorized_calculation(repo_root: str | Path) -> dict[str, Any]:
    """Fail closed until an independent review accepts this exact packet/tool."""

    root = Path(repo_root).resolve()
    review_path = root / REVIEW_RELATIVE_PATH
    if not review_path.is_file():
        _fail("RECONCILIATION_REVIEW_ANCHOR_MISSING", REVIEW_RELATIVE_PATH)
    packet_path = root / PACKET_RELATIVE_PATH
    packet = _load_json(packet_path, "RECONCILIATION_PACKET_MISSING_OR_INVALID")
    review = _load_json(review_path, "RECONCILIATION_REVIEW_ANCHOR_INVALID")
    tool_sha = _sha256((root / SCRIPT_RELATIVE_PATH).read_bytes())
    packet_sha = _sha256(packet_path.read_bytes())
    if (
        review.get("verdict") != EXPECTED_REVIEW_VERDICT
        or review.get("selected_next_target") != EXPECTED_REVIEW_NEXT_TARGET
    ):
        _fail("RECONCILIATION_REVIEW_NOT_ACCEPTED")
    accepted = review.get("accepted_calculation_authority")
    if not isinstance(accepted, Mapping):
        _fail("RECONCILIATION_REVIEW_AUTHORITY_MISSING")
    expected_authority = {
        "packet_sha256": packet_sha,
        "tool_sha256": tool_sha,
        "source_output_tree_sha256": EXPECTED_SOURCE_OUTPUT_TREE_SHA256,
        "one_read_only_calculation_only": True,
        "simulation_authorized": False,
        "H_A_through_H_E_acceptance_authorized": False,
    }
    if any(accepted.get(key) != value for key, value in expected_authority.items()):
        _fail("RECONCILIATION_REVIEW_AUTHORITY_MISMATCH")
    if packet.get("calculation_tool", {}).get("sha256") != tool_sha:
        _fail("RECONCILIATION_TOOL_IDENTITY_MISMATCH")
    result_review_path = root / RESULT_REVIEW_RELATIVE_PATH
    if (
        not result_review_path.is_file()
        or _sha256(result_review_path.read_bytes()) != EXPECTED_RESULT_REVIEW_SHA256
    ):
        _fail("SOURCE_RESULT_REVIEW_IDENTITY_MISMATCH")
    source_root = root / custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    if (
        implementation_v0.directory_tree_sha256(source_root)
        != EXPECTED_SOURCE_OUTPUT_TREE_SHA256
    ):
        _fail("SOURCE_OUTPUT_TREE_IDENTITY_MISMATCH")
    result_root = root / RESULT_OUTPUT_ROOT_RELATIVE_PATH
    if result_root.exists():
        _fail("RECONCILIATION_RESULT_ROOT_ALREADY_EXISTS")
    return {
        "review_anchor_sha256": _sha256(review_path.read_bytes()),
        "packet_sha256": packet_sha,
        "tool_sha256": tool_sha,
        "source_output_tree_sha256": EXPECTED_SOURCE_OUTPUT_TREE_SHA256,
        "result_root_absent": True,
        "simulation_authorized": False,
        "H_A_through_H_E_acceptance_authorized": False,
    }


def _load_payloads(root: Path) -> dict[str, Mapping[str, Any]]:
    matrix = _load_json(
        root / custody_v3.RUN_MATRIX_RELATIVE_PATH,
        "RUN_MATRIX_MISSING_OR_INVALID",
    )
    records = matrix.get("records")
    if not isinstance(records, list) or len(records) != 6:
        _fail("RUN_MATRIX_IDENTITY_MISMATCH")
    payloads: dict[str, Mapping[str, Any]] = {}
    for record in records:
        if not isinstance(record, Mapping):
            _fail("RUN_MATRIX_IDENTITY_MISMATCH")
        run_id = str(record.get("run_id"))
        payload, _, _ = raw_v3._load_role_payload(
            root / str(record["json_relative_output_path"]),
            root / str(record["npz_relative_output_path"]),
            expected_run_id=run_id,
            expected_json_sha256=None,
            expected_npz_sha256=None,
        )
        raw_v3._validate_payload_identity(payload, record)
        payloads[run_id] = payload
    return payloads


def _normalized_from_defect(defect: Any, tolerance: float) -> dict[str, float]:
    raw = raw_v3._block_maxima(
        np.asarray(defect, dtype=np.float64).reshape(raw_v3.PACKED_WIDTH)
    )
    denominator = max(float(tolerance), raw_v3.GAMMA64)
    return {
        block_id: raw[block_id] / denominator for block_id in raw_v3.BLOCK_IDS
    }


def _compare_all_fields(
    payloads: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    fields: list[dict[str, Any]] = []
    record_winners: list[dict[str, Any]] = []
    for run_id in (
        "MECHv0:R13_LOOSE:INSTRUMENTED",
        "MECHv0:R13_TIGHT:INSTRUMENTED",
        "MECHv0:R10_LOOSE:INSTRUMENTED",
    ):
        payload = payloads[run_id]
        tolerance = float(payload["configuration"]["solver_tolerance"])
        records: list[tuple[str, int, int | None, Any]] = []
        for step in payload["raw_events"]["solver_steps"]:
            for event in step["iteration_events"]:
                records.append(
                    (
                        "iteration",
                        int(step["step"]),
                        int(event["iteration"]),
                        event["packed_update_defect"],
                    )
                )
        for event in payload["raw_events"]["terminal_equation_blocks"]:
            records.append(
                (
                    "terminal",
                    int(event["step"]),
                    None,
                    event["packed_terminal_equation_defect"],
                )
            )
        for family, step, iteration, defect in records:
            comparison = compare_normalized_vector(
                _normalized_from_defect(defect, tolerance)
            )
            record_winners.append(
                {
                    "run_id": run_id,
                    "event_family": family,
                    "step": step,
                    "iteration": iteration,
                    "producer_dominant_block_id": comparison[
                        "producer_dominant_block_id"
                    ],
                    "verifier_dominant_block_id": comparison[
                        "verifier_dominant_block_id"
                    ],
                    "dominant_block_changed": comparison[
                        "dominant_block_changed"
                    ],
                }
            )
            for row in comparison["fields"]:
                fields.append(
                    {
                        "run_id": run_id,
                        "event_family": family,
                        "step": step,
                        "iteration": iteration,
                        "classifier_share_input": family == "terminal",
                        **row,
                    }
                )
    return {
        "field_count": len(fields),
        "exact_match_count": sum(row["exact_bit_match"] for row in fields),
        "mismatch_count": sum(not row["exact_bit_match"] for row in fields),
        "one_or_two_ulp_mismatch_count": sum(
            (not row["exact_bit_match"]) and row["ulp_distance"] in (1, 2)
            for row in fields
        ),
        "maximum_ulp_distance": max(row["ulp_distance"] for row in fields),
        "dominant_block_change_count": sum(
            row["dominant_block_changed"] for row in record_winners
        ),
        "event_ordering_change_count": sum(
            row["dominant_block_changed"] for row in record_winners
        ),
        "field_comparisons": fields,
        "record_winner_comparisons": record_winners,
    }


def _shares_for_defect(
    defect: np.ndarray, tolerance: float, semantics_id: str
) -> tuple[dict[str, float], dict[str, float]]:
    normalized = _normalized_from_defect(defect, tolerance)
    if semantics_id == PRODUCER_SEMANTICS:
        shares = numpy_producer_shares(normalized)
    elif semantics_id == VERIFIER_SEMANTICS:
        shares = python_verifier_shares(normalized)
    else:
        raise ValueError(f"unknown semantics: {semantics_id}")
    return normalized, shares


@contextmanager
def _candidate_assembler_semantics(semantics_id: str) -> Iterator[None]:
    """Temporarily replace only the disputed derived-share reconstruction."""

    original_normalized = raw_v3._normalized_and_shares
    original_validate = raw_v3._validate_block_mapping

    def selected(defect: np.ndarray, tolerance: float) -> tuple[dict[str, float], dict[str, float]]:
        return _shares_for_defect(defect, tolerance, semantics_id)

    def validate_cached(
        observed: Any, expected: Mapping[str, float], name: str
    ) -> None:
        if name in {"iteration.share", "terminal.share"}:
            mapping = raw_v3._require_exact_keys(
                observed,
                raw_v3.BLOCK_IDS,
                diagnostic="UNKNOWN_NINTH_SOLVER_BLOCK",
            )
            for block_id in raw_v3.BLOCK_IDS:
                raw_v3._finite_float(
                    mapping[block_id], f"historical.cached.{name}.{block_id}"
                )
            return
        original_validate(observed, expected, name)

    with _PATCH_LOCK:
        raw_v3._normalized_and_shares = selected
        raw_v3._validate_block_mapping = validate_cached
        try:
            yield
        finally:
            raw_v3._normalized_and_shares = original_normalized
            raw_v3._validate_block_mapping = original_validate


def _candidate_result(root: Path, semantics_id: str) -> dict[str, Any]:
    with _candidate_assembler_semantics(semantics_id):
        assembled = raw_v3.assemble_raw_evidence(root)
    classified = classifier_v3._classify_assembled(assembled)
    return {
        "semantics_id": semantics_id,
        "evidence_result": classified["evidence_result"],
        "supported_mechanism_ids": classified["supported_mechanism_ids"],
        "aggregate_mechanism_result": classified["aggregate_mechanism_result"],
        "hypothesis_decisions": classified["hypothesis_decisions"],
        "block_dominance_metrics": assembled.recomputed_metrics[
            "block_dominance"
        ],
        "distributed_accumulation_metrics": assembled.recomputed_metrics[
            "distributed_accumulation"
        ],
    }


def _predicate_comparison(
    producer: Mapping[str, Any], verifier: Mapping[str, Any]
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for hypothesis_id in classifier_v3.HYPOTHESES_A_TO_D + (classifier_v3.H_E,):
        left = producer["hypothesis_decisions"][hypothesis_id]
        right = verifier["hypothesis_decisions"][hypothesis_id]
        left_criteria = {
            item["criterion_id"]: item["status"]
            for item in left["necessary_condition_decisions"]
        }
        right_criteria = {
            item["criterion_id"]: item["status"]
            for item in right["necessary_condition_decisions"]
        }
        criterion_ids = sorted(set(left_criteria) | set(right_criteria))
        changes = [
            {
                "criterion_id": criterion_id,
                "producer_status": left_criteria.get(criterion_id),
                "verifier_status": right_criteria.get(criterion_id),
                "changed": left_criteria.get(criterion_id)
                != right_criteria.get(criterion_id),
            }
            for criterion_id in criterion_ids
        ]
        rows.append(
            {
                "hypothesis_id": hypothesis_id,
                "producer_status": left["status"],
                "verifier_status": right["status"],
                "hypothesis_status_changed": left["status"] != right["status"],
                "criterion_comparisons": changes,
                "criterion_change_count": sum(item["changed"] for item in changes),
            }
        )
    return {
        "hypotheses": rows,
        "threshold_decision_change_count": sum(
            row["criterion_change_count"] for row in rows
        ),
        "hypothesis_predicate_change_count": sum(
            row["hypothesis_status_changed"] for row in rows
        ),
        "supported_mechanism_set_changed": (
            producer["supported_mechanism_ids"]
            != verifier["supported_mechanism_ids"]
        ),
        "final_candidate_classification_changed": (
            producer["aggregate_mechanism_result"]
            != verifier["aggregate_mechanism_result"]
            or producer["supported_mechanism_ids"]
            != verifier["supported_mechanism_ids"]
        ),
    }


def build_authorized_comparison(repo_root: str | Path) -> dict[str, Any]:
    """Build the one nonauthoritative comparison after accepted packet review."""

    root = Path(repo_root).resolve()
    preflight = preflight_authorized_calculation(root)
    source_root = root / custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    source_tree_before = implementation_v0.directory_tree_sha256(source_root)
    payloads = _load_payloads(root)
    field_comparison = _compare_all_fields(payloads)
    producer = _candidate_result(root, PRODUCER_SEMANTICS)
    verifier = _candidate_result(root, VERIFIER_SEMANTICS)
    predicates = _predicate_comparison(producer, verifier)
    source_tree_after = implementation_v0.directory_tree_sha256(source_root)
    if (
        source_tree_before != EXPECTED_SOURCE_OUTPUT_TREE_SHA256
        or source_tree_after != EXPECTED_SOURCE_OUTPUT_TREE_SHA256
    ):
        _fail("SOURCE_OUTPUT_TREE_CHANGED_DURING_RECONCILIATION")
    return {
        "schema_id": f"{TOOL_ID}_RESULT",
        "tool_id": TOOL_ID,
        "authority": preflight,
        "source_output_tree_sha256_before": source_tree_before,
        "source_output_tree_sha256_after": source_tree_after,
        "historical_semantics": list(SEMANTICS_IDS),
        "field_comparison": field_comparison,
        "producer_candidate": producer,
        "verifier_candidate": verifier,
        "predicate_comparison": predicates,
        "predicate_invariant": (
            field_comparison["dominant_block_change_count"] == 0
            and predicates["threshold_decision_change_count"] == 0
            and predicates["hypothesis_predicate_change_count"] == 0
            and predicates["final_candidate_classification_changed"] is False
        ),
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
    """Exclusively write the one versioned derived comparison artifact."""

    root = Path(repo_root).resolve()
    report = build_authorized_comparison(root)
    result_root = root / RESULT_OUTPUT_ROOT_RELATIVE_PATH
    try:
        result_root.mkdir(parents=False, exist_ok=False)
        with (root / RESULT_RELATIVE_PATH).open("xb") as stream:
            stream.write(_canonical_json_bytes(report))
    except OSError as error:
        _fail("RECONCILIATION_RESULT_EXCLUSIVE_WRITE_FAILED", str(error))
    return report


__all__ = [
    "PRODUCER_SEMANTICS",
    "ReconciliationError",
    "TOOL_ID",
    "VERIFIER_SEMANTICS",
    "build_authorized_comparison",
    "compare_normalized_vector",
    "numpy_producer_shares",
    "preflight_authorized_calculation",
    "python_verifier_shares",
    "self_validate",
    "ulp_distance",
    "write_authorized_comparison_once",
]
