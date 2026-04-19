from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class QmStatCycleGateSpec:
    cycle: int
    doc_status_token: str
    blocker_doc_token: str
    exclusion_doc_token: str
    scope_doc_token: str
    cycle_status_doc_token: str
    artifact_status: str
    criteria_token: str
    criteria_orders: tuple[int, ...]
    exclusion_equal_orders: tuple[int, ...]
    exclusion_mismatch_orders: tuple[int, ...]
    exclusion_mismatch_mode: str = "all"


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
_ORDINAL_NAMES = {
    1: "first",
    2: "second",
    3: "third",
    4: "fourth",
    6: "sixth",
    8: "eighth",
    10: "tenth",
    12: "twelfth",
    14: "fourteenth",
    16: "sixteenth",
    18: "eighteenth",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _frac_list(values: list[str]) -> list[Fraction]:
    return [Fraction(value) for value in values]


def _doc_path(cycle: int) -> Path:
    return (
        REPO_ROOT
        / "formal"
        / "docs"
        / "paper"
        / f"DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE{cycle:02d}_v0.md"
    )


def _artifact_path(cycle: int) -> Path:
    return REPO_ROOT / "formal" / "output" / f"qm_stat_class_b_seam_physics_pilot_cycle{cycle:02d}_v0.json"


def _gate_relative_path(cycle: int) -> str:
    return f"formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle{cycle:02d}_gate.py"


def _artifact_relative_path(cycle: int) -> str:
    return f"formal/output/qm_stat_class_b_seam_physics_pilot_cycle{cycle:02d}_v0.json"


def _assign_test(module_globals: dict[str, object], test_name: str, test_callable: object) -> None:
    test_callable.__name__ = test_name
    module_globals[test_name] = test_callable


def _moment_value_map(support: list[Fraction], probs: list[Fraction], orders: tuple[int, ...]) -> dict[int, Fraction]:
    mu = sum(probability * point for probability, point in zip(probs, support))
    values: dict[int, Fraction] = {1: mu}
    centered = [point - mu for point in support]
    if 2 in orders:
        values[2] = sum(probability * delta**2 for probability, delta in zip(probs, centered))
    for order in orders:
        if order in {1, 2}:
            continue
        values[order] = sum(probability * delta**order for probability, delta in zip(probs, centered))
    return values


def _moment_section(order: int) -> tuple[str, str, str]:
    if order == 1:
        return "first_moment", "qm_mu", "stat_mu"
    if order == 2:
        return "second_central_moment", "qm_var", "stat_var"
    ordinal = _ORDINAL_NAMES[order]
    return f"{ordinal}_central_moment", f"qm_m{order}", f"stat_m{order}"


def _assert_payload_matches_moments(payload: dict, qm_values: dict[int, Fraction], stat_values: dict[int, Fraction], orders: tuple[int, ...]) -> None:
    for order in orders:
        section_key, qm_key, stat_key = _moment_section(order)
        section = payload[section_key]
        assert qm_values[order] == Fraction(section[qm_key])
        assert stat_values[order] == Fraction(section[stat_key])


def register_qm_stat_cycle_gate_suite(module_globals: dict[str, object], spec: QmStatCycleGateSpec) -> None:
    doc_path = _doc_path(spec.cycle)
    artifact_path = _artifact_path(spec.cycle)
    prev_artifact_path = _artifact_path(spec.cycle - 1)

    def _test_artifacts_exist() -> None:
        assert doc_path.exists(), f"Missing QM-STAT Cycle{spec.cycle:02d} target doc."
        assert artifact_path.exists(), f"Missing QM-STAT Cycle{spec.cycle:02d} artifact."
        assert prev_artifact_path.exists(), f"Missing QM-STAT Cycle{spec.cycle - 1:02d} predecessor artifact."

    def _test_doc_contains_required_tokens() -> None:
        text = _read(doc_path)
        required_tokens = [
            f"DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE{spec.cycle:02d}_v0",
            f"TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE{spec.cycle:02d}-v0",
            spec.doc_status_token,
            spec.blocker_doc_token,
            spec.exclusion_doc_token,
            spec.scope_doc_token,
            spec.cycle_status_doc_token,
            _artifact_relative_path(spec.cycle),
            _gate_relative_path(spec.cycle),
        ]
        missing = [token for token in required_tokens if token not in text]
        assert not missing, f"QM-STAT Cycle{spec.cycle:02d} doc missing required token(s): " + ", ".join(missing)

    def _test_artifact_schema_and_predecessor_tieback() -> None:
        artifact = _json(artifact_path)
        assert artifact["artifact_id"] == f"qm_stat_class_b_seam_physics_pilot_cycle{spec.cycle:02d}_v0"
        assert artifact["seam_id"] == "SEAM-QM-STAT"
        assert artifact["class_token"] == "TOE_CK_CLASS_COMPATIBILITY_v0"
        assert artifact["status"] == spec.artifact_status

        derived = artifact["derived_from"]
        assert derived["artifact_id"] == f"qm_stat_class_b_seam_physics_pilot_cycle{spec.cycle - 1:02d}_v0"
        assert derived["artifact_path"] == _artifact_relative_path(spec.cycle - 1)

    def _test_blocker_criteria() -> None:
        artifact = _json(artifact_path)
        criteria = artifact["blocker_discharge_criteria"]

        assert criteria["token"] == spec.criteria_token

        xs = [Fraction(value) for value in criteria["shared_support"]]
        qm_p = _frac_list(criteria["qm_probability_mass"])
        stat_p = _frac_list(criteria["stat_probability_mass"])

        assert sum(qm_p) == Fraction(criteria["normalization"]["qm_sum"])
        assert sum(stat_p) == Fraction(criteria["normalization"]["stat_sum"])

        qm_values = _moment_value_map(xs, qm_p, spec.criteria_orders)
        stat_values = _moment_value_map(xs, stat_p, spec.criteria_orders)
        _assert_payload_matches_moments(criteria, qm_values, stat_values, spec.criteria_orders)
        for order in spec.criteria_orders:
            assert qm_values[order] == stat_values[order]

    def _test_exclusion() -> None:
        artifact = _json(artifact_path)
        exclusion = artifact["bounded_incompatibility_exclusion"]
        orders = tuple(dict.fromkeys(spec.exclusion_equal_orders + spec.exclusion_mismatch_orders))

        xs = [Fraction(value) for value in exclusion["shared_support"]]
        qm_p = _frac_list(exclusion["qm_probability_mass"])
        stat_p = _frac_list(exclusion["stat_probability_mass"])

        qm_values = _moment_value_map(xs, qm_p, orders)
        stat_values = _moment_value_map(xs, stat_p, orders)
        _assert_payload_matches_moments(exclusion, qm_values, stat_values, orders)

        for order in spec.exclusion_equal_orders:
            assert qm_values[order] == stat_values[order]

        mismatches = [qm_values[order] != stat_values[order] for order in spec.exclusion_mismatch_orders]
        if spec.exclusion_mismatch_mode == "any":
            assert any(mismatches)
        else:
            assert all(mismatches)

        assert exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    def _test_nonclaim_boundary_and_adjudication() -> None:
        artifact = _json(artifact_path)
        bounded = artifact["bounded_scope"]

        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["continuum_statistical_closure_claimed"] is False
        assert bounded["external_truth_claimed"] is False

        adjudication = artifact["adjudication"]
        assert adjudication["token"] == f"QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE{spec.cycle:02d}_ADJUDICATION"
        assert adjudication["value"] == "NOT_YET_DISCHARGED"

    cycle_str = f"{spec.cycle:02d}"
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_artifacts_exist", _test_artifacts_exist)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_doc_contains_required_tokens", _test_doc_contains_required_tokens)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_artifact_schema_and_predecessor_tieback", _test_artifact_schema_and_predecessor_tieback)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_blocker_criteria", _test_blocker_criteria)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_exclusion", _test_exclusion)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_nonclaim_boundary_and_adjudication", _test_nonclaim_boundary_and_adjudication)