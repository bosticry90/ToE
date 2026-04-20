from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class QmStatSynthesisGateSpec:
    cycle_from: int
    cycle_to: int
    required_doc_tokens: tuple[str, ...]
    from_artifact_status: str
    to_artifact_status: str
    from_criteria_token: str
    to_criteria_token: str
    from_criteria_orders: tuple[int, ...]
    to_criteria_orders: tuple[int, ...]
    newly_added_orders: tuple[int, ...]
    exclusion_equal_orders: tuple[int, ...]
    exclusion_mismatch_orders: tuple[int, ...]


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md').")


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
    20: "twentieth",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _frac_list(values: list[str]) -> list[Fraction]:
    return [Fraction(value) for value in values]


def _synthesis_doc_path(cycle_from: int, cycle_to: int) -> Path:
    return (
        REPO_ROOT
        / "formal"
        / "docs"
        / "paper"
        / f"DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE{cycle_from:02d}_TO_{cycle_to:02d}_SYNTHESIS_v0.md"
    )


def _cycle_doc_path(cycle: int) -> Path:
    return (
        REPO_ROOT
        / "formal"
        / "docs"
        / "paper"
        / f"DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE{cycle:02d}_v0.md"
    )


def _artifact_path(cycle: int) -> Path:
    return REPO_ROOT / "formal" / "output" / f"qm_stat_class_b_seam_physics_pilot_cycle{cycle:02d}_v0.json"


def _gate_relative_path(cycle_from: int, cycle_to: int) -> str:
    return f"formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle{cycle_from:02d}_to_{cycle_to:02d}_synthesis_gate.py"


def _assign_test(module_globals: dict[str, object], test_name: str, test_callable: object) -> None:
    test_callable.__name__ = test_name
    module_globals[test_name] = test_callable


def _moment_section(order: int) -> tuple[str, str, str]:
    if order == 1:
        return "first_moment", "qm_mu", "stat_mu"
    if order == 2:
        return "second_central_moment", "qm_var", "stat_var"
    ordinal = _ORDINAL_NAMES[order]
    return f"{ordinal}_central_moment", f"qm_m{order}", f"stat_m{order}"


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


def _assert_payload_matches_moments(payload: dict, qm_values: dict[int, Fraction], stat_values: dict[int, Fraction], orders: tuple[int, ...]) -> None:
    for order in orders:
        section_key, qm_key, stat_key = _moment_section(order)
        section = payload[section_key]
        assert qm_values[order] == Fraction(section[qm_key])
        assert stat_values[order] == Fraction(section[stat_key])


def register_qm_stat_synthesis_gate_suite(module_globals: dict[str, object], spec: QmStatSynthesisGateSpec) -> None:
    synthesis_doc_path = _synthesis_doc_path(spec.cycle_from, spec.cycle_to)
    from_doc_path = _cycle_doc_path(spec.cycle_from)
    to_doc_path = _cycle_doc_path(spec.cycle_to)
    from_artifact_path = _artifact_path(spec.cycle_from)
    to_artifact_path = _artifact_path(spec.cycle_to)

    def _test_artifacts_exist() -> None:
        for path in (synthesis_doc_path, from_doc_path, to_doc_path, from_artifact_path, to_artifact_path):
            assert path.exists(), f"Missing required file: {path}"

    def _test_doc_tokens() -> None:
        text = _read(synthesis_doc_path)
        required_tokens = [
            f"DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE{spec.cycle_from:02d}_TO_{spec.cycle_to:02d}_SYNTHESIS_v0",
            f"TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE{spec.cycle_from:02d}-TO-{spec.cycle_to:02d}-SYNTHESIS-v0",
            *spec.required_doc_tokens,
            _gate_relative_path(spec.cycle_from, spec.cycle_to),
        ]
        missing = [token for token in required_tokens if token not in text]
        assert not missing, (
            f"QM-STAT Cycle{spec.cycle_from:02d}-to-{spec.cycle_to:02d} synthesis doc missing required token(s): "
            + ", ".join(missing)
        )

    def _test_additive_delta_is_material() -> None:
        from_artifact = _json(from_artifact_path)
        to_artifact = _json(to_artifact_path)

        assert from_artifact["status"] == spec.from_artifact_status
        assert to_artifact["status"] == spec.to_artifact_status

        from_criteria = from_artifact["blocker_discharge_criteria"]
        to_criteria = to_artifact["blocker_discharge_criteria"]
        assert from_criteria["token"] == spec.from_criteria_token
        assert to_criteria["token"] == spec.to_criteria_token

        from_support = [Fraction(value) for value in from_criteria["shared_support"]]
        from_qm = _frac_list(from_criteria["qm_probability_mass"])
        from_stat = _frac_list(from_criteria["stat_probability_mass"])
        from_qm_values = _moment_value_map(from_support, from_qm, spec.from_criteria_orders)
        from_stat_values = _moment_value_map(from_support, from_stat, spec.from_criteria_orders)
        _assert_payload_matches_moments(from_criteria, from_qm_values, from_stat_values, spec.from_criteria_orders)
        for order in spec.from_criteria_orders:
            assert from_qm_values[order] == from_stat_values[order]

        to_support = [Fraction(value) for value in to_criteria["shared_support"]]
        to_qm = _frac_list(to_criteria["qm_probability_mass"])
        to_stat = _frac_list(to_criteria["stat_probability_mass"])
        to_qm_values = _moment_value_map(to_support, to_qm, spec.to_criteria_orders)
        to_stat_values = _moment_value_map(to_support, to_stat, spec.to_criteria_orders)
        _assert_payload_matches_moments(to_criteria, to_qm_values, to_stat_values, spec.to_criteria_orders)
        for order in spec.to_criteria_orders:
            assert to_qm_values[order] == to_stat_values[order]

        for order in spec.newly_added_orders:
            section_key, _, _ = _moment_section(order)
            assert section_key not in from_criteria
            assert section_key in to_criteria

    def _test_exclusion_strengthening_present() -> None:
        from_exclusion = _json(from_artifact_path)["bounded_incompatibility_exclusion"]
        to_exclusion = _json(to_artifact_path)["bounded_incompatibility_exclusion"]

        assert from_exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
        assert to_exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

        for order in spec.newly_added_orders:
            section_key, _, _ = _moment_section(order)
            assert section_key not in from_exclusion
            assert section_key in to_exclusion

        orders = tuple(dict.fromkeys(spec.exclusion_equal_orders + spec.exclusion_mismatch_orders))
        if orders:
            support = [Fraction(value) for value in to_exclusion["shared_support"]]
            qm_probs = _frac_list(to_exclusion["qm_probability_mass"])
            stat_probs = _frac_list(to_exclusion["stat_probability_mass"])
            qm_values = _moment_value_map(support, qm_probs, orders)
            stat_values = _moment_value_map(support, stat_probs, orders)
            _assert_payload_matches_moments(to_exclusion, qm_values, stat_values, orders)
            for order in spec.exclusion_equal_orders:
                assert qm_values[order] == stat_values[order]
            for order in spec.exclusion_mismatch_orders:
                assert qm_values[order] != stat_values[order]

    def _test_promotion_still_blocked() -> None:
        from_artifact = _json(from_artifact_path)
        to_artifact = _json(to_artifact_path)
        assert from_artifact["adjudication"]["value"] == "NOT_YET_DISCHARGED"
        assert to_artifact["adjudication"]["value"] == "NOT_YET_DISCHARGED"
        for artifact in (from_artifact, to_artifact):
            bounded = artifact["bounded_scope"]
            assert bounded["class_flip_claimed"] is False
            assert bounded["full_theorem_discharge_claimed"] is False
            assert bounded["continuum_statistical_closure_claimed"] is False
            assert bounded["external_truth_claimed"] is False

    cycle_str = f"{spec.cycle_from:02d}_to_{spec.cycle_to:02d}"
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_synthesis_artifacts_exist", _test_artifacts_exist)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_synthesis_doc_tokens", _test_doc_tokens)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_additive_delta_is_material", _test_additive_delta_is_material)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_exclusion_strengthening_present", _test_exclusion_strengthening_present)
    _assign_test(module_globals, f"test_qm_stat_cycle{cycle_str}_promotion_still_blocked", _test_promotion_still_blocked)