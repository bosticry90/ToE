from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.comparators.ct02_energy_causality_update_bounds_v0 import (
    CT02EnergyCausalityCase,
    CT02EnergyCausalityReport,
    _load_ct02_report_artifact,
)
from formal.python.toe.comparators.ct03_energy_causality_rep_variant_v0 import (
    CT03EnergyCausalityCase,
    CT03EnergyCausalityReport,
    _load_ct03_report_artifact,
)
from formal.python.toe.comparators.ct05_rep_invariant_admissibility_class_v0 import (
    CT05RepInvariantCase,
    CT05RepInvariantReport,
    ct05_v0_tolerances,
)
from formal.python.toe.comparators.rl11_causality_signal_cone_v0 import (
    RL11CausalityCase,
    RL11CausalityReport,
    _load_rl11_report_artifact,
)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _default_artifact_dir(repo_root: Path) -> Path:
    return repo_root / "formal" / "external_evidence" / "ct05_rep_invariant_admissibility_class_domain_01"


def _pick_case(cases: list[object], *, kind: str) -> object:
    for case in cases:
        if getattr(case, "kind", None) == kind:
            return case
    raise ValueError(f"Missing CT-05 source case kind='{kind}'.")


def _bound_ok(case: CT02EnergyCausalityCase | CT03EnergyCausalityCase, *, params: dict[str, float | str]) -> bool:
    eps_drift = float(params["eps_drift"])
    eps_break = float(params["eps_break"])
    cfl_max = float(params["cfl_max"])
    return bool(
        float(case.cfl) <= cfl_max + eps_break
        and float(case.rel_drift) <= eps_drift
        and float(case.max_rel_drift) <= eps_drift
    )


def _bound_residual(a: CT02EnergyCausalityCase, b: CT03EnergyCausalityCase) -> float:
    return float(
        max(
            abs(float(a.rel_drift) - float(b.rel_drift)),
            abs(float(a.max_rel_drift) - float(b.max_rel_drift)),
            abs(float(a.rel_drop) - float(b.rel_drop)),
        )
    )


def _admissible(case: RL11CausalityCase, *, params: dict[str, float]) -> bool:
    cfl_max = float(params["cfl_max"])
    eps_causal = float(params["eps_causal"])
    return bool(float(case.cfl) <= cfl_max and float(case.leakage_outside_cone) <= eps_causal)


def build_ct05_reports(
    *,
    tolerance_profile: str = "pinned",
    rep_break_delta: float = 1e-2,
) -> tuple[CT05RepInvariantReport, CT05RepInvariantReport]:
    tolerances = ct05_v0_tolerances(tolerance_profile)

    repo_root = _find_repo_root(Path(__file__))
    ct02_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "ct02_energy_causality_update_bounds_domain_01"
        / "ct02_reference_report.json"
    )
    ct03_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "ct03_energy_causality_rep_variant_domain_01"
        / "ct03_reference_report.json"
    )
    rl11_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "rl11_causality_signal_cone_domain_01"
        / "rl11_reference_report.json"
    )

    ct02_report, _ = _load_ct02_report_artifact(ct02_path)
    ct03_report, _ = _load_ct03_report_artifact(ct03_path)
    rl11_report, _ = _load_rl11_report_artifact(rl11_path)

    ct02_pos = _pick_case(ct02_report.cases, kind="positive_control")
    ct03_pos = _pick_case(ct03_report.cases, kind="positive_control")
    rl11_pos = _pick_case(rl11_report.cases, kind="positive_control")
    rl11_neg = _pick_case(rl11_report.cases, kind="negative_control")

    assert isinstance(ct02_pos, CT02EnergyCausalityCase)
    assert isinstance(ct03_pos, CT03EnergyCausalityCase)
    assert isinstance(rl11_pos, RL11CausalityCase)
    assert isinstance(rl11_neg, RL11CausalityCase)

    base_residual = _bound_residual(ct02_pos, ct03_pos)
    bound_ok_ref = _bound_ok(ct02_pos, params=ct02_report.params)
    bound_ok_rep = _bound_ok(ct03_pos, params=ct03_report.params)
    admissible_pos = _admissible(rl11_pos, params=rl11_report.params)
    admissible_neg = _admissible(rl11_neg, params=rl11_report.params)

    params = {
        "eps_rep_invariant": float(tolerances["eps_rep_invariant"]),
        "eps_bound_residual": float(tolerances["eps_bound_residual"]),
        "rep_break_delta": float(rep_break_delta),
        "ct02_report_fingerprint": ct02_report.fingerprint(),
        "ct03_report_fingerprint": ct03_report.fingerprint(),
        "rl11_report_fingerprint": rl11_report.fingerprint(),
        "ct02_domain_tag": str(ct02_report.domain_tag),
        "ct03_domain_tag": str(ct03_report.domain_tag),
        "rl11_domain_tag": str(rl11_report.domain_tag),
    }

    report = CT05RepInvariantReport(
        schema="CT-05/rep_invariant_admissibility_class_front_door_report/v1",
        config_tag="ct05_rep_invariant_admissibility_class_v0",
        regime_tag="CT05_Rep_Invariant_Admissibility_Class",
        domain_tag="ct05_rep_invariant_admissibility_class_domain_01",
        params=params,
        boundary="rep_invariant_gate",
        cases=[
            CT05RepInvariantCase(
                case_id="POSITIVE",
                kind="positive_control",
                admissible_ref=bool(admissible_pos),
                admissible_rep=bool(admissible_pos),
                bound_ok_ref=bool(bound_ok_ref),
                bound_ok_rep=bool(bound_ok_rep),
                bound_residual=float(base_residual),
                rep_delta=0.0,
            ),
            CT05RepInvariantCase(
                case_id="NEG_REP_BREAK",
                kind="negative_control_rep_break",
                admissible_ref=bool(admissible_pos),
                admissible_rep=bool(admissible_pos),
                bound_ok_ref=bool(bound_ok_ref),
                bound_ok_rep=bool(bound_ok_rep),
                bound_residual=float(base_residual + float(rep_break_delta)),
                rep_delta=float(rep_break_delta),
            ),
            CT05RepInvariantCase(
                case_id="NEG_ADMISSIBILITY",
                kind="negative_control_admissibility",
                admissible_ref=bool(admissible_neg),
                admissible_rep=bool(admissible_neg),
                bound_ok_ref=bool(bound_ok_ref),
                bound_ok_rep=bool(bound_ok_rep),
                bound_residual=float(base_residual),
                rep_delta=0.0,
            ),
        ],
    )

    return report, report


def main() -> None:
    repo_root = _find_repo_root(Path(__file__))
    out_dir = _default_artifact_dir(repo_root)
    report, candidate = build_ct05_reports()
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "ct05_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "ct05_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
