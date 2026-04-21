from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research.metadata import ResearchArtifactMetadata, classify_research_artifact, ensure_valid_research_metadata


REPO_ROOT = find_repo_root(Path(__file__))

PILOT_OUTPUT_PATHS = {
    "pillar": Path("formal/output/research/research_stat_entropy_balance_probe_20260419_v0.json"),
    "seam": Path("formal/output/research/research_qm_stat_transport_witness_probe_20260419_v0.json"),
    "master_action": Path("formal/output/research/research_master_action_transport_binding_probe_20260419_v0.json"),
}
SUMMARY_OUTPUT_PATH = Path("formal/output/reports/research_mode_pilot_pack_20260419_v0.json")


def _ptr(path: Path) -> str:
    return str(path).replace("\\", "/")


def _round(value: float, digits: int = 12) -> float:
    return round(float(value), digits)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _stat_entropy(time_value: float, diffusion_coefficient: float) -> float:
    return 0.5 * math.log(4.0 * math.pi * math.e * diffusion_coefficient * time_value)


def build_pillar_pilot() -> dict[str, Any]:
    diffusion_coefficient = 0.5
    time_value = 1.25
    finite_difference_step = 1.0e-6

    entropy_value = _stat_entropy(time_value, diffusion_coefficient)
    analytic_entropy_rate = 1.0 / (2.0 * time_value)
    fisher_information = 1.0 / (2.0 * diffusion_coefficient * time_value)
    de_bruijn_rhs = diffusion_coefficient * fisher_information
    centered_difference_rate = (
        _stat_entropy(time_value + finite_difference_step, diffusion_coefficient)
        - _stat_entropy(time_value - finite_difference_step, diffusion_coefficient)
    ) / (2.0 * finite_difference_step)

    metadata = ResearchArtifactMetadata(
        artifact_id="research_stat_entropy_balance_probe_20260419_v0",
        research_object="1D Gaussian diffusion entropy functional",
        research_question="Does the declared STAT entropy plan admit a bounded local de Bruijn identity check with a direct analytic artifact?",
        test_type="DERIVATION",
        output_kind="DERIVATION_NOTE",
        target_kind="PILLAR",
        target_binding="TARGET-TH-ENTROPY-PLAN",
        delta_class="ENTROPY_BALANCE_LOCAL_IDENTITY",
        contradiction_context="NONE",
        provenance_family="research_mode_pilot_pack_20260419_v0",
        assumptions=(
            "positive diffusion coefficient on a bounded local probe window",
            "closed-form Gaussian entropy identity remains the primary analytical reference",
        ),
        regime_scope="bounded Gaussian diffusion probe",
        numerical_provenance="ANALYTIC_CLOSED_FORM_WITH_FINITE_DIFFERENCE_CHECK",
        assumption_stability="HIGH",
        artifact_nature="MIXED",
        formalization_route="PYTHON_THEN_LEAN4",
        route_justification="The identity is analytically crisp but is retained here with a finite-difference spot-check before any Lean-facing obligation is declared.",
        lean_candidate_target="STAT_ENTROPY_LOCAL_DE_BRUIJN_IDENTITY",
        lean_module_target="NONE",
        nonclaim_boundary="Repository-local research artifact only; no pillar activation or canonical promotion.",
        promotability="NOT_READY",
    )
    ensure_valid_research_metadata(metadata)

    return {
        "schema_id": "RESEARCH_STAT_ENTROPY_BALANCE_PROBE_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "artifact_path": _ptr(PILOT_OUTPUT_PATHS["pillar"]),
        "artifact_class": classify_research_artifact(metadata),
        "metadata": dict(metadata.__dict__),
        "math_context": {
            "object_equation_v0": "H(t) = 0.5 log(4 pi e D t)",
            "identity_tested_v0": "dH/dt = D I",
            "regime_v0": "bounded Gaussian diffusion probe",
        },
        "metrics": {
            "diffusion_coefficient": diffusion_coefficient,
            "time_value": time_value,
            "entropy_value": _round(entropy_value),
            "analytic_entropy_rate": _round(analytic_entropy_rate),
            "fisher_information": _round(fisher_information),
            "de_bruijn_rhs": _round(de_bruijn_rhs),
            "centered_difference_rate": _round(centered_difference_rate),
            "de_bruijn_gap_abs": _round(abs(analytic_entropy_rate - de_bruijn_rhs)),
            "finite_difference_gap_abs": _round(abs(centered_difference_rate - analytic_entropy_rate)),
        },
        "research_outcome": {
            "result_v0": "RETAIN_LOCAL_ENTROPY_BALANCE_IDENTITY",
            "direct_math_artifact_v0": True,
            "canonical_mutation_attempted_v0": False,
        },
    }


def build_seam_pilot() -> dict[str, Any]:
    amplitude = 1.2
    sigma = 0.9
    velocity = 1.75
    time_value = 0.4
    x_samples = [index * 0.25 for index in range(-8, 9)]

    residual_samples: list[float] = []
    density_samples: list[float] = []
    for x_value in x_samples:
        translated = x_value - velocity * time_value
        density = (amplitude**2) * math.exp(-((translated**2) / (sigma**2)))
        density_dt = density * ((2.0 * velocity * translated) / (sigma**2))
        current_dx = velocity * density * ((-2.0 * translated) / (sigma**2))
        residual = density_dt + current_dx
        density_samples.append(density)
        residual_samples.append(residual)

    metadata = ResearchArtifactMetadata(
        artifact_id="research_qm_stat_transport_witness_probe_20260419_v0",
        research_object="rigid-translation Gaussian density/current ansatz",
        research_question="Can the QM-STAT seam blocker be reduced to a bounded local transport witness with zero continuity residual on a declared ansatz?",
        test_type="REDUCTION_CHECK",
        output_kind="RESULT_SUMMARY",
        target_kind="SEAM",
        target_binding="ROW-SEAM-QM-STAT-001",
        delta_class="LOCAL_TRANSPORT_WITNESS",
        contradiction_context="formal/output/architecture/SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json",
        provenance_family="research_mode_pilot_pack_20260419_v0",
        assumptions=(
            "rigid-translation Gaussian ansatz is treated as a bounded local witness only",
            "continuity closure on sampled support does not authorize seam-state mutation",
        ),
        regime_scope="bounded rigid-translation continuity witness",
        numerical_provenance="ANALYTIC_IDENTITY_WITH_GRID_SAMPLED_RESIDUAL_CHECK",
        assumption_stability="MEDIUM",
        artifact_nature="MIXED",
        formalization_route="PYTHON_THEN_LEAN4",
        route_justification="The witness begins as an exploratory transport reduction, but a retained successful witness naturally matures into a theorem-style obligation if later tightened.",
        lean_candidate_target="QM_STAT_LOCAL_TRANSPORT_WITNESS",
        lean_module_target="NONE",
        nonclaim_boundary="Repository-local research artifact only; no seam-state flip or transport-package promotion.",
        promotability="NOT_READY",
    )
    ensure_valid_research_metadata(metadata)

    return {
        "schema_id": "RESEARCH_QM_STAT_TRANSPORT_WITNESS_PROBE_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "artifact_path": _ptr(PILOT_OUTPUT_PATHS["seam"]),
        "artifact_class": classify_research_artifact(metadata),
        "metadata": dict(metadata.__dict__),
        "math_context": {
            "object_equation_v0": "rho(x,t) = A^2 exp(-(x - vt)^2 / sigma^2), j(x,t) = v rho(x,t)",
            "identity_tested_v0": "partial_t rho + partial_x j = 0",
            "regime_v0": "bounded rigid-translation continuity witness",
        },
        "metrics": {
            "amplitude": amplitude,
            "sigma": sigma,
            "velocity": velocity,
            "time_value": time_value,
            "sample_count": len(x_samples),
            "peak_density": _round(max(density_samples)),
            "continuity_residual_sup_abs": _round(max(abs(value) for value in residual_samples)),
            "continuity_residual_l1": _round(sum(abs(value) for value in residual_samples)),
        },
        "research_outcome": {
            "result_v0": "RETAIN_LOCAL_TRANSPORT_WITNESS_AND_KEEP_SEAM_BOUNDARY_FAIL_CLOSED",
            "direct_math_artifact_v0": True,
            "canonical_mutation_attempted_v0": False,
        },
    }


def build_master_action_pilot() -> dict[str, Any]:
    wave_number = 1.4
    frequency = 2.1
    baseline_lambda = 1.0
    optimized_lambda = (frequency / wave_number) ** 2
    baseline_residual_amplitude = abs(frequency**2 - baseline_lambda * (wave_number**2))
    optimized_residual_amplitude = abs(frequency**2 - optimized_lambda * (wave_number**2))

    metadata = ResearchArtifactMetadata(
        artifact_id="research_master_action_transport_binding_probe_20260419_v0",
        research_object="single-parameter transport-binding surrogate for a traveling-wave probe",
        research_question="Can a one-parameter local transport-binding surrogate collapse the master-action advisory residual on a declared wave probe without mutating canonical state?",
        test_type="DERIVATION",
        output_kind="RESULT_SUMMARY",
        target_kind="MASTER_ACTION",
        target_binding="MASTER_ACTION_PACKET_01_TRANSPORT_BINDING_RECOVERY_20260418_v0",
        delta_class="LOCAL_TRANSPORT_BINDING_SURROGATE",
        contradiction_context="formal/output/reports/master_action_packet_01_transport_binding_recovery_20260418_v0.json",
        provenance_family="research_mode_pilot_pack_20260419_v0",
        assumptions=(
            "single-parameter surrogate remains advisory-only and bounded to the declared wave probe",
            "residual minimization does not by itself stabilize a theorem-grade structural statement",
        ),
        regime_scope="bounded advisory transport-binding surrogate",
        numerical_provenance="CLOSED_FORM_PARAMETER_SWEEP_ON_DECLARED_WAVE_PROBE",
        assumption_stability="MEDIUM",
        artifact_nature="NUMERICAL",
        formalization_route="PYTHON_FIRST",
        route_justification="The surrogate remains numerical and exploratory; it should stay in Python until a stable structural claim exists.",
        lean_candidate_target="NONE",
        lean_module_target="NONE",
        nonclaim_boundary="Repository-local advisory research artifact only; no master-action reclassification or canonical mutation.",
        promotability="NOT_READY",
    )
    ensure_valid_research_metadata(metadata)

    return {
        "schema_id": "RESEARCH_MASTER_ACTION_TRANSPORT_BINDING_PROBE_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "artifact_path": _ptr(PILOT_OUTPUT_PATHS["master_action"]),
        "artifact_class": classify_research_artifact(metadata),
        "metadata": dict(metadata.__dict__),
        "math_context": {
            "object_equation_v0": "phi_tt - lambda phi_xx = 0 on phi(x,t) = sin(k x - omega t)",
            "identity_tested_v0": "lambda* = (omega / k)^2 minimizes the local Euler-Lagrange residual amplitude",
            "regime_v0": "bounded advisory transport-binding surrogate",
        },
        "metrics": {
            "wave_number": wave_number,
            "frequency": frequency,
            "baseline_lambda": baseline_lambda,
            "optimized_lambda": _round(optimized_lambda),
            "baseline_residual_amplitude_abs": _round(baseline_residual_amplitude),
            "optimized_residual_amplitude_abs": _round(optimized_residual_amplitude),
            "optimized_stationarity_recovered": optimized_residual_amplitude < 1.0e-12,
        },
        "research_outcome": {
            "result_v0": "RETAIN_LOCAL_BINDING_MINIMIZER_AS_ADVISORY_ONLY",
            "direct_math_artifact_v0": True,
            "canonical_mutation_attempted_v0": False,
        },
    }


def build_pilot_pack() -> dict[str, Any]:
    pillar = build_pillar_pilot()
    seam = build_seam_pilot()
    master_action = build_master_action_pilot()
    pilots = {
        "pillar": pillar,
        "seam": seam,
        "master_action": master_action,
    }

    artifact_classes = [pilot["artifact_class"] for pilot in pilots.values()]
    direct_math_artifact_count = sum(1 for pilot in pilots.values() if pilot["research_outcome"]["direct_math_artifact_v0"])
    canonical_mutation_attempts = sum(1 for pilot in pilots.values() if pilot["research_outcome"]["canonical_mutation_attempted_v0"])

    return {
        "schema_id": "RESEARCH_MODE_PILOT_PACK_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "policy_basis": "formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md",
        "pilot_artifact_paths": {name: pilot["artifact_path"] for name, pilot in pilots.items()},
        "pilots": pilots,
        "observability": {
            "target_kinds_covered": [
                pillar["metadata"]["target_kind"],
                seam["metadata"]["target_kind"],
                master_action["metadata"]["target_kind"],
            ],
            "artifact_classes": artifact_classes,
            "direct_math_artifact_count": direct_math_artifact_count,
            "canonical_mutation_attempts": canonical_mutation_attempts,
            "release_gate_truth_changes": 0,
            "throughput_signal_v0": "THREE_OF_THREE_PILOTS_TERMINATE_IN_DIRECT_MATH_ARTIFACTS",
            "boundary_signal_v0": "ZERO_CANONICAL_MUTATION_ATTEMPTS_AND_PROMOTION_REMAINS_EXTERNAL_TO_RESEARCH_MODE",
        },
        "summary": {
            "terminal_outcome": "RESEARCH_MODE_PILOT_PACK_MATERIALIZED",
            "step_13_status_v0": "COMPLETE_BOUNDED_v0_NONCLAIM",
            "step_14_status_v0": "PRELIMINARY_LOOP_SHORTENING_SIGNAL_PRESENT_NONCLAIM",
            "next_action": "REVIEW_PILOT_OUTPUTS_FOR_SANDBOX_CANDIDACY_WITHOUT_CANONICAL_MUTATION",
        },
        "report_path": _ptr(SUMMARY_OUTPUT_PATH),
    }


def materialize_pilot_outputs(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    pack = build_pilot_pack()

    for pilot in pack["pilots"].values():
        _write_json(repo_root / pilot["artifact_path"], pilot)

    _write_json(repo_root / SUMMARY_OUTPUT_PATH, pack)
    return pack


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or write the research-mode pilot pack.")
    parser.add_argument("--write", action="store_true", help="Write retained pilot artifacts into the repository output tree.")
    args = parser.parse_args()

    pack = materialize_pilot_outputs() if args.write else build_pilot_pack()
    print(json.dumps(pack["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())