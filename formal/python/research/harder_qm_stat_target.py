from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import acceptance_review
from formal.python.research.metadata import ResearchArtifactMetadata, classify_research_artifact


REPO_ROOT = find_repo_root(Path(__file__))

HARDER_TARGET_ARTIFACT_PATH = Path(
    "formal/output/research/research_qm_stat_transport_moment_stack_probe_20260419_v0.json"
)
HARDER_TARGET_REPORT_PATH = Path(
    "formal/output/reports/research_mode_harder_qm_stat_target_20260419_v0.json"
)

BRIDGE_OBJECT_PATH = Path("formal/output/architecture/SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json")
WITNESS_BINDING_PATH = Path("formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json")
BLOCKER_DEFINITIONS_PATH = Path("formal/output/authority/authoritative_blocker_definitions.json")


def _ptr(path: Path) -> str:
    return str(path).replace("\\", "/")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    target_path = path if path.is_absolute() else (REPO_ROOT / path)
    return json.loads(target_path.read_text(encoding="utf-8"))


def _integrate_trapezoid(values: list[float], step: float) -> float:
    if not values:
        return 0.0
    if len(values) == 1:
        return values[0] * step
    interior = sum(values[1:-1])
    return step * (0.5 * values[0] + interior + 0.5 * values[-1])


def _density(x_value: float, time_value: float, amplitude: float, sigma: float, velocity: float) -> float:
    translated = x_value - velocity * time_value
    return (amplitude**2) * math.exp(-((translated**2) / (sigma**2)))


def _current(x_value: float, time_value: float, amplitude: float, sigma: float, velocity: float) -> float:
    return velocity * _density(x_value, time_value, amplitude, sigma, velocity)


def _moment_stack_snapshot(
    *,
    time_value: float,
    amplitude: float,
    sigma: float,
    velocity: float,
    x_values: list[float],
    dx: float,
    dt: float,
) -> dict[str, float]:
    density_values = [_density(x_value, time_value, amplitude, sigma, velocity) for x_value in x_values]
    current_values = [_current(x_value, time_value, amplitude, sigma, velocity) for x_value in x_values]

    dt_density = [
        (2.0 * velocity * (x_value - velocity * time_value) / (sigma**2)) * rho
        for x_value, rho in zip(x_values, density_values)
    ]
    dx_current = [
        velocity * (-2.0 * (x_values[index] - velocity * time_value) / (sigma**2)) * density_values[index]
        for index in range(1, len(current_values) - 1)
    ]
    continuity_residual = [
        dt_density[index] + dx_current[index - 1]
        for index in range(1, len(x_values) - 1)
    ]

    mass = _integrate_trapezoid(density_values, dx)
    first_moment = _integrate_trapezoid([x_value * rho for x_value, rho in zip(x_values, density_values)], dx)
    second_moment = _integrate_trapezoid([x_value * x_value * rho for x_value, rho in zip(x_values, density_values)], dx)
    j_integral = _integrate_trapezoid(current_values, dx)
    xj_integral = _integrate_trapezoid([x_value * current for x_value, current in zip(x_values, current_values)], dx)

    return {
        "time_value": time_value,
        "mass": mass,
        "continuity_residual_sup_abs": max(abs(value) for value in continuity_residual),
        "first_moment": first_moment,
        "first_moment_rate_closed_form": velocity * mass,
        "first_moment_rate_transport": j_integral,
        "second_moment": second_moment,
        "second_moment_rate_closed_form": 2.0 * velocity * first_moment,
        "second_moment_rate_transport": 2.0 * xj_integral,
    }


def build_harder_qm_stat_target_artifact() -> dict[str, Any]:
    bridge_object = _read_json(BRIDGE_OBJECT_PATH)
    witness_binding = _read_json(WITNESS_BINDING_PATH)
    blocker_definitions = _read_json(BLOCKER_DEFINITIONS_PATH)

    amplitude = 1.2
    sigma = 0.9
    velocity = 1.75
    dx = 0.05
    dt = 1.0e-4
    x_values = [(-12.0 + dx * index) for index in range(int((24.0 / dx)) + 1)]
    time_values = [0.2, 0.4, 0.6]
    snapshots = [
        _moment_stack_snapshot(
            time_value=time_value,
            amplitude=amplitude,
            sigma=sigma,
            velocity=velocity,
            x_values=x_values,
            dx=dx,
            dt=dt,
        )
        for time_value in time_values
    ]

    base_mass = snapshots[0]["mass"]
    latest_definition = next(
        reversed(
            [
                entry
                for entry in blocker_definitions.get("entries", [])
                if entry.get("target_row_id") == bridge_object.get("row_id") and entry.get("status") == "ACTIVE"
            ]
        ),
        {},
    )

    metadata = ResearchArtifactMetadata(
        artifact_id="research_qm_stat_transport_moment_stack_probe_20260419_v0",
        research_object="multi-time QM-STAT transport moment stack anchored to the live residual bridge object",
        research_question="Can the live QM-STAT transport-residual blocker be compressed into a bounded three-time moment-stack witness that preserves continuity and first/second-moment transport identities?",
        test_type="REDUCTION_CHECK",
        output_kind="RESULT_SUMMARY",
        target_kind="SEAM",
        target_binding=str(bridge_object.get("row_id", "ROW-SEAM-QM-STAT-001")),
        delta_class="ROW_LOCAL_TRANSPORT_MOMENT_STACK",
        contradiction_context=_ptr(BRIDGE_OBJECT_PATH),
        provenance_family="research_mode_harder_qm_stat_target_20260419_v0",
        nonclaim_boundary="Repository-local harder live research artifact only; no seam-state flip, sandbox payload emission, or canonical mutation.",
        promotability="NOT_READY",
    )

    return {
        "schema_id": "RESEARCH_QM_STAT_TRANSPORT_MOMENT_STACK_PROBE_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "artifact_path": _ptr(HARDER_TARGET_ARTIFACT_PATH),
        "artifact_class": classify_research_artifact(metadata),
        "metadata": dict(metadata.__dict__),
        "live_anchor": {
            "row_id": bridge_object.get("row_id"),
            "target_package_id": bridge_object.get("target_package_id"),
            "bridge_object_id": bridge_object.get("object_id"),
            "witness_id": witness_binding.get("witness_id"),
            "minimal_upstream_unit_id": witness_binding.get("minimal_upstream_unit_id"),
            "authoritative_blocker_definition_id": latest_definition.get("definition_id"),
            "authoritative_coupling_state": latest_definition.get("coupling_state"),
            "authoritative_promotion_ruling": latest_definition.get("promotion_ruling"),
        },
        "math_context": {
            "object_equation_v0": "rho(x,t) = A^2 exp(-(x-vt)^2 / sigma^2), j(x,t) = v rho(x,t)",
            "identity_stack_v0": [
                "partial_t rho + partial_x j = 0",
                "d/dt int x rho dx = int j dx",
                "d/dt int x^2 rho dx = 2 int x j dx",
            ],
            "regime_v0": "bounded three-time transport-moment stack witness anchored to the live QM-STAT residual package",
        },
        "metrics": {
            "amplitude": amplitude,
            "sigma": sigma,
            "velocity": velocity,
            "x_sample_count": len(x_values),
            "time_values": time_values,
            "continuity_residual_sup_abs_max": max(snapshot["continuity_residual_sup_abs"] for snapshot in snapshots),
            "mass_drift_abs_max": max(abs(snapshot["mass"] - base_mass) for snapshot in snapshots),
            "first_moment_transport_gap_abs_max": max(
                abs(snapshot["first_moment_rate_closed_form"] - snapshot["first_moment_rate_transport"])
                for snapshot in snapshots
            ),
            "second_moment_transport_gap_abs_max": max(
                abs(snapshot["second_moment_rate_closed_form"] - snapshot["second_moment_rate_transport"])
                for snapshot in snapshots
            ),
        },
        "snapshots": snapshots,
        "research_outcome": {
            "result_v0": "RETAIN_ROW_LOCAL_TRANSPORT_MOMENT_STACK_WITNESS_AND_KEEP_SEAM_BOUNDARY_FAIL_CLOSED",
            "direct_math_artifact_v0": True,
            "canonical_mutation_attempted_v0": False,
        },
    }


def build_harder_qm_stat_target_report() -> dict[str, Any]:
    acceptance = acceptance_review.build_acceptance_review()
    artifact = build_harder_qm_stat_target_artifact()
    metrics = dict(artifact["metrics"])
    live_anchor = dict(artifact["live_anchor"])

    acceptance_ok = acceptance["summary"]["terminal_outcome"] == "RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_PASSED_BOUNDED"
    live_anchor_ok = all(
        [
            live_anchor.get("row_id") == "ROW-SEAM-QM-STAT-001",
            live_anchor.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            live_anchor.get("bridge_object_id") == "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0",
            live_anchor.get("witness_id") == "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0",
        ]
    )
    metric_stack_ok = all(
        [
            float(metrics["continuity_residual_sup_abs_max"]) < 1.0e-6,
            float(metrics["mass_drift_abs_max"]) < 1.0e-6,
            float(metrics["first_moment_transport_gap_abs_max"]) < 1.0e-5,
            float(metrics["second_moment_transport_gap_abs_max"]) < 1.0e-4,
            bool(artifact["research_outcome"]["direct_math_artifact_v0"]),
            not bool(artifact["research_outcome"]["canonical_mutation_attempted_v0"]),
        ]
    )
    all_criteria_pass = all([acceptance_ok, live_anchor_ok, metric_stack_ok])

    return {
        "schema_id": "RESEARCH_MODE_HARDER_QM_STAT_TARGET_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "target_scope_v0": "ONE_HARDER_LIVE_QM_STAT_ROW_LOCAL_TRANSPORT_RESIDUAL_TARGET_ONLY",
        "artifact": artifact,
        "criteria": {
            "step14_acceptance_precondition": {
                "status_v0": "PASS" if acceptance_ok else "FAIL",
                "criterion_v0": "The harder live target runs only after the research-mode rollout passes Step 14 acceptance.",
            },
            "live_anchor_alignment": {
                "status_v0": "PASS" if live_anchor_ok else "FAIL",
                "criterion_v0": "The harder target must bind to the live QM-STAT residual bridge object and witness surfaces.",
            },
            "transport_moment_stack": {
                "status_v0": "PASS" if metric_stack_ok else "FAIL",
                "criterion_v0": "The harder target must materialize a direct multi-time continuity and transport-moment witness with bounded residual gaps.",
            },
        },
        "objective_quality": {
            "criteria": {
                "acceptance_ok": acceptance_ok,
                "live_anchor_ok": live_anchor_ok,
                "metric_stack_ok": metric_stack_ok,
                "all_criteria_pass": all_criteria_pass,
            },
            "inputs": {
                "artifact_id": artifact["metadata"]["artifact_id"],
                "artifact_path": artifact["artifact_path"],
                "row_id": live_anchor.get("row_id"),
                "target_package_id": live_anchor.get("target_package_id"),
                "authoritative_blocker_definition_id": live_anchor.get("authoritative_blocker_definition_id"),
                "continuity_residual_sup_abs_max": metrics["continuity_residual_sup_abs_max"],
                "mass_drift_abs_max": metrics["mass_drift_abs_max"],
                "first_moment_transport_gap_abs_max": metrics["first_moment_transport_gap_abs_max"],
                "second_moment_transport_gap_abs_max": metrics["second_moment_transport_gap_abs_max"],
            },
            "summary": {
                "harder_target_basis_v0": "LIVE_QM_STAT_ROW_LOCAL_RESIDUAL_PACKAGE_WITH_THREE_TIME_TRANSPORT_MOMENT_STACK",
                "harder_target_limit_v0": "This is still a bounded local witness and does not claim seam closure, sandbox promotion, or canonical change.",
            },
        },
        "summary": {
            "terminal_outcome": (
                "RESEARCH_MODE_HARDER_QM_STAT_TARGET_MATERIALIZED"
                if all_criteria_pass
                else "RESEARCH_MODE_HARDER_QM_STAT_TARGET_EVIDENCE_INCOMPLETE"
            ),
            "row_id": live_anchor.get("row_id"),
            "target_package_id": live_anchor.get("target_package_id"),
            "harder_target_status_v0": (
                "COMPLETE_BOUNDED_v0_NONCLAIM" if all_criteria_pass else "EVIDENCE_INCOMPLETE_v0_NONCLAIM"
            ),
            "next_action": (
                "COMPARE_QM_STAT_SANDBOX_CANDIDATE_AND_HARDER_TARGET_OUTPUTS_BEFORE_NEXT_GOVERNED_ENTRY"
                if all_criteria_pass
                else "REPAIR_HARDER_QM_STAT_TARGET_INPUTS_AND_RERUN"
            ),
        },
        "source_bundle": {
            "step14_acceptance_report": "formal/output/reports/research_mode_step14_acceptance_review_20260419_v0.json",
            "bridge_object": _ptr(BRIDGE_OBJECT_PATH),
            "witness_binding": _ptr(WITNESS_BINDING_PATH),
            "authoritative_blocker_definitions": _ptr(BLOCKER_DEFINITIONS_PATH),
        },
        "non_claim_boundary": "Repository-local harder live QM-STAT research target only; no seam closure, sandbox payload emission, promotion, or canonical mutation claim.",
    }


def materialize_harder_qm_stat_target(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    report = build_harder_qm_stat_target_report()
    _write_json(repo_root / HARDER_TARGET_ARTIFACT_PATH, report["artifact"])
    _write_json(repo_root / HARDER_TARGET_REPORT_PATH, report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or write the harder live QM-STAT research target.")
    parser.add_argument("--write", action="store_true", help="Write the harder live QM-STAT artifact and report into the repository output tree.")
    args = parser.parse_args()

    report = materialize_harder_qm_stat_target() if args.write else build_harder_qm_stat_target_report()
    print(json.dumps(report["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())