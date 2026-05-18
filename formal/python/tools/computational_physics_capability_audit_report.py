from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0"
AUDIT_ID = "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
REPORT_ID = "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_REPORT_v0"
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_JSON_OUT = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_REPORT_v0.md"

ALLOWED_ROLES = [
    "simulation",
    "verification",
    "validation_relevant",
    "robustness",
    "regime_recovery",
    "falsifier",
    "uq_relevant",
    "model_comparison",
    "governance_only",
]

STATUS_ENUMS = {
    "claim_boundary": [
        "nonclaim",
        "internal_consequence",
        "known_limit_relevant",
        "validation_candidate",
        "blocked",
    ],
    "verification_status": [
        "none",
        "partial",
        "gated",
        "convergence_checked",
        "independently_replicated",
    ],
    "validation_status": [
        "none",
        "internal_only",
        "known_limit_candidate",
        "empirical_candidate",
        "validated_in_bounded_domain",
    ],
    "uq_status": [
        "none",
        "qualitative",
        "partial",
        "quantitative",
    ],
    "robustness_status": [
        "none",
        "partial",
        "perturbation_scanned",
        "resolution_scanned",
        "solver_crosschecked",
    ],
    "known_limit_status": [
        "none",
        "candidate",
        "partial",
        "passed",
        "failed",
        "blocked",
    ],
    "falsifier_status": [
        "absent",
        "defined",
        "executed_pass",
        "executed_fail",
        "blocked",
    ],
}


def _norm(path: str) -> str:
    return path.replace("\\", "/")


def _ptr(path: Path) -> str:
    return _norm(str(path.relative_to(REPO_ROOT)))


def _path_status(paths: list[str]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for rel in paths:
        norm = _norm(rel)
        parts = Path(norm).parts
        forbidden = bool(parts and parts[0] in {"archive", "quarantine"}) or "/quarantine/" in norm
        if forbidden:
            raise ValueError(f"Forbidden retired-storage or quarantine audit path: {norm}")
        abs_path = REPO_ROOT / norm
        out.append({"path": norm, "exists": abs_path.exists()})
    return out


def _row(
    *,
    artifact_id: str,
    artifact_path: str,
    computational_physics_role: list[str],
    physics_domain: list[str],
    claim_boundary: str,
    verification_status: str,
    validation_status: str,
    uq_status: str,
    robustness_status: str,
    known_limit_status: str,
    falsifier_status: str,
    evidence_paths: list[str],
    notes: str,
) -> dict[str, Any]:
    unknown_roles = sorted(set(computational_physics_role) - set(ALLOWED_ROLES))
    if unknown_roles:
        raise ValueError(f"{artifact_id} has unknown roles: {unknown_roles}")
    status_values = {
        "claim_boundary": claim_boundary,
        "verification_status": verification_status,
        "validation_status": validation_status,
        "uq_status": uq_status,
        "robustness_status": robustness_status,
        "known_limit_status": known_limit_status,
        "falsifier_status": falsifier_status,
    }
    for field, value in status_values.items():
        if value not in STATUS_ENUMS[field]:
            raise ValueError(f"{artifact_id} has invalid {field}: {value}")

    return {
        "artifact_id": artifact_id,
        "artifact_path": _norm(artifact_path),
        "computational_physics_role": computational_physics_role,
        "physics_domain": physics_domain,
        "claim_boundary": claim_boundary,
        "verification_status": verification_status,
        "validation_status": validation_status,
        "uq_status": uq_status,
        "robustness_status": robustness_status,
        "known_limit_status": known_limit_status,
        "falsifier_status": falsifier_status,
        "promotion_allowed": False,
        "evidence_paths": _path_status(evidence_paths),
        "notes": notes,
    }


def audit_rows() -> list[dict[str, Any]]:
    return [
        _row(
            artifact_id="C6_CP_NLSE_2D_LANE",
            artifact_path="formal/python/crft/cp_nlse_2d.py",
            computational_physics_role=["simulation", "verification", "robustness", "regime_recovery", "falsifier"],
            physics_domain=["nonlinear_field", "QM", "general"],
            claim_boundary="internal_consequence",
            verification_status="gated",
            validation_status="internal_only",
            uq_status="none",
            robustness_status="partial",
            known_limit_status="partial",
            falsifier_status="defined",
            evidence_paths=[
                "formal/python/crft/cp_nlse_2d.py",
                "formal/python/crft/tests/test_c6_cp_nlse_2d_dispersion.py",
                "formal/python/crft/tests/test_c6_cp_nlse_2d_dispersion_eigenfunction.py",
                "formal/python/crft/tests/test_c6_cp_nlse_2d_norm_drift.py",
                "formal/toe_formal/ToeFormal/CPNLSE2D/Dispersion.lean",
            ],
            notes=(
                "2D CP-NLSE executable lane with dispersion and norm-drift gates; "
                "safe reading is internal computational consequence plus limited known-limit pressure."
            ),
        ),
        _row(
            artifact_id="C7_MT01A_ACOUSTIC_METRIC_LANE",
            artifact_path="formal/python/crft/acoustic_metric.py",
            computational_physics_role=["simulation", "verification", "validation_relevant", "robustness", "falsifier"],
            physics_domain=["GR", "nonlinear_field", "cross_pillar"],
            claim_boundary="validation_candidate",
            verification_status="gated",
            validation_status="internal_only",
            uq_status="none",
            robustness_status="perturbation_scanned",
            known_limit_status="candidate",
            falsifier_status="defined",
            evidence_paths=[
                "formal/python/crft/acoustic_metric.py",
                "formal/python/tests/test_mt01_acoustic_metric_lock.py",
                "formal/python/tests/test_c7_acoustic_metric_inequalities.py",
                "formal/python/tests/test_c7_acoustic_metric_perturbation_stability.py",
                "formal/toe_formal/ToeFormal/CRFT/Geom/AcousticMetric.lean",
            ],
            notes=(
                "Acoustic-metric diagnostic construction with inequality and perturbation gates; "
                "safe reading is emergent-geometry candidate pressure, not geometry validation."
            ),
        ),
        _row(
            artifact_id="UCFF_SPECTRAL_AUDIT_LINEAGE",
            artifact_path="formal/docs/ucff_core_front_door_spec.md",
            computational_physics_role=["verification", "uq_relevant", "model_comparison", "regime_recovery"],
            physics_domain=["QFT", "nonlinear_field", "general"],
            claim_boundary="internal_consequence",
            verification_status="gated",
            validation_status="internal_only",
            uq_status="qualitative",
            robustness_status="partial",
            known_limit_status="candidate",
            falsifier_status="defined",
            evidence_paths=[
                "formal/docs/ucff_core_front_door_spec.md",
                "formal/docs/ucff_core_front_door_contract.md",
                "formal/python/toe/ucff/core_front_door.py",
                "formal/python/tests/test_ucff_core_front_door_roundtrip.py",
                "formal/python/tests/test_ucff_core_front_door_symbolic_invariant_01.py",
                "formal/python/tests/test_ucff_core_front_door_symbolic_invariant_02.py",
            ],
            notes=(
                "UCFF front-door and symbolic invariants support structural numerical bookkeeping; "
                "safe reading is internal structural support and future UQ relevance."
            ),
        ),
        _row(
            artifact_id="BRAGG_DISPERSION_ELIMINATIVE_LANE",
            artifact_path="formal/docs/cv01_bec_bragg_v1_front_door_contract.md",
            computational_physics_role=["validation_relevant", "falsifier", "model_comparison", "uq_relevant"],
            physics_domain=["QM", "nonlinear_field"],
            claim_boundary="validation_candidate",
            verification_status="gated",
            validation_status="empirical_candidate",
            uq_status="partial",
            robustness_status="partial",
            known_limit_status="candidate",
            falsifier_status="defined",
            evidence_paths=[
                "formal/docs/cv01_bec_bragg_v1_front_door_contract.md",
                "formal/docs/first_empirical_comparator_domain_bec_bragg.md",
                "formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md",
                "formal/python/toe/comparators/cv01_bec_bragg_v1.py",
                "formal/python/tests/test_cv01_bec_bragg_v1_front_door.py",
                "formal/python/tests/test_ov_br03n_bragg_dispersion_digitized_lock.py",
            ],
            notes=(
                "Bragg/dispersion comparator lane can support pruning pressure and empirical-comparator design; "
                "safe reading remains validation-candidate, not validation complete."
            ),
        ),
        _row(
            artifact_id="RL01_RELATIVISTIC_DISPERSION_LIMIT",
            artifact_path="formal/docs/rl01_relativistic_dispersion_v0_front_door_contract.md",
            computational_physics_role=["verification", "validation_relevant", "regime_recovery", "falsifier", "model_comparison"],
            physics_domain=["SR", "QFT", "general"],
            claim_boundary="known_limit_relevant",
            verification_status="gated",
            validation_status="known_limit_candidate",
            uq_status="none",
            robustness_status="partial",
            known_limit_status="partial",
            falsifier_status="defined",
            evidence_paths=[
                "formal/docs/rl01_relativistic_dispersion_v0_front_door_contract.md",
                "formal/python/toe/comparators/rl01_relativistic_dispersion_v0.py",
                "formal/python/tests/test_rl01_relativistic_dispersion_v0_front_door.py",
                "formal/python/tests/test_rl01_relativistic_dispersion_v0_surface_contract_freeze.py",
                "formal/external_evidence/relativistic_dispersion_domain_01/rl01_reference_report.json",
                "formal/external_evidence/relativistic_dispersion_domain_01/rl01_candidate_report.json",
            ],
            notes=(
                "Relativistic dispersion front door is a known-limit recovery candidate with deterministic checks; "
                "safe reading is conditional regime-recovery evidence only."
            ),
        ),
        _row(
            artifact_id="RL02_NONRELATIVISTIC_NLSE_LIMIT",
            artifact_path="formal/docs/rl02_nonrelativistic_nlse_v0_front_door_contract.md",
            computational_physics_role=["verification", "validation_relevant", "regime_recovery", "falsifier", "model_comparison"],
            physics_domain=["QM", "QFT", "nonlinear_field"],
            claim_boundary="known_limit_relevant",
            verification_status="gated",
            validation_status="known_limit_candidate",
            uq_status="none",
            robustness_status="partial",
            known_limit_status="partial",
            falsifier_status="defined",
            evidence_paths=[
                "formal/docs/rl02_nonrelativistic_nlse_v0_front_door_contract.md",
                "formal/python/toe/comparators/rl02_nonrelativistic_nlse_v0.py",
                "formal/python/tests/test_rl02_nonrelativistic_nlse_v0_front_door.py",
                "formal/python/tests/test_rl02_nonrelativistic_nlse_v0_surface_contract_freeze.py",
                "formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_reference_report.json",
                "formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_candidate_report.json",
            ],
            notes=(
                "Nonrelativistic NLSE front door is a known-limit recovery candidate with deterministic checks; "
                "safe reading is conditional regime-recovery evidence only."
            ),
        ),
        _row(
            artifact_id="GR01_DERIVATION_COMPLETENESS_GATE",
            artifact_path="formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md",
            computational_physics_role=["verification", "regime_recovery", "governance_only"],
            physics_domain=["GR"],
            claim_boundary="blocked",
            verification_status="gated",
            validation_status="none",
            uq_status="none",
            robustness_status="partial",
            known_limit_status="blocked",
            falsifier_status="blocked",
            evidence_paths=[
                "formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md",
                "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md",
                "formal/python/tests/test_gr01_hardening_roadmap_gate.py",
                "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean",
                "formal/toe_formal/ToeFormal/Variational/GR01AssumptionLedger.lean",
            ],
            notes=(
                "GR01 hardening is derivation-readiness and weak-field bookkeeping; "
                "safe reading is no computational validation claim and no claim promotion."
            ),
        ),
        _row(
            artifact_id="BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS",
            artifact_path="formal/python/tools/bridge_program_orthogonality_report_generate.py",
            computational_physics_role=["verification", "robustness", "falsifier", "model_comparison"],
            physics_domain=["cross_pillar", "general"],
            claim_boundary="internal_consequence",
            verification_status="gated",
            validation_status="internal_only",
            uq_status="qualitative",
            robustness_status="perturbation_scanned",
            known_limit_status="none",
            falsifier_status="defined",
            evidence_paths=[
                "formal/python/tools/bridge_program_orthogonality_report_generate.py",
                "formal/python/tools/bridge_program_orthogonality_mismatch_report_generate.py",
                "formal/python/tests/test_bridge_program_orthogonality_report_generate_determinism.py",
                "formal/python/tests/test_bridge_program_orthogonality_robustness_guard.py",
                "formal/python/tests/test_bridge_program_orthogonality_mismatch_report_generate_determinism.py",
            ],
            notes=(
                "Bridge orthogonality reports classify seam mismatch and robustness behavior; "
                "safe reading is failure/orthogonality evidence only."
            ),
        ),
    ]


def build_audit_payload(*, captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC) -> dict[str, Any]:
    rows = audit_rows()
    roles_present = sorted({role for row in rows for role in row["computational_physics_role"]})
    missing_evidence = [
        {"artifact_id": row["artifact_id"], "path": evidence["path"]}
        for row in rows
        for evidence in row["evidence_paths"]
        if not evidence["exists"]
    ]
    promotion_allowed_count = sum(1 for row in rows if row["promotion_allowed"])
    return {
        "schema_id": SCHEMA_ID,
        "audit_id": AUDIT_ID,
        "report_id": REPORT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "roadmap_pointer": "formal/docs/paper/COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md",
        "policy_bindings": [
            "formal/docs/release/GROUNDED_SPECULATION_POSTURE_STANDARD_v0.md",
            "formal/docs/release/COMPUTATIONAL_ANALYSIS_BOUNDED_AUTHORIZATION_CLASS_20260416_v0.json",
            "formal/docs/release/COMPUTATIONAL_ANALYSIS_LANE_EXECUTION_POLICY_20260416_v0.md",
            "formal/docs/paper/CLAIM_TAXONOMY_v1.md",
        ],
        "classification_outcome": (
            "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_CLASSIFIES_EXISTING_NONCLAIM_ANALYSIS_SURFACES_WITHOUT_PROMOTION"
        ),
        "scope": {
            "scope_rule": "BOUNDED_MAJOR_EXISTING_COMPUTATIONAL_LANES_ONLY",
            "included_artifact_count": len(rows),
            "included_lanes": [row["artifact_id"] for row in rows],
            "excluded_scope": [
                "EVERY_PYTHON_TEST_IN_REPO",
                "EVERY_LEAN_FILE_IN_REPO",
                "FULL_PAPER_INVENTORY",
                "ARCHIVE_AND_QUARANTINE_PATHS",
            ],
        },
        "allowed_roles": ALLOWED_ROLES,
        "status_enums": STATUS_ENUMS,
        "audit_rows": rows,
        "summary": {
            "row_count": len(rows),
            "roles_present": roles_present,
            "promotion_allowed_count": promotion_allowed_count,
            "all_promotion_allowed_false": promotion_allowed_count == 0,
            "missing_evidence_count": len(missing_evidence),
            "missing_evidence": missing_evidence,
            "next_recommended_packet": "VVUQ_CREDIBILITY_LEDGER_v0_AFTER_RESULT_REVIEW",
        },
        "non_claim_boundary": (
            "Capability classification only; no theorem discharge, blocker movement, lane reopen, "
            "Phase 2 authorization, empirical validation claim, seam closure, master-action promotion, "
            "or external-truth claim."
        ),
    }


def build_markdown_report(payload: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Computational Physics Capability Audit Report v0",
        "",
        "Spec ID:",
        "- `COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_REPORT_v0`",
        "",
        "Status:",
        f"- `{payload['status']}`",
        "",
        "Classification outcome:",
        f"- `{payload['classification_outcome']}`",
        "",
        "Authority binding:",
        f"- `{payload['authorization_class']}`",
        f"- Roadmap: `{payload['roadmap_pointer']}`",
        "- JSON audit: `formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_computational_physics_capability_audit_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {payload['non_claim_boundary']}",
        "",
        "Scope:",
        f"- Included rows: `{payload['summary']['row_count']}`",
        "- Excluded: every Python test, every Lean file, full paper inventory, archive paths, quarantine paths.",
        "",
        "## Audit Rows",
        "",
        "| Artifact | Roles | Claim boundary | Verification | Validation | UQ | Robustness | Known limit | Falsifier | Promotion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["audit_rows"]:
        roles = ", ".join(row["computational_physics_role"])
        lines.append(
            "| `{artifact_id}` | {roles} | `{claim_boundary}` | `{verification_status}` | "
            "`{validation_status}` | `{uq_status}` | `{robustness_status}` | "
            "`{known_limit_status}` | `{falsifier_status}` | `{promotion}` |".format(
                artifact_id=row["artifact_id"],
                roles=roles,
                claim_boundary=row["claim_boundary"],
                verification_status=row["verification_status"],
                validation_status=row["validation_status"],
                uq_status=row["uq_status"],
                robustness_status=row["robustness_status"],
                known_limit_status=row["known_limit_status"],
                falsifier_status=row["falsifier_status"],
                promotion=str(row["promotion_allowed"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            f"- Promotion allowed count: `{payload['summary']['promotion_allowed_count']}`",
            f"- Missing evidence count: `{payload['summary']['missing_evidence_count']}`",
            f"- Next recommended packet: `{payload['summary']['next_recommended_packet']}`",
            "",
            "Interpretive note:",
            "- This audit says that the selected artifacts perform recognizable computational-physics functions.",
            "- It does not say that those artifacts validate the ToE.",
            "",
        ]
    )
    return "\n".join(lines)


def write_audit(*, json_out: Path, md_out: Path, captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC) -> dict[str, Any]:
    payload = build_audit_payload(captured_at_utc=captured_at_utc)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(payload), encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the bounded computational-physics capability audit.")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    payload = write_audit(json_out=json_out, md_out=md_out, captured_at_utc=str(ns.captured_at_utc))
    print(
        "computational_physics_capability_audit_report: "
        f"rows={payload['summary']['row_count']} "
        f"promotion_allowed_count={payload['summary']['promotion_allowed_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
