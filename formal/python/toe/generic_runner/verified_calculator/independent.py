"""Pinned Julia/Nemo and Lean runtime-certificate verification routes."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from .api import EvaluatedRunV1, JuliaEvidenceV1, LeanEvidenceV1
from .canonical import canonical_bytes, file_sha256, strict_json_bytes
from .errors import CalculatorError, require


REPOSITORY_ROOT = Path(__file__).resolve().parents[5]
JULIA_PROJECT = REPOSITORY_ROOT / "formal" / "tooling" / "scientific_compute" / "julia"
JULIA_SCRIPT = JULIA_PROJECT / "verified_calculator_v1.jl"
JULIA_NUMERICS_SCRIPT = JULIA_PROJECT / "verified_calculator_numerics_v1.jl"
LEAN_PROJECT = REPOSITORY_ROOT / "formal" / "toe_formal"
LEAN_CHECKER = LEAN_PROJECT / ".lake" / "build" / "bin" / ("vpc_certificate_checker.exe" if os.name == "nt" else "vpc_certificate_checker")


def _julia_executable() -> Path:
    override = os.environ.get("VPC_JULIA_EXE")
    if override:
        return Path(override)
    if os.name == "nt":
        local = Path(os.environ.get("LOCALAPPDATA", "")) / "Programs" / "Julia-1.12.6" / "bin" / "julia.exe"
        if local.is_file():
            return local
    return Path("julia")


def run_julia_independent(run: EvaluatedRunV1) -> JuliaEvidenceV1:
    require(JULIA_SCRIPT.is_file(), "JULIA_VERIFIER_SCRIPT")
    with tempfile.TemporaryDirectory(prefix="vpc-julia-") as directory:
        root = Path(directory)
        documents = {
            "profile.json": run.contracts.profile.to_dict(),
            "policy.json": run.contracts.policy.to_dict(),
            "request.json": run.request.to_dict(),
            "candidate.json": run.candidate.to_dict(),
        }
        for name, value in documents.items():
            (root / name).write_bytes(canonical_bytes(value))
        command = [
            str(_julia_executable()), "--startup-file=no", f"--project={JULIA_PROJECT}", str(JULIA_SCRIPT),
            str(root / "profile.json"), str(root / "policy.json"), str(root / "request.json"), str(root / "candidate.json"), str(run.contracts.source_root),
        ]
        environment = dict(os.environ)
        environment.update({"JULIA_PKG_OFFLINE": "true", "JULIA_HISTORY": str(root / "julia_history")})
        process = subprocess.run(command, capture_output=True, timeout=run.contracts.policy.resource_limits.trusted_route_seconds, env=environment)
        require(process.returncode == 0, "JULIA_VERIFIER_REJECTED", detail=process.stderr.decode("utf-8", "replace")[-10_000:])
        raw = process.stdout
        require(len(raw) <= run.contracts.policy.resource_limits.plugin_output_bytes, "JULIA_RECEIPT_SIZE")
        value = strict_json_bytes(raw.strip(), max_bytes=run.contracts.policy.resource_limits.plugin_output_bytes)
    required = {"schema_id", "verifier_id", "computation_id", "candidate_hash", "output_value_hashes", "shared_physics_routines", "arbitrary_code_from_candidate_executed", "scientific_promotion"}
    require(set(value) == required and value["schema_id"] == "JuliaIndependentEvidenceV1" and value["scientific_promotion"] is False, "JULIA_EVIDENCE_SCHEMA")
    evidence = JuliaEvidenceV1(value["verifier_id"], value["computation_id"], value["candidate_hash"], dict(value["output_value_hashes"]), value["shared_physics_routines"], value["arbitrary_code_from_candidate_executed"], value)
    require(evidence.computation_id == run.request.computation_id and evidence.candidate_hash == run.candidate.candidate_hash, "JULIA_EVIDENCE_BINDING")
    return evidence


def run_lean_certificate_checker(run: EvaluatedRunV1) -> LeanEvidenceV1:
    require(LEAN_CHECKER.is_file(), "LEAN_CHECKER_NOT_BUILT", detail=str(LEAN_CHECKER))
    with tempfile.TemporaryDirectory(prefix="vpc-lean-") as directory:
        path = Path(directory) / "runtime_certificate.json"
        path.write_bytes(canonical_bytes(run.certificate.to_dict()))
        certificate_file_sha256 = file_sha256(path)
        process = subprocess.run([str(LEAN_CHECKER), str(path), certificate_file_sha256, run.certificate.certificate_hash], capture_output=True, timeout=run.contracts.policy.resource_limits.trusted_route_seconds)
        stdout = process.stdout.decode("utf-8", "strict").strip()
        expected = f"ACCEPTED {run.certificate.certificate_hash} FILE_SHA256 {certificate_file_sha256} SCIENTIFIC_PROMOTION_FALSE"
        require(process.returncode == 0 and stdout == expected, "LEAN_CERTIFICATE_REJECTED", detail=process.stderr.decode("utf-8", "replace")[-2000:])
    payload = {"schema_id": "LeanRuntimeCertificateEvidenceV1", "verifier_id": run.contracts.policy.lean_verifier, "accepted_certificate_hash": run.certificate.certificate_hash, "certificate_file_sha256": certificate_file_sha256, "checker_output": stdout, "scientific_promotion": False}
    return LeanEvidenceV1(run.contracts.policy.lean_verifier, run.certificate.certificate_hash, payload)


def run_julia_numerical_control(kind: str, specification: dict[str, Any], *, timeout: int = 1_800) -> dict[str, Any]:
    require(kind in {"interval", "ode", "qmc", "covariance"} and JULIA_NUMERICS_SCRIPT.is_file(), "JULIA_NUMERICAL_CONTROL_KIND")
    with tempfile.TemporaryDirectory(prefix="vpc-julia-numeric-") as directory:
        path = Path(directory) / "specification.json"
        path.write_bytes(canonical_bytes(specification))
        environment = dict(os.environ)
        environment.update({"JULIA_PKG_OFFLINE": "true", "JULIA_HISTORY": str(Path(directory) / "julia_history")})
        command = [str(_julia_executable()), "--startup-file=no", f"--project={JULIA_PROJECT}", str(JULIA_NUMERICS_SCRIPT), kind, str(path)]
        process = subprocess.run(command, capture_output=True, timeout=timeout, env=environment)
        require(process.returncode == 0, "JULIA_NUMERICAL_CONTROL_REJECTED", detail=process.stderr.decode("utf-8", "replace")[-2000:])
        value = strict_json_bytes(process.stdout.strip(), max_bytes=10 * 1024 * 1024)
    require(value.get("scientific_promotion") is False, "NUMERICAL_SCIENTIFIC_PROMOTION")
    return value


def crosscheck_ode(specification: dict[str, Any]) -> dict[str, Any]:
    from .numerics import solve_declarative_ode
    python = solve_declarative_ode(specification)
    julia = run_julia_numerical_control("ode", specification)
    left = [float.fromhex(item) for item in python["final_state_hex"]]
    right = [float(item) for item in julia["final_state"]]
    tolerance = max(float(specification["atol"]) * 20, float(specification["rtol"]) * 20 * max([1.0, *map(abs, left), *map(abs, right)]))
    require(len(left) == len(right) and max(abs(a - b) for a, b in zip(left, right)) <= tolerance, "ODE_CROSSCHECK_MISMATCH")
    return {"schema_id": "NumericalCrosscheckReceiptV1", "verification_class": "CROSSCHECKED_NUMERICAL", "system_kind": specification["system_kind"], "specification_hash": python["specification_hash"], "python": python, "julia": julia, "acceptance_tolerance": format(tolerance, ".17g"), "rigorous_enclosure": False, "scientific_promotion": False}


def crosscheck_interval(certificate: dict[str, Any]) -> dict[str, Any]:
    from .numerics import evaluate_interval_certificate
    python = evaluate_interval_certificate(certificate)
    julia = run_julia_numerical_control("interval", certificate)
    require(python["certificate_hash"] == julia["certificate_hash"] and python["enclosure"] == julia["enclosure"], "INTERVAL_CROSSCHECK_MISMATCH")
    return {"schema_id": "EnclosureCrosscheckReceiptV1", "verification_class": "VERIFIED_ENCLOSURE", "certificate_hash": python["certificate_hash"], "enclosure": python["enclosure"], "python_checker": python, "julia_checker": julia, "guarantee": python["guarantee"], "scientific_promotion": False}


def crosscheck_qmc(specification: dict[str, Any]) -> dict[str, Any]:
    from .numerics import qmc_ensemble
    python = qmc_ensemble(specification)
    julia = run_julia_numerical_control("qmc", specification)
    require(python["generated_input_set_sha256"] == julia["generated_input_set_sha256"], "QMC_INPUT_SET_MISMATCH")
    require(abs(float.fromhex(python["mean_hex"]) - float(julia["mean"])) <= 1e-14, "QMC_MEAN_MISMATCH")
    return {"schema_id": "NumericalCrosscheckReceiptV1", "verification_class": "CROSSCHECKED_NUMERICAL", "semantics": "SAMPLED_DISTRIBUTION_ESTIMATE", "specification_hash": python["specification_hash"], "generated_input_set_sha256": python["generated_input_set_sha256"], "python": python, "julia": julia, "rigorous_enclosure": False, "scientific_promotion": False}


def crosscheck_covariance(specification: dict[str, Any]) -> dict[str, Any]:
    from .numerics import covariance_propagation
    python = covariance_propagation(specification)
    julia = run_julia_numerical_control("covariance", specification)
    python_jacobian = [[float.fromhex(value) for value in row] for row in python["jacobian_hex"]]
    julia_jacobian = [[float(value) for value in row] for row in julia["jacobian"]]
    require(len(python_jacobian) == len(julia_jacobian) and all(len(a) == len(b) and all(abs(x - y) <= 1e-7 * max(1.0, abs(x), abs(y)) for x, y in zip(a, b)) for a, b in zip(python_jacobian, julia_jacobian)), "COVARIANCE_JACOBIAN_MISMATCH")
    return {"schema_id": "NumericalCrosscheckReceiptV1", "verification_class": "CROSSCHECKED_NUMERICAL", "semantics": "LOCAL_LINEAR_COVARIANCE", "specification_hash": python["specification_hash"], "python": python, "julia": julia, "rigorous_enclosure": False, "scientific_promotion": False}
