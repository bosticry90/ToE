"""Command-line interface for the verified calculator trusted package."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shlex
import sys

from .api import evaluate_candidate, inspect_receipt, load_contract_set, replay_evidence, run_challenges, verify_run
from .canonical import canonical_json, strict_json_file
from .contracts import CalculationRequestV1, CandidatePacketV1
from .errors import CalculatorError
from .plugin import run_unsafe_plugin


def _contracts(arguments) -> tuple:
    contracts = load_contract_set(Path(arguments.profile), Path(arguments.policy), Path(arguments.source_root))
    request = CalculationRequestV1.from_dict(strict_json_file(Path(arguments.request)))
    candidate = CandidatePacketV1.from_dict(strict_json_file(Path(arguments.candidate)))
    return contracts, request, candidate


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="verified-calculator", description="Declarative verified physics calculator v1")
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("run", "verify", "challenge"):
        sub = commands.add_parser(name)
        sub.add_argument("--profile", required=True); sub.add_argument("--policy", required=True)
        sub.add_argument("--source-root", required=True); sub.add_argument("--request", required=True); sub.add_argument("--candidate", required=True)
        if name in ("verify", "challenge"):
            sub.add_argument("--challenge-specs", required=True)
    inspect = commands.add_parser("inspect"); inspect.add_argument("receipt")
    replay = commands.add_parser("replay"); replay.add_argument("bundle")
    freeze = commands.add_parser("freeze"); freeze.add_argument("bundle"); freeze.add_argument("--destination", required=True)
    authority = commands.add_parser("attach-authority"); authority.add_argument("receipt"); authority.add_argument("binding")
    plugin = commands.add_parser("plugin-run")
    plugin.add_argument("--unsafe-allow-arbitrary-code", action="store_true", required=True)
    plugin.add_argument("--input", required=True); plugin.add_argument("plugin_command", nargs=argparse.REMAINDER)
    return parser


def main(argv: list[str] | None = None) -> int:
    arguments = _parser().parse_args(argv)
    try:
        if arguments.command in {"run", "verify", "challenge"}:
            contracts, request, candidate = _contracts(arguments)
            run = evaluate_candidate(contracts, request, candidate)
            if arguments.command == "run":
                output = {"execution_status": "SUCCEEDED", "computation_id": request.computation_id, "candidate_hash": candidate.candidate_hash, "graph_hash": run.evaluation.graph_hash, "outputs": run.evaluation.output_data(), "runtime_certificate": run.certificate.to_dict(), "limitations": ["This command alone does not confer VERIFIED_EXACT; Julia, Lean, and mandatory challenges remain required."]}
            else:
                from .challenges import ChallengeSpecV1
                registry = strict_json_file(Path(arguments.challenge_specs))
                specs = tuple(ChallengeSpecV1.from_dict(row) for row in registry["challenge_specs"])
                results = run_challenges(run, specs)
                if arguments.command == "challenge":
                    output = {"challenge_results": [row.to_dict() for row in results]}
                else:
                    from .independent import run_julia_independent, run_lean_certificate_checker
                    receipt = verify_run(run, challenge_results=results, challenge_specs=specs, julia_evidence=run_julia_independent(run), lean_evidence=run_lean_certificate_checker(run))
                    output = receipt.to_dict()
        elif arguments.command == "inspect":
            from .evidence import VerificationReceiptV1
            output = inspect_receipt(VerificationReceiptV1.from_dict(strict_json_file(Path(arguments.receipt), max_bytes=256 * 1024 * 1024)))
        elif arguments.command == "replay":
            output = replay_evidence(Path(arguments.bundle))
        elif arguments.command == "plugin-run":
            command = arguments.plugin_command
            if command and command[0] == "--": command = command[1:]
            candidate, provenance = run_unsafe_plugin(command, input_packet=Path(arguments.input).read_bytes(), unsafe_allow_arbitrary_code=arguments.unsafe_allow_arbitrary_code)
            output = {"candidate": candidate.to_dict(), "plugin_provenance": provenance}
        elif arguments.command == "freeze":
            from .evidence import FrozenEvidenceBundleV1, freeze_bundle
            value = strict_json_file(Path(arguments.bundle), max_bytes=256 * 1024 * 1024)
            bundle = FrozenEvidenceBundleV1.from_dict(value)
            path = freeze_bundle(bundle, Path(arguments.destination))
            output = {"bundle_hash": bundle.bundle_hash, "path": str(path)}
        elif arguments.command == "attach-authority":
            from .contracts import ScientificAuthorityBindingV1
            from .evidence import VerificationReceiptV1, attach_authority
            receipt = VerificationReceiptV1.from_dict(strict_json_file(Path(arguments.receipt), max_bytes=256 * 1024 * 1024))
            binding = ScientificAuthorityBindingV1.from_dict(strict_json_file(Path(arguments.binding)))
            output = attach_authority(receipt, binding).to_dict()
        else:
            raise CalculatorError("COMMAND_NOT_IMPLEMENTED")
        sys.stdout.write(canonical_json(output) + "\n")
        return 0
    except CalculatorError as exc:
        sys.stderr.write(canonical_json({"execution_status": "REJECTED", "error_code": exc.code, "location": exc.location, "detail": exc.detail}) + "\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
