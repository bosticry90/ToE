"""Explicitly unsafe candidate-only plugin execution."""
from __future__ import annotations

from pathlib import Path
import subprocess
import threading
from typing import Sequence

from .canonical import strict_json_bytes
from .contracts import CandidatePacketV1, ResourceLimitsV1
from .errors import CalculatorError, require


UNSAFE_PLUGIN_WARNING = (
    "Arbitrary plugin code is not sandboxed and may access files, processes, or "
    "other resources available to the current operating-system account."
)


def run_unsafe_plugin(
    command: Sequence[str],
    *,
    input_packet: bytes,
    unsafe_allow_arbitrary_code: bool,
    limits: ResourceLimitsV1 | None = None,
) -> tuple[CandidatePacketV1, dict]:
    limits = limits or ResourceLimitsV1()
    require(unsafe_allow_arbitrary_code is True, "UNSAFE_PLUGIN_FLAG_REQUIRED")
    require(command and all(isinstance(item, str) and item for item in command), "PLUGIN_COMMAND")
    require(len(input_packet) <= limits.bundle_bytes, "BUNDLE_SIZE_LIMIT")
    process = subprocess.Popen(list(command), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    chunks: dict[str, list[bytes]] = {"stdout": [], "stderr": []}
    state = {"bytes": 0, "exceeded": False}
    lock = threading.Lock()

    def drain(name: str, stream) -> None:
        while True:
            chunk = stream.read(64 * 1024)
            if not chunk:
                return
            with lock:
                state["bytes"] += len(chunk)
                if state["bytes"] > limits.plugin_output_bytes:
                    state["exceeded"] = True
                    process.kill()
                    return
                chunks[name].append(chunk)

    readers = tuple(threading.Thread(target=drain, args=(name, stream), daemon=True) for name, stream in (("stdout", process.stdout), ("stderr", process.stderr)))
    for reader in readers:
        reader.start()
    try:
        assert process.stdin is not None
        process.stdin.write(input_packet)
        process.stdin.close()
        process.wait(timeout=limits.plugin_seconds)
    except subprocess.TimeoutExpired as exc:
        process.kill()
        process.wait()
        raise CalculatorError("PLUGIN_TIMEOUT") from exc
    finally:
        for reader in readers:
            reader.join(timeout=5)
    require(not state["exceeded"], "PLUGIN_OUTPUT_LIMIT")
    stdout, stderr = b"".join(chunks["stdout"]), b"".join(chunks["stderr"])
    require(process.returncode == 0, "PLUGIN_NONZERO_EXIT", detail=str(process.returncode))
    value = strict_json_bytes(stdout, max_bytes=limits.plugin_output_bytes, max_depth=limits.json_depth, max_string_bytes=limits.string_bytes, max_container_members=limits.container_members)
    candidate = CandidatePacketV1.from_dict(value)
    provenance = {
        "execution_class": "UNSAFE_ARBITRARY_CODE_CANDIDATE_ONLY",
        "warning": UNSAFE_PLUGIN_WARNING,
        "command_executable": str(Path(command[0])),
        "exit_code": process.returncode,
        "stderr_present": bool(stderr),
        "trusted_receipt_emitted": False,
    }
    return candidate, provenance
