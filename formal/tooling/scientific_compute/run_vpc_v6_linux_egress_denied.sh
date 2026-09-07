#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 4 ]]; then
  echo "usage: $0 TESTED_ROOT OUTPUT_DIRECTORY WINDOWS_REFERENCE_BUNDLE PAYLOAD_LEDGER_SEED" >&2
  exit 64
fi

tested_root=$(realpath "$1")
output_directory=$(realpath -m "$2")
windows_reference_bundle=$(realpath "$3")
payload_ledger_seed=$(realpath "$4")
attempt_id="VPC_C03_RV_EXACT_V6_3307E355_LINUX_EGRESS_DENIED_${GITHUB_RUN_ID:-LOCAL}_${GITHUB_RUN_ATTEMPT:-0}"
stage="ENTER_NETWORK_NAMESPACE"
disposition="FAIL"
mkdir -p "$output_directory"

finish() {
  local exit_code=$?
  export VPC_FINISH_EXIT_CODE="$exit_code"
  export VPC_FINISH_STAGE="$stage"
  export VPC_FINISH_DISPOSITION="$disposition"
  export VPC_FINISH_ATTEMPT_ID="$attempt_id"
  export VPC_FINISH_OUTPUT="$output_directory"
  python - <<'PY'
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path

root = Path(os.environ["VPC_FINISH_OUTPUT"])
files = []
for path in sorted(root.glob("**/*")):
    if path.is_file() and path.name != "outcome.json":
        files.append({
            "path": path.relative_to(root).as_posix(),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "bytes": path.stat().st_size,
        })
outcome = {
    "schema_id": "VerifiedCalculatorLinuxEgressDeniedOutcomeV6",
    "attempt_id": os.environ["VPC_FINISH_ATTEMPT_ID"],
    "completed_at_utc": datetime.now(timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z"),
    "disposition": os.environ["VPC_FINISH_DISPOSITION"],
    "terminal_stage": os.environ["VPC_FINISH_STAGE"],
    "exit_code": int(os.environ["VPC_FINISH_EXIT_CODE"]),
    "evidence_files": files,
    "scientific_promotion": False,
    "product_v1_release": False,
    "production_activation": False,
}
(root / "outcome.json").write_text(json.dumps(outcome, sort_keys=True, separators=(",", ":")), encoding="utf-8")
PY
}
trap finish EXIT

stage="ISOLATION_STATE_BEFORE_EXECUTION"
printf '%s\n' "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" > "$output_directory/network_isolation_started_at_utc.txt"
ip link set lo up
ip -j address show > "$output_directory/interfaces_before.json"
ip -j -4 route show table all > "$output_directory/routes_ipv4_before.json"
ip -j -6 route show table all > "$output_directory/routes_ipv6_before.json"
export VPC_NETWORK_EVIDENCE_DIRECTORY="$output_directory"
python - <<'PY' > "$output_directory/network_boundary_before.json"
import json
import os
from pathlib import Path
import socket

root = Path(os.environ["VPC_NETWORK_EVIDENCE_DIRECTORY"])
interfaces = json.loads((root / "interfaces_before.json").read_text(encoding="utf-8"))
ipv4_routes = json.loads((root / "routes_ipv4_before.json").read_text(encoding="utf-8"))
ipv6_routes = json.loads((root / "routes_ipv6_before.json").read_text(encoding="utf-8"))
interface_names = sorted(row["ifname"] for row in interfaces)
no_default_ipv4 = all(row.get("dst") != "default" for row in ipv4_routes)
no_default_ipv6 = all(row.get("dst") != "default" for row in ipv6_routes)
probes = []
for family, address in ((socket.AF_INET, "1.1.1.1"), (socket.AF_INET6, "2606:4700:4700::1111")):
    sock = socket.socket(family, socket.SOCK_STREAM)
    sock.settimeout(3.0)
    try:
        sock.connect((address, 443))
        probes.append({"family": family, "address": address, "result": "CONNECTED__FAIL"})
    except OSError as exc:
        probes.append({"family": family, "address": address, "result": "EGRESS_DENIED", "error": type(exc).__name__, "errno": exc.errno})
    finally:
        sock.close()
result = {
    "interface_names": interface_names,
    "loopback_only": interface_names == ["lo"],
    "no_default_ipv4_route": no_default_ipv4,
    "no_default_ipv6_route": no_default_ipv6,
    "active_probes": probes,
}
print(json.dumps(result, sort_keys=True, separators=(",", ":")))
if not (result["loopback_only"] and no_default_ipv4 and no_default_ipv6 and all(row["result"] == "EGRESS_DENIED" for row in probes)):
    raise SystemExit(1)
PY

stage="TRUSTED_270_TEST_CLOSURE"
cd "$tested_root"
test_roots=(
  formal/python/tests/test_verified_calculator_v1.py
  formal/python/tests/test_typed_provenance_kernel_v1.py
  formal/python/tests/test_runner_provenance_verifier_v4.py
  formal/python/tests/test_c03_normalization_v1.py
  formal/python/tests/test_seven_record_source_candidate_v4.py
  formal/python/tests/test_rv_source_derivation_v2.py
  formal/python/tests/test_c03_physical_dag_v1.py
  formal/python/tests/test_verified_calculator_v6_repairs.py
)
python -m pytest "${test_roots[@]}" --junitxml="$output_directory/pytest.xml" > "$output_directory/pytest.log" 2>&1

stage="TRUSTED_EXACT_QUALIFICATION"
freeze_directory="$tested_root/formal/output/vpc_v6_linux_bundle_${GITHUB_RUN_ID:-local}_${GITHUB_RUN_ATTEMPT:-0}"
python -m formal.python.toe.generic_runner.verified_calculator_c03_rv_qualification_v2 \
  --freeze-directory "$freeze_directory" > "$output_directory/qualification.json" 2> "$output_directory/qualification.stderr.log"
export VPC_QUALIFICATION_SUMMARY="$output_directory/qualification.json"
export VPC_TESTED_ROOT="$tested_root"
linux_bundle=$(python - <<'PY'
import json
import os
from pathlib import Path
summary = json.loads(Path(os.environ["VPC_QUALIFICATION_SUMMARY"]).read_text(encoding="utf-8"))
required = {
    "computation_id": "20a479ef428a9f079b7ea0c3b5506689383e26d2242579180777489818bbaeb8",
    "graph_hash": "ddf90176934cb018775ef7bb78ce8f5516fce40afbe7b4ed491e6116f4b46801",
    "runtime_certificate_hash": "401d6aa6f502c751113931975d222f261d59849897b7e24e9e504404dfa88502",
    "lean_qualification_envelope_hash": "ad7aef9e7039ce0412c782368c3c6c1d2a678ead68c7c1e4c3be26ebd2d1ca4c",
    "dependency_closure_hash": "a01b60485d9b9fcdd3b7307af16204d735abf1ee8ef9cff9177b77fc6773d058",
    "replay_status": "MATCHED",
    "source_node_count": 31,
    "derived_node_count": 160,
    "output_root_count": 16,
    "type_signature_receipt_count": 207,
    "trusted_physics_operation_count": 19,
    "challenge_result_count": 373,
}
for key, value in required.items():
    if summary.get(key) != value:
        raise SystemExit(f"QUALIFICATION_IDENTITY_MISMATCH:{key}:{summary.get(key)!r}:{value!r}")
if any(summary.get(key) is not False for key in ("scientific_promotion", "product_v1_release", "production_activation")):
    raise SystemExit("QUALIFICATION_PROMOTION_FLAG")
print((Path(os.environ["VPC_TESTED_ROOT"]) / summary["frozen_bundle_path"]).resolve())
PY
)
cp "$linux_bundle" "$output_directory/linux_bundle.json"

stage="DETERMINISTIC_REPLAY_A"
export VPC_LINUX_BUNDLE="$output_directory/linux_bundle.json"
python - <<'PY' > "$output_directory/replay_a.json"
import json
import os
from pathlib import Path
from formal.python.toe.generic_runner.verified_calculator import api
print(json.dumps(api.replay_evidence(Path(os.environ["VPC_LINUX_BUNDLE"])), sort_keys=True, separators=(",", ":")))
PY
grep -q '"replay_status":"MATCHED"' "$output_directory/replay_a.json"

stage="DETERMINISTIC_REPLAY_B"
python - <<'PY' > "$output_directory/replay_b.json"
import json
import os
from pathlib import Path
from formal.python.toe.generic_runner.verified_calculator import api
print(json.dumps(api.replay_evidence(Path(os.environ["VPC_LINUX_BUNDLE"])), sort_keys=True, separators=(",", ":")))
PY
grep -q '"replay_status":"MATCHED"' "$output_directory/replay_b.json"

stage="LINUX_DEPENDENCY_CLOSURE"
python - <<'PY' > "$output_directory/linux_dependency_closure.json"
import json
import os
from pathlib import Path
bundle = json.loads(Path(os.environ["VPC_LINUX_BUNDLE"]).read_text(encoding="utf-8"))
if len(bundle["dependency_manifests"]) != 1:
    raise SystemExit("DEPENDENCY_MANIFEST_CENSUS")
print(json.dumps(bundle["dependency_manifests"][0], sort_keys=True, separators=(",", ":")))
PY

stage="D07_D01_D02_PEER_ACCEPTANCE"
python formal/python/tools/run_vpc_v6_repair_acceptance.py \
  --repo-root "$tested_root" \
  --bundle "$windows_reference_bundle" \
  --peer-closure "$output_directory/linux_dependency_closure.json" \
  --output "$output_directory/repair_acceptance.json" \
  --attempt-id "$attempt_id" > "$output_directory/repair_acceptance.stdout.log" 2> "$output_directory/repair_acceptance.stderr.log"
grep -q '"status": "PASS"' "$output_directory/repair_acceptance.stdout.log"

stage="WINDOWS_LINUX_643_ROW_SCIENTIFIC_COMPARISON"
python formal/python/tools/compare_vpc_v6_payload.py \
  --seed "$payload_ledger_seed" \
  --reference "$windows_reference_bundle" \
  --amended "$output_directory/linux_bundle.json" \
  --output "$output_directory/windows_linux_payload_equivalence.json" \
  --attempt-id "$attempt_id" > "$output_directory/windows_linux_payload_equivalence.stdout.log" 2> "$output_directory/windows_linux_payload_equivalence.stderr.log"
grep -q '"status": "PASS"' "$output_directory/windows_linux_payload_equivalence.stdout.log"
grep -q '"MATCH": 643' "$output_directory/windows_linux_payload_equivalence.stdout.log"

stage="ISOLATION_STATE_AFTER_EXECUTION"
ip -j address show > "$output_directory/interfaces_after.json"
ip -j -4 route show table all > "$output_directory/routes_ipv4_after.json"
ip -j -6 route show table all > "$output_directory/routes_ipv6_after.json"
python - <<'PY' > "$output_directory/network_boundary_after.json"
import json
import os
from pathlib import Path
import socket

root = Path(os.environ["VPC_NETWORK_EVIDENCE_DIRECTORY"])
interfaces = json.loads((root / "interfaces_after.json").read_text(encoding="utf-8"))
ipv4_routes = json.loads((root / "routes_ipv4_after.json").read_text(encoding="utf-8"))
ipv6_routes = json.loads((root / "routes_ipv6_after.json").read_text(encoding="utf-8"))
interface_names = sorted(row["ifname"] for row in interfaces)
no_default_ipv4 = all(row.get("dst") != "default" for row in ipv4_routes)
no_default_ipv6 = all(row.get("dst") != "default" for row in ipv6_routes)
probes = []
for family, address in ((socket.AF_INET, "1.1.1.1"), (socket.AF_INET6, "2606:4700:4700::1111")):
    sock = socket.socket(family, socket.SOCK_STREAM)
    sock.settimeout(3.0)
    try:
        sock.connect((address, 443))
        probes.append({"family": family, "address": address, "result": "CONNECTED__FAIL"})
    except OSError as exc:
        probes.append({"family": family, "address": address, "result": "EGRESS_DENIED", "error": type(exc).__name__, "errno": exc.errno})
    finally:
        sock.close()
result = {
    "interface_names": interface_names,
    "loopback_only": interface_names == ["lo"],
    "no_default_ipv4_route": no_default_ipv4,
    "no_default_ipv6_route": no_default_ipv6,
    "active_probes": probes,
}
print(json.dumps(result, sort_keys=True, separators=(",", ":")))
if not (result["loopback_only"] and no_default_ipv4 and no_default_ipv6 and all(row["result"] == "EGRESS_DENIED" for row in probes)):
    raise SystemExit(1)
PY

stage="COMPLETE"
disposition="PASS"
