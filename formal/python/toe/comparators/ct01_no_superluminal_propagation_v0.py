from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root
from typing import Any, Mapping

import numpy as np


CT01_TOLERANCE_PROFILE_ENV = "TOE_CT01_TOLERANCE_PROFILE"

CT01_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_ct01": 1e-8,
        "eps_break": 1e-3,
        "u_threshold": 1e-3,
    },
    "portable": {
        "eps_ct01": 1e-6,
        "eps_break": 1e-3,
        "u_threshold": 1e-3,
    },
}


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


    return (
        "# CT-01 - No Superluminal Propagation Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted CT-01 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.ct01_no_superluminal_propagation_front_door`\n"
        "- Outputs: `formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_reference_report.json`, "
        "`formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_ct01_no_superluminal_propagation_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
