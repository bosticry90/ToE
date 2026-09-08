"""Untrusted C03/RV proposal adapted to the v6 complete type contract."""
from __future__ import annotations

from pathlib import Path
from typing import Any

from formal.python.toe.generic_runner import verified_calculator_c03_rv_candidate_v1 as v1
from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import verification_policy_v2
from formal.python.toe.generic_runner.verified_calculator.c03_rv_type_contracts import trusted_value_type
from formal.python.toe.generic_runner.verified_calculator.contracts import CalculationRequestV1, CandidatePacketV1


def candidate(root: Path = v1.normalization.ROOT) -> tuple[Any, Any, CalculationRequestV1, CandidatePacketV1]:
    profile, _, old_request, old_packet = v1.candidate(root)
    policy = verification_policy_v2()
    request = CalculationRequestV1(
        profile.contract_hash, policy.contract_hash, old_request.inputs,
        old_request.requested_roots, old_request.execution_budgets,
        old_request.stochastic_experiments,
    )
    graph = {
        "nodes": [
            {**dict(row), "value_type": trusted_value_type(row["node_id"])}
            for row in old_packet.graph["nodes"]
        ],
        "edges": [list(row) for row in old_packet.graph["edges"]],
    }
    packet = CandidatePacketV1(
        request.computation_id,
        {**old_packet.producer, "producer_id": "C03_RV_PRESERVED_INDEPENDENT_CHECKER_PROPOSAL_v2_D02"},
        graph, old_packet.claimed_outputs, old_packet.source_bindings,
        {**(old_packet.generator_provenance or {}), "amendment": "D02_COMPLETE_VALUE_TYPE_DECLARATIONS"},
    )
    return profile, policy, request, packet
