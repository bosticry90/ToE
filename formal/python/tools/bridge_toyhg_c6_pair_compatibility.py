from __future__ import annotations

"""Toy-H/Toy-G joint pair-compatibility functional (quarantine-safe)."""


def evaluate_toyhg_c6_pair_compatibility(
    *,
    toyh_phase_bridge_pass: bool,
    toyh_current_bridge_pass: bool,
    toyg_bridge_pass: bool,
    toyh_phase_reason: str = "",
    toyh_current_reason: str = "",
    toyg_reason: str = "",
) -> dict:
    phase_pass = bool(toyh_phase_bridge_pass)
    current_pass = bool(toyh_current_bridge_pass)
    toyg_pass = bool(toyg_bridge_pass)

    status_vector = [
        "P" if phase_pass else "F",
        "P" if current_pass else "F",
        "P" if toyg_pass else "F",
    ]
    signature = "-".join(status_vector)

    admissible = len({phase_pass, current_pass, toyg_pass}) == 1

    if admissible:
        reason = "PASS_PAIR_COMPATIBLE"
        localization = "none"
    elif phase_pass == current_pass and phase_pass != toyg_pass:
        reason = "FAIL_PAIR_TOYG_MISMATCH"
        localization = "toyg_bridge_channel"
    elif phase_pass == toyg_pass and phase_pass != current_pass:
        reason = "FAIL_PAIR_CURRENT_MISMATCH"
        localization = "toyh_current_channel"
    elif current_pass == toyg_pass and current_pass != phase_pass:
        reason = "FAIL_PAIR_PHASE_MISMATCH"
        localization = "toyh_phase_channel"
    else:
        reason = "FAIL_PAIR_MIXED"
        localization = "mixed"

    signed_margin = 0.1 if admissible else -0.1

    return {
        "schema_version": 1,
        "observable_id": "TOYHG_C6_pair_compatibility_v1",
        "inputs": {
            "toyh_phase_bridge_pass": bool(phase_pass),
            "toyh_current_bridge_pass": bool(current_pass),
            "toyg_bridge_pass": bool(toyg_pass),
            "toyh_phase_reason": str(toyh_phase_reason),
            "toyh_current_reason": str(toyh_current_reason),
            "toyg_reason": str(toyg_reason),
        },
        "metrics": {
            "signature": signature,
            "n_pass_channels": int(sum(1 for x in [phase_pass, current_pass, toyg_pass] if x)),
            "n_fail_channels": int(sum(1 for x in [phase_pass, current_pass, toyg_pass] if not x)),
            "signed_margin": float(signed_margin),
        },
        "status": {
            "admissible": bool(admissible),
            "localization_note": localization,
        },
        "reason_code": reason,
    }

