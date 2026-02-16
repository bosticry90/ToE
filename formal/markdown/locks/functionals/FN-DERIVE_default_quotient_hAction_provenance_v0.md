# FN-DERIVE default-quotient hAction provenance v0

Scope / limits
- Structural provenance record only.
- No physics truth claim.
- Does not discharge `hAction`; records where it is supplied on the default path.

Record (deterministic)

```json
{
  "default_wrapper_symbol": "Rep32_cubic_lane_declared_g",
  "module": "formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean",
  "notes": [
    "hAction is an explicit caller-supplied assumption on the default wrapper.",
    "No hidden derivation is permitted for action specialization."
  ],
  "obligation": "hAction : actionRep32.action = actionRep32Cubic declared_g_rep32",
  "schema": "FN-DERIVE/default_quotient_hAction_provenance/v0",
  "source_kind": "assumption_field",
  "source_symbol": "Rep32CubicLaneAssumptions.hAction",
  "status_date": "2026-02-12"
}
```

Record fingerprint: `1d2196de0514cf631041f09eb228d7c0b0f0ae611f2aa1f053120f9ee616f677`
