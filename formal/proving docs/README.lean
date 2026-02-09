/-
ToeFormal/Derivation/Bridges/README.lean

This file is not code-critical; it is a “bridge skeleton” placeholder that will later
contain the precise mapping from derivation-layer operators/symbols to each LOCK module.

Key principle:
- Locks stay authoritative.
- Derivation layer has a single Fourier convention.
- Bridges explicitly state how each lock’s opaque operators map into derivation-layer symbols,
  including any sign flips, truncations, and regime assumptions.
-/

namespace ToeFormal.Derivation.Bridges

/-
TODO (Layer E):
1) Bridge to UCFF/FirstOrder.lean:
   - show: locked residual form ↔ derivation EOM_P1 with an explicit coefficient map.
2) Bridge to UCFF/SecondOrderNumerics.lean:
   - treat lock-fixed ω(k) polynomial as the symbol definition for that module.
3) Bridge to UCFF/SecondOrderTimeDomain.lean:
   - treat lock-fixed ω^2(k) polynomial as the symbol definition for that module.
4) Bridge to CRFT/Geom/AcousticMetric.lean:
   - show it is a representative acoustic metric (up to conformal factor), and state conditions.
-/

end ToeFormal.Derivation.Bridges
