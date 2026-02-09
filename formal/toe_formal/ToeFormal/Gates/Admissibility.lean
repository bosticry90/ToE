/-
Aggregates admissibility gates into a single import.
No proofs are provided; this module is only a declaration surface.
-/
import ToeFormal.Gates.CT01
import ToeFormal.Gates.SYM01
import ToeFormal.Gates.CAUS01
import ToeFormal.Gates.RAC

namespace ToeFormal.Gates

-- Stable identifiers for downstream tooling / documentation.
def gateIds : List String := ["CT01", "SYM01", "CAUS01"]

end ToeFormal.Gates
