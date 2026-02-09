import Mathlib
import ToeFormal.Constraints.FN01_CandidateMembership

namespace ToeFormal
namespace Constraints
namespace FN01

/-
FN-01 Candidate API (Lean “front door”).

Policy:
- Downstream Lean proofs should import *this* module (not `FN01_CandidateMembership`)
  when they want to reference a specific FN candidate perturbation.

Rationale:
- Keeps the surface area stable: candidate definitions, membership lemmas, and
  per-candidate DR corollaries are re-exported through a single import.
- Paired with the Python enforcement test, this makes Lean-side bypass difficult.
-/

namespace CandidateAPI

-- Re-export the canonical phase action and all candidate definitions / lemmas.
-- (They remain in the `ToeFormal.Constraints.FN01` namespace; this module is the
-- required import surface.)

end CandidateAPI

end FN01
end Constraints
end ToeFormal
