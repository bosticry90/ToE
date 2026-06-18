import ToeFormal.Derivation.QFTGRScalarSandbox

/-
Thin QFT-GR lane aggregate for tiered validation. At present it exposes the
current scalar-sandbox source-admissibility chain without importing the full
repository-level ToeFormal surface.
-/

namespace ToeFormal
namespace Derivation
namespace QFTGR

def aggregateTargetId : String := "ToeFormal.Derivation.QFTGR"

def scalarSandboxTargetId : String :=
  QFTGRScalarSandbox.aggregateTargetId

def currentScopedResult : String :=
  QFTGRScalarSandbox.currentScopedResult

theorem qft_gr_lane_aggregate_exposes_scalar_sandbox :
    scalarSandboxTargetId = "ToeFormal.Derivation.QFTGRScalarSandbox" ∧
      currentScopedResult =
        "PROVISIONAL_SCALAR_SOURCE_PASSES_LOCAL_SOURCE_ADMISSIBILITY_REVIEW_ON_SHELL_" ++
          "NO_SEMICLASSICAL_OR_TOE_NATIVE_CLOSURE" := by
  decide

end QFTGR
end Derivation
end ToeFormal
