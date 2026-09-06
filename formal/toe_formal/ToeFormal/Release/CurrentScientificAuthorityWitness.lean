import ToeFormal.Release.CurrentAuthority

namespace ToeFormal
namespace Release
namespace CurrentScientificAuthorityWitness

def targetPrefix : String := "TOE_CURRENT_TARGET="
def authorityPrefix : String := "TOE_CURRENT_AUTHORITY="

def main : IO Unit := do
  IO.println (targetPrefix ++ Derivation.CurrentTarget.currentLiveTarget)
  IO.println (authorityPrefix ++ CurrentAuthority.currentTarget)

end CurrentScientificAuthorityWitness
end Release
end ToeFormal

def main : IO Unit :=
  ToeFormal.Release.CurrentScientificAuthorityWitness.main
