/-
AD-00 — Admissibility manifest (Lean-authored literal).

Purpose
- Provide a Lean-owned declaration of which gate suites are enabled.
- Python tooling may *consume* this literal to build a tracked-hashes manifest,
  but Python should not be the author of enable/disable truth.

Notes
- This is intentionally minimal: we are not running Lean to emit JSON yet.
  The immediate step is making the enable/disable source live in a Lean file.
- The JSON block is parsed by tooling between BEGIN/END markers.
- Keep this JSON small and stable; tracked file hashes live in the Python-built
  manifest under formal/markdown locks/gates/admissibility_manifest.json.
-/

namespace ToeFormal
namespace Constraints

/- BEGIN_ADMISSIBILITY_MANIFEST_JSON
{
  "version": 1,
  "gates": {
    "CT01": {"enabled": false},
    "SYM01": {"enabled": false},
    "CAUS01": {"enabled": false}
  }
}
END_ADMISSIBILITY_MANIFEST_JSON -/

end Constraints
end ToeFormal

namespace ToeFormal
namespace Gates

/-- Lean-authored default enablement policy for admissibility gates.

This is intentionally conservative: presence of Lean files does not imply enablement.
Actual enforcement remains in the Python admissibility manifest consumed by tooling.
-/
def defaultEnabled : List String := []
def defaultEnabled : List String := ["CT01", "SYM01", "CAUS01"]
def defaultEnabled : List String := []

end Gates
end ToeFormal
