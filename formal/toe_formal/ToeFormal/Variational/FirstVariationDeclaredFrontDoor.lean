/-
ToeFormal/Variational/FirstVariationDeclaredFrontDoor.lean

Front door for first-variation uniqueness on the representation quotient.

Policy:
- Import this module (not `FirstVariationDeclared.lean`) for the default
  EL/uniqueness route.
- This module re-exports only the quotient-lane symbols.
- The legacy Field2D lane remains available but is non-critical.
-/

import Mathlib
import ToeFormal.Variational.FirstVariationDeclaredFieldRep
