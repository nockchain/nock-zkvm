/-
  Nock/Jet/HoldsNBridge.lean

  **The two `HoldsN` definitions agree.**  J-1 (`Nock/Jet/Semantics.lean`) carries a
  verbatim copy `Nock.Jet.HoldsN` of A-1's `Nock.Atoms.HoldsN`.  Neither definition is changed;
  this module proves they are equal (by `rfl`), so downstream code may use either.
-/
import Nock.Atoms.HoldsN
import Nock.Jet.Semantics

set_option autoImplicit false

namespace Nock.Jet

open Nock.NockVMROM.Thm54

/-- The J-1 copy and the A-1 definition of `HoldsN` are the same predicate. -/
theorem holdsN_eq_atoms : Nock.Jet.HoldsN = Nock.Atoms.HoldsN := rfl

/-- Pointwise form. -/
theorem holdsN_iff_atoms (x : P8PublicClaim) : Nock.Jet.HoldsN x ↔ Nock.Atoms.HoldsN x := Iff.rfl

end Nock.Jet
