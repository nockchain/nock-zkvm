/-
  `decodeDagR` of the emitted `walkJ8` chip (kernel); with `decodeDagR_eq` it is the `decodeDagL d = some gates` hypothesis of
  `evalDagK_toEx_of_decodeDag`.
-/
import NockvmE2E.Emit.Chips
import NockvmE2E.Emit.TieR

set_option autoImplicit false

namespace NockvmE2E.Emit
open Nock.Emit

theorem decR_walkJ8 : decodeDagR emit_walkJ8 = some walkJ8Spec.gates := by decide +kernel

end NockvmE2E.Emit

#print axioms NockvmE2E.Emit.decR_walkJ8
