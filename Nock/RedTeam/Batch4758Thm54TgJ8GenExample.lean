/-
  Nock/RedTeam/Batch4758Thm54TgJ8GenExample.lean

  The general J-8 tracegen `genJ8`
  (B4755-4757), run on the example `*[[0 0] [0 1]]` with the empty registry and fuel `1`, returns exactly the
  example's checker input `Example.honest χ` at every coin vector `χ` (kernel-checked; the input's chips are the proved
  fills B4750-B4754).  So `nockvm-j8check --prog example` and the default `nockvm-j8check check` check the same
  object.  Native verdicts on other programs are not kernel-checked here.
-/
import Nock.V1J8.GenExample

namespace Nock.RedTeam.Batch4758

open Nock.V1J8.Exe
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base (s0 f0 R0)

theorem gen_example (χ : CoinsE) : Nock.V1J8.Gen.genJ8 R0 1 s0 f0 χ = some (Nock.V1J8.Example.honest χ) :=
  Nock.V1J8.GenEx.genJ8_example χ

#print axioms Nock.V1J8.GenEx.genJ8_example
#print axioms gen_example

end Nock.RedTeam.Batch4758
