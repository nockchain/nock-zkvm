import Lean
import Nock.RedTeam.Batch332Thm54ZModLiterals
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesHostile

/-
  Nock/RedTeam/Batch1570Thm54ZeroBinderDot.lean

  Field `ZMod 769`, `K = GaloisField 769 3` (`768 = 3 * 2^8`, `h = 8`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch1570

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.RedTeam

abbrev DF := DotConfig769.F
abbrev DK := DotConfig769.K

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK
local instance : Fact (Nat.Prime 769) := ⟨by norm_num⟩
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

noncomputable section

/-- `nockCompilesHostile` at the dot product, `ZMod 769`, `Λ = 22`. -/
noncomputable def b1570_dot_hostile :=
  nockCompilesHostile (p := 769) (K := DK)
    DotConfig769.alphaA DotConfig769.alphaA MemoryTable.formRDefault
    Batch327.b327_dot_run Batch332.b332_dot_bound
    Batch263.b263_subject_bounded Batch263.b263_formula_bounded
    (by
      rw [Batch332.b332_dot_rom]
      exact Nat.lt_of_le_of_lt
        (leafBound_of_traceConfined Batch180.dot_air_traceConfined)
        (by
          have h := Batch327.b327_dot_hΛp
          simpa [DotConfig769.ringChar_K] using h))
    (by norm_num)
    (by norm_num)
    DotConfig769.finrank_cubic
    (by
      have h := Batch327.b327_dot_hF_orbit
      simpa [ZMod.card] using h)
    ⟨Batch327.b327_dot_hwin', Batch327.b327_dot_hmemOrd'⟩
    (by
      have h := Batch327.b327_dot_hKsz'
      simpa [DotConfig769.ringChar_K] using h)

end

end Nock.RedTeam.Batch1570

open Lean Elab Command Meta

namespace Batch1570BinderWalk

def explicitBinders (n : Name) : MetaM Nat := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    let mut e := 0
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo == .default then e := e + 1
    return e

run_cmd do
  for n in [``Nock.RedTeam.Batch1570.b1570_dot_hostile] do
    let e ← liftTermElabM (explicitBinders n)
    unless e == 0 do throwError m!"{n}: {e} explicit binders, expected 0"
    logInfo m!"BINDER-WALK {n}: 0 explicit binders"

end Batch1570BinderWalk

#print axioms Nock.RedTeam.Batch1570.b1570_dot_hostile
