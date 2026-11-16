import Lean
import Nock.RedTeam.Batch332Thm54ZModLiterals
import Nock.RedTeam.Batch1259Thm54HonestNonVacuityConcrete
import Nock.RedTeam.Batch1402Thm54HonestRejectedAtForeignTuple
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesHostile
import Nock.NockVMROM.Thm54.HostileSemanticSoundness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1401Thm54HostileLiterals.lean

  `nockCompilesHostile`
  (`TraceGen/GenNockCompilesHostile.lean`) instantiated at three non-vacuous programs with ZERO explicit
  binders (binder walk below asserts 0):
  * `b1401_matmul_hostile`: the Goldilocks 2×2 matmul (DEMO-SUITE row 16), arguments of
    `Batch332.b332_matmul_from_zmod` verbatim;
  * `b1401_fib_hostile`: Peano-fib, arguments of `Batch332.b332_fib_from_zmod` verbatim;
  * `b1401_f73_hostile`: `Batch1259`'s concrete F73 program `*[0 [1 0]] = 0` at `λ = 0`.
  Plus `b1401_f73_foreign`: definition-of-done item (ii) at the F73 program, zero binders --
  the honest pair is accepted at `honestTuple` and rejected at the foreign IO pole
  (`Batch1402.honest_rejected_at_foreign_ioPole_zmod`).

  Fixed-trace shape only: conjuncts (4)/(5) are about trace pairs fixed before every coin; nothing
  here states or implies `:966` / interactive soundness at the two-message chronology.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch1401

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksOrbit
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K
abbrev DF := DotConfig769.F
abbrev DK := DotConfig769.K
abbrev FF := FibConfigGoldilocks.F
abbrev FK := FibConfigGoldilocks.K

local instance charRingGK : CharP GK (ringChar GK) := ringChar.charP GK
local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK
local instance charRingFK : CharP FK (ringChar FK) := ringChar.charP FK

local instance : Fact (Nat.Prime 769) := ⟨by norm_num⟩

noncomputable local instance : Fintype GK := Fintype.ofFinite _
noncomputable local instance : DecidableEq GK := Classical.decEq _
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _
noncomputable local instance : Fintype FK := Fintype.ofFinite _
noncomputable local instance : DecidableEq FK := Classical.decEq _

noncomputable section

/-! ## Goldilocks 2×2 matmul -/

/-- `nockCompilesHostile` at the Goldilocks 2×2 matmul. -/
noncomputable def b1401_matmul_hostile :=
  nockCompilesHostile (p := Field.p) (K := GK)
    MatmulConfigGoldilocks.alphaA MatmulConfigGoldilocks.alphaA MemoryTable.formRDefault
    Nock.RedTeam.Batch327.b327_mm_run Nock.RedTeam.Batch332.b332_mm_bound
    mmSubject_bounded_p mmFormula_bounded_p
    (by
      change programLeafBound (airReorder (romTree (K := GK)
          (evalGRom_le_evalRom (evalGRom_of_runBounded Nock.RedTeam.Batch327.b327_mm_run Nock.RedTeam.Batch332.b332_mm_bound))))
        < Field.p
      rw [Nock.RedTeam.Batch332.b332_mm_rom]
      exact Nat.lt_of_le_of_lt
        (leafBound_of_traceConfined mm_traceConfined)
        (by simp only [Field.p]; norm_num))
    (by simp only [Field.p]; norm_num)
    (by simp only [Field.p]; norm_num)
    MatmulConfigGoldilocks.finrank_cubic
    (by
      have h := Nock.RedTeam.Batch327.b327_mm_hF_orbit
      simpa [ZMod.card, Field.p] using h)
    ⟨Nock.RedTeam.Batch327.b327_mm_hwin', Nock.RedTeam.Batch327.b327_mm_hmemOrd'⟩
    (by
      have h := Nock.RedTeam.Batch327.b327_mm_hKsz'
      simpa [MatmulConfigGoldilocks.ringChar_K] using h)

/-! ## Peano-fib -/

/-- `nockCompilesHostile` at Peano-fib. -/
noncomputable def b1401_fib_hostile :=
  nockCompilesHostile (p := Field.p) (K := FK)
    FibConfigGoldilocks.alphaA FibConfigGoldilocks.alphaA MemoryTable.formRDefault
    Nock.RedTeam.Batch327.b327_fib_run Nock.RedTeam.Batch332.b332_fib_bound
    fibSubject_bounded_p fibFormula_bounded_p
    (by
      change programLeafBound (airReorder (romTree (K := FK)
          (evalGRom_le_evalRom (evalGRom_of_runBounded Nock.RedTeam.Batch327.b327_fib_run Nock.RedTeam.Batch332.b332_fib_bound))))
        < Field.p
      rw [Nock.RedTeam.Batch332.b332_fib_rom]
      exact Nat.lt_of_le_of_lt
        (leafBound_of_traceConfined fib_traceConfined)
        (by simp only [Field.p]; norm_num))
    (by simp only [Field.p]; norm_num)
    (by simp only [Field.p]; norm_num)
    FibConfigGoldilocks.finrank_cubic
    (by
      have h := Nock.RedTeam.Batch327.b327_fib_hF_orbit
      simpa [ZMod.card, Field.p] using h)
    ⟨Nock.RedTeam.Batch327.b327_fib_hwin', Nock.RedTeam.Batch327.b327_fib_hmemOrd'⟩
    (by
      have h := Nock.RedTeam.Batch327.b327_fib_hKsz'
      simpa [FibConfigGoldilocks.ringChar_K] using h)

/-! ## The concrete F73 program of `Batch1259` -/

open Nock.RedTeam.Batch1259 in
/-- `nockCompilesHostile` at `*[0 [1 0]] = 0` over `ZMod 73`, `K = GaloisField 73 3`, `α = 5`, `λ = 0`. -/
noncomputable def b1401_f73_hostile :=
  nockCompilesHostile (p := 73) (K := K0) α0 α0 (0 : K0) hrun0 hbound0 hs0 hf0
    (hΛp0 _) hp0 hp64_0 hK0 (hF0 _) (hwin0 _) (hKszChar0 _)

open Nock.RedTeam.Batch1259 in
/-- Item (ii) at the F73 program: honest pair accepted at `honestTuple`, rejected at the foreign IO pole. -/
noncomputable def b1401_f73_foreign :=
  Nock.RedTeam.Batch1402.honest_rejected_at_foreign_ioPole_zmod (p := 73) (K := K0) α0 (0 : K0) hrun0
    hbound0 hs0 hf0 (hΛp0 _) hp0 hp64_0 hK0 (hF0 _) (hwin0 _) (hKszChar0 _)

end

end Nock.RedTeam.Batch1401

open Lean Elab Command Meta

namespace Batch1401BinderWalk

def explicitBinders (n : Name) : MetaM Nat := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    let mut e := 0
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo == .default then e := e + 1
    return e

run_cmd do
  for n in [``Nock.RedTeam.Batch1401.b1401_matmul_hostile, ``Nock.RedTeam.Batch1401.b1401_fib_hostile,
      ``Nock.RedTeam.Batch1401.b1401_f73_hostile, ``Nock.RedTeam.Batch1401.b1401_f73_foreign] do
    let e ← liftTermElabM (explicitBinders n)
    unless e == 0 do throwError m!"{n}: {e} explicit binders, expected 0"
    logInfo m!"BINDER-WALK {n}: 0 explicit binders"

end Batch1401BinderWalk

#print axioms Nock.RedTeam.Batch1401.b1401_matmul_hostile
#print axioms Nock.RedTeam.Batch1401.b1401_fib_hostile
#print axioms Nock.RedTeam.Batch1401.b1401_f73_hostile
#print axioms Nock.RedTeam.Batch1401.b1401_f73_foreign
