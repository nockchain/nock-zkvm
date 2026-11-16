/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibInstances.lean

  The two Goldilocks inhabitants of the Peano-fib
  program: `nockCompiles_of_grom_atTree_p62` at the
  literal seed `φ(7^(2^32−1))`, and `nockCompiles_p67` with compiler-chosen
  seed.  Claim is `⟨fibSubject, fibFormula, fibResult⟩` and `fibResult`
  is `evalN`'s result (`fibF3 = 3`, clause 3).  Binder walk: 0 explicit.

  Opcodes the 2×2 matmul does not use: OP2, OP3, OP8.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenFibConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksHbad
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksSeed
import Nock.NockVMROM.Thm54.TraceGen.GenFibTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.Framework.Thm54

local instance charRingFibK : CharP FibConfigGoldilocks.K (ringChar FibConfigGoldilocks.K) :=
  ringChar.charP FibConfigGoldilocks.K

noncomputable local instance : Fintype FibConfigGoldilocks.K := Fintype.ofFinite _
noncomputable local instance : DecidableEq FibConfigGoldilocks.K := Classical.decEq _

noncomputable section

/-- Claimed result is `evalN`'s result (clause 3, `F = 3`). -/
theorem fib_claimed_is_evalN : fibResult = .atom 3 := rfl

theorem fib_evalN : Nock.evalN 32 fibSubject fibFormula = some fibResult :=
  fib_evalN_n4

theorem fib_hΛ : 1 ≤ (42 : ℕ) := by decide

/-- `romTree` of the guarded run is the generated `fibTree`. -/
theorem fib_rom_eq :
    romTree (K := FibConfigGoldilocks.K) (evalGRom_le_evalRom fib_grom) = fibTree (K := FibConfigGoldilocks.K) :=
  (fibTree_eq_of_gen
    (romTree_spec (K := FibConfigGoldilocks.K) (evalGRom_le_evalRom fib_grom))).symm

theorem fib_assign_rows :
    (bfsForest [bfsAssign (airReorder (fibTree (K := FibConfigGoldilocks.K)))]).length = 33 := by
  rw [bfsForest_bfsAssign_length]
  have hsz : (airReorder (fibTree (K := FibConfigGoldilocks.K))).size = 33 := by
    rw [airReorder_size, fibTree_size]
  simp [bfsForest_length, totalSize] at hsz ⊢
  exact hsz

/-- Joint seed budget at 33 AIR-ordered rows / `Λ = 42` sits under `|K|`. -/
theorem fib_hseedcard :
    seedBudgetVcomp 42
      (bfsForest [bfsAssign (airReorder (fibTree (K := FibConfigGoldilocks.K)))]).length
      < Fintype.card FibConfigGoldilocks.K := by
  have hsq : sizeWindowRootBound 42 ≤ 42 * 42 :=
    sizeWindowRootBound_le_square 42
  rw [fib_assign_rows, Field.card_K]
  unfold seedBudgetVcomp seedBudget
  simp only [Field.p] at hsq ⊢
  omega

theorem fib_p67_hcomp :
    (bfsRows (airReorder (fibTree (K := FibConfigGoldilocks.K)))).length
      ≤ 2 ^ FibConfigGoldilocks.executionOrbit.h := by
  rw [← genComputeRows_bfsForest_length (0 : FibConfigGoldilocks.K) FibConfigGoldilocks.alphaA]
  exact fib_hcomp (0 : FibConfigGoldilocks.K) FibConfigGoldilocks.alphaA

theorem fib_hrows :
    3 * (bfsRows (airReorder (fibTree (K := FibConfigGoldilocks.K)))).length
        < ringChar FibConfigGoldilocks.K ∧
      programMemShape FibConfigGoldilocks.alphaA (fibTree (K := FibConfigGoldilocks.K))
        < ringChar FibConfigGoldilocks.K := by
  have h1 := fib_p67_hcomp
  have h2 : programMemShape FibConfigGoldilocks.alphaA (fibTree (K := FibConfigGoldilocks.K))
      ≤ 2 ^ FibConfigGoldilocks.executionOrbit.h := by
    rw [programMemShape_spec (lmb := MemoryTable.formRDefault) 0]
    exact fib_hmem (0 : FibConfigGoldilocks.K) FibConfigGoldilocks.alphaA
  rw [FibConfigGoldilocks.executionOrbit_h] at h1 h2
  rw [← FibConfigGoldilocks.hchar]
  simp only [Field.p]
  constructor <;> omega

/-- `nockCompiles_of_grom_atTree_p62` at the Peano-fib
    program.  Literal `seedZ`; coins inhabited from `fib_exists_computeCoins`.
    Claim is the program triple; `fibResult` is `evalN`'s result. -/
noncomputable def fib_nockCompiles_p62 :=
  let a := Classical.choose fib_exists_computeCoins
  let ha := Classical.choose_spec fib_exists_computeCoins
  let b := Classical.choose ha
  let hb := Classical.choose_spec ha
  let c := Classical.choose hb
  let hcoins := Classical.choose_spec hb
  fun hfirst hmore =>
  nockCompiles_of_grom_atTree_p62 (hF := GeneratedField.primeFieldElems_zmod _) (hrows := fib_hrows) (F := FibConfigGoldilocks.F) (K := FibConfigGoldilocks.K) (q := Field.p)
    (Λ := 42)
    FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA FibConfigGoldilocks.alphaA MemoryTable.formRDefault
    FibConfigGoldilocks.seedZ_ne_zero FibConfigGoldilocks.two_ne_zero a b c
    FibConfigGoldilocks.executionOrbit FibConfigGoldilocks.horb
    (fibTree_eq (K := FibConfigGoldilocks.K))
    fibSubject_bounded_p fibFormula_bounded_p fib_grom
    fibTree_seedGood hcoins
    fib_hΛ fib_traceConfined
    (fib_hcomp FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA)
    (fib_hmem FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA)
    fib_hwin fib_hmemOrd
    FibConfigGoldilocks.hq FibConfigGoldilocks.hchar
    hfirst (fib_hbad fib_hΛ) fib_hout
    (by rw [← compilerKszOf_eq_L]
        exact fib_hKszChar FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA)
    fib_hprogCap
    (by rw [← programMemRows_eq_L]
        exact fib_hmemCap FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA)
    FibConfigGoldilocks.basis FibConfigGoldilocks.packageOrbit
    FibConfigGoldilocks.hcap
    (by rw [← compilerNOf_eq_L]
        exact fib_hcard FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA) hmore

/-- `nockCompiles_p67` at the Peano-fib program.
    Chosen seed is compiler `∃`; counts are dummy-`0` + irrel.
    Claim is the program triple; `fibResult` is `evalN`'s result. -/
noncomputable def fib_nockCompiles_p67 :=
  nockCompiles_p67 (hF := GeneratedField.primeFieldElems_zmod _) (hrows := by rw [fib_rom_eq]; exact fib_hrows) (F := FibConfigGoldilocks.F) (K := FibConfigGoldilocks.K) (q := Field.p) (Λ := 42)
    FibConfigGoldilocks.alphaA FibConfigGoldilocks.alphaA MemoryTable.formRDefault FibConfigGoldilocks.two_ne_zero
    fib_grom fibSubject_bounded_p fibFormula_bounded_p
    (by rw [fib_rom_eq]; exact fib_traceConfined)
    (by rw [fib_rom_eq]; exact fib_hseedcard)
    FibConfigGoldilocks.hq FibConfigGoldilocks.hchar
    FibConfigGoldilocks.executionOrbit FibConfigGoldilocks.horb
    (by rw [fib_rom_eq]; exact fib_p67_hcomp)
    (by rw [fib_rom_eq, programMemShape_spec (lmb := MemoryTable.formRDefault) 0]
        exact fib_hmem (0 : FibConfigGoldilocks.K) FibConfigGoldilocks.alphaA)
    (by rw [fib_rom_eq]; exact fib_hwin)
    (by rw [fib_rom_eq]; exact fib_hmemOrd)
    (by rw [fib_rom_eq, ← compilerKszOf_eq_L]
        exact fib_hKszChar (0 : FibConfigGoldilocks.K) FibConfigGoldilocks.alphaA)
    (by rw [fib_rom_eq]; exact fib_hprogCap)
    (by rw [fib_rom_eq]; exact fib_hmemCap (0 : FibConfigGoldilocks.K) FibConfigGoldilocks.alphaA)
    FibConfigGoldilocks.basis FibConfigGoldilocks.packageOrbit
    FibConfigGoldilocks.hcap
    (by rw [fib_rom_eq, ← compilerNOf_eq_L]
        exact fib_hcard (0 : FibConfigGoldilocks.K) FibConfigGoldilocks.alphaA)

end

end Nock.NockVMROM.Thm54.TraceGen

open Lean Elab Command Meta

namespace Batch314BinderWalk

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo)

def binderCounts (n : Name) : MetaM (Nat × Nat × Nat) := do
  let tel ← binderTelescope n
  let mut expl := 0
  let mut impl := 0
  let mut inst := 0
  for (_, bi) in tel do
    match bi with
    | .default => expl := expl + 1
    | .implicit | .strictImplicit => impl := impl + 1
    | .instImplicit => inst := inst + 1
  return (tel.size, expl, inst)

def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi) =>
    if bi == .default then some nm else none

run_cmd do
  let n62 : Name := ``Nock.NockVMROM.Thm54.TraceGen.fib_nockCompiles_p62
  let n67 : Name := ``Nock.NockVMROM.Thm54.TraceGen.fib_nockCompiles_p67
  let (t62, expl62, _) ← liftTermElabM (binderCounts n62)
  let (t67, expl67, _) ← liftTermElabM (binderCounts n67)
  if expl62 ≠ 5 then
    throwError m!"fib_nockCompiles_p62 explicit binders: got {expl62}, expected 5 (hfirst/hmore/hax/hbasis/hwidth)"
  if expl67 ≠ 5 then
    throwError m!"fib_nockCompiles_p67 explicit binders: got {expl67}, expected 5 (hfirst/hmore/hax/hbasis/hwidth)"
  logInfo m!"BINDER-WALK p62={t62}/{expl62} p67={t67}/{expl67}"

end Batch314BinderWalk

#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_nockCompiles_p62
#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_nockCompiles_p67
#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_evalN
