/-
  Nock/RedTeam/Batch287Thm54BinderTransportReview.lean

  Did not write the restatements.

  Paper re-read at source: `:1090-1099`, `:1097`, `:1160`, `:1450`, `:1697`,
  `:1846-1852`, `:1893`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
  No production file under `Nock/NockVMROM/` is edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenExactExecution
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.Framework.Thm54.OrbitDomain
import Nock.RedTeam.Batch246Thm54InputsAtGeneratedCarrier
import Nock.RedTeam.Batch286Thm54P62CapacityBinders
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Lean Elab Command Meta

/-- Binder telescope of a constant's type (instances and implicits included). -/
def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  forallTelescope info.type fun xs _ => do
    xs.mapM fun x => do
      let id := x.fvarId!
      pure (← id.getUserName, ← id.getBinderInfo)

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

/-- Names of default (explicit) binders, in telescope order. -/
def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi) =>
    if bi == .default then some nm else none

run_cmd do
  let check (n : Name) (total expl : Nat) : CommandElabM Unit := do
    let (t, e, _i) ← liftTermElabM (binderCounts n)
    if t ≠ total || e ≠ expl then
      throwError m!"binder count {n}: got total {t} explicit {e}, expected {total}/{expl}"
    logInfo m!"BINDER-COUNT {n} total={t} explicit={e}"
  let n0 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_of_grom_atRomSeed
  let n1 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p61
  let n2 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p62
  check n0 73 55
  check n1 65 47
  check n2 57 39
  let e0 ← liftTermElabM (explicitNames n0)
  let e1 ← liftTermElabM (explicitNames n1)
  let e2 ← liftTermElabM (explicitNames n2)
  for nm in e1 do
    unless e0.contains nm || nm == `lmb || nm == `hmemOrd || nm == `αW do
      throwError m!"P6.1 added explicit binder {nm}"
  for nm in e2 do
    unless e1.contains nm do
      throwError m!"P6.2 added explicit binder {nm}"
  logInfo m!"BINDER-DIFF p61 explicit names ⊆ atRomSeed"
  logInfo m!"BINDER-DIFF p62 explicit names ⊆ p61"

namespace Nock.RedTeam.Batch287

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework.Thm54
open Nock.RedTeam
open Nock.NockVMROM.Thm54.BuildableAxisWitness

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK




noncomputable section

/-! ## F-1. Claim conjunct is the evaluation result. -/

/-- `hgrom` is §1's `hrun`: a guarded ROM run is a reference-interpreter run. -/
theorem hgrom_implies_evalN {q fuel : ℕ} {subject formula result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result) :
    Nock.evalN fuel subject formula = some result :=
  evalGRom_evalN hgrom

/-- Tier A's `hgrom` is the same `result` the package claims. -/
theorem b287_tierA_grom_evalN :
    Nock.evalN 4 dotSubject dotFormula = some dotResult :=
  evalGRom_evalN Batch263.b263_grom

/-- Independent evalN pin of the same triple. -/
theorem b287_claimed_result_is_evalN :
    Nock.evalN 4 dotSubject dotFormula = some dotResult :=
  Batch246.b246_claim_evalN

/-! ## F-2. Compiler choices; `kMem` ignores the challenge vector. -/

/-- No `result`, no acceptance. -/
theorem compilerChallengeVector_is_coins {K : Type} [Field K] (α z a b c lmb : K) :
    compilerChallengeVector α z a b c lmb =
      { a := a, b := b, c := c, α := α, z := z, β := 0, γ := 0,
        lam := lmb } :=
  rfl

/-- `kMem` is the forest's root count, independent of `chal`. -/
theorem genExactConfig_kMem_eq_mf_length
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem).kMem
      = mf.length :=
  rfl

theorem compilerKszOf_is_max {K : Type} [Field K]
    (z α : K) (t : NTree (GenComputeRow K)) :
    compilerKszOf z α t = max (programAcc t) (2 * programMemRoots z α t) :=
  rfl

theorem compilerNOf_is_max {K : Type} [Field K]
    (z α : K) (t : NTree (GenComputeRow K)) :
    compilerNOf z α t = max (programAcc t) (programMemRows z α t) :=
  rfl

/-- The four `le_max` comparisons at the compiler choice, not by a hypothesis. -/
theorem compiler_comparisons_hold (acc mfLen memR : ℕ) :
    acc ≤ compilerKsz acc mfLen ∧
      2 * mfLen ≤ compilerKsz acc mfLen ∧
      acc ≤ compilerN acc memR ∧
      memR ≤ compilerN acc memR :=
  ⟨compilerKsz_acc acc mfLen, compilerKsz_two_mul acc mfLen,
    compilerN_acc acc memR, compilerN_mem acc memR⟩

theorem B_eq_orderOf_le_rfl {K : Type} [Monoid K] (α : K) :
    orderOf α ≤ orderOf α :=
  le_rfl

/-! ## F-3. Tier A numerals. -/

theorem b287_compilerKsz_eq_20 :
    compilerKszOfL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)) = 20 :=
  Batch286.b286_compilerKsz

theorem b287_compilerN_eq_184 :
    compilerNOfL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)) = 184 :=
  Batch286.b286_compilerN

theorem b287_compilerKsz_is_max_13_20 :
    compilerKsz 13 10 = 20 ∧ compilerKsz 13 10 = max 13 (2 * 10) := by
  constructor <;> norm_num

theorem b287_compilerN_is_max_13_184 :
    compilerN 13 184 = 184 ∧ compilerN 13 184 = max 13 184 := by
  constructor <;> norm_num

/-! ## F-4. `hcard` vs `hrow`; RAP orbit vs timestamp `α`. -/

theorem b287_hcard_is_quadratic {K' : Type} [Fintype K'] (n : ℕ)
    (hpos : 0 < Fintype.card K') :
    ioFailureUnionBound 8 n n (Fintype.card K') < Fintype.card (K' × K')
      ↔ 28 * n * n + 4 * n < Fintype.card K' :=
  GoldilocksParameters.hcard_iff n hpos

/-- `hrow`-shape holds, `hcard` fails. -/
theorem b287_hrow_holds_hcard_fails_deg1 :
    6 < 769 ∧ ¬ (28 * 6 * 6 + 4 * 6 < 769) := by
  constructor <;> norm_num

theorem b287_hcard_fails_n6_card769 :
    ¬ (ioFailureUnionBound 8 6 6 769 < 769 * 769) := by
  rw [GoldilocksParameters.ioFailureUnionBound_eight]
  norm_num

theorem b287_hcard_holds_n5_card769 :
    ioFailureUnionBound 8 5 5 769 < 769 * 769 := by
  rw [GoldilocksParameters.ioFailureUnionBound_eight]
  norm_num

/-- §1 cubic carrier at a small prime: `n < p` does not give `hcard` -/
theorem b287_cubic_p13_hrow_not_hcard :
    9 < 13 ∧ ¬ (28 * 9 * 9 + 4 * 9 < 13 ^ 3) := by
  constructor <;> norm_num

/-- Same cubic shape at Tier A's prime: `n < p` does give `hcard`. -/
theorem b287_cubic_p769_hrow_implies_hcard :
    28 * 768 * 768 + 4 * 768 < 769 ^ 3 := by
  norm_num

theorem b287_orbit_ω_order {K : Type} [Field K] (o : OrbitDomain K) :
    orderOf o.ω = 2 ^ o.h :=
  o.order_ω

theorem b287_two_pow_ne_192 (h : ℕ) : 2 ^ h ≠ 192 := by
  rcases Nat.lt_or_ge h 8 with hlt | hge
  · have : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro heq
    have hpow : 2 ^ 8 ≤ 2 ^ h := Nat.pow_le_pow_right (by decide : 0 < 2) hge
    have : 256 ≤ 192 := by
      rw [show 2 ^ 8 = 256 from rfl, heq] at hpow
      exact hpow
    exact (by decide : ¬ 256 ≤ 192) this

/-- Timestamp `α` at Tier A cannot inhabit `orbit.ω` -/
theorem b287_alphaA_cannot_be_orbit_ω :
    orderOf alphaA = 192 ∧ ∀ h : ℕ, 2 ^ h ≠ 192 :=
  ⟨Batch180.alphaA_order_eq_192, b287_two_pow_ne_192⟩

/-- `packageOrbit` wants exact order `e · 2^h`, not `orderOf α` -/
theorem b287_strictOrbit_order {F : Type} [Field F] {e h : ℕ}
    (o : StrictOrbitDomain F e h) :
    orderOf o.ω = e * 2 ^ h :=
  o.order_ω

/-! ## F-5. Witnesses fire; claim is the generated program's result. -/

noncomputable def b287_p61_fires :=
  Batch285.b285_nockCompiles_p61

noncomputable def b287_p62_fires :=
  Batch286.b286_nockCompiles_p62

theorem b287_p62_claim_result :
    ∀ {package : OptimizedFullStrictNockVMROMPackage DF DK 8},
      package.optimized.verifier.raw.claim = ⟨dotSubject, dotFormula, dotResult⟩ →
        package.optimized.verifier.raw.claim.result = dotResult := by
  intro package h
  rw [h]

end

end Nock.RedTeam.Batch287

#print axioms Nock.RedTeam.Batch287.hgrom_implies_evalN
#print axioms Nock.RedTeam.Batch287.b287_tierA_grom_evalN
#print axioms Nock.RedTeam.Batch287.b287_claimed_result_is_evalN
#print axioms Nock.RedTeam.Batch287.compilerChallengeVector_is_coins
#print axioms Nock.RedTeam.Batch287.genExactConfig_kMem_eq_mf_length
#print axioms Nock.RedTeam.Batch287.compilerKszOf_is_max
#print axioms Nock.RedTeam.Batch287.compilerNOf_is_max
#print axioms Nock.RedTeam.Batch287.compiler_comparisons_hold
#print axioms Nock.RedTeam.Batch287.B_eq_orderOf_le_rfl
#print axioms Nock.RedTeam.Batch287.b287_compilerKsz_eq_20
#print axioms Nock.RedTeam.Batch287.b287_compilerN_eq_184
#print axioms Nock.RedTeam.Batch287.b287_compilerKsz_is_max_13_20
#print axioms Nock.RedTeam.Batch287.b287_compilerN_is_max_13_184
#print axioms Nock.RedTeam.Batch287.b287_hcard_is_quadratic
#print axioms Nock.RedTeam.Batch287.b287_hrow_holds_hcard_fails_deg1
#print axioms Nock.RedTeam.Batch287.b287_hcard_fails_n6_card769
#print axioms Nock.RedTeam.Batch287.b287_hcard_holds_n5_card769
#print axioms Nock.RedTeam.Batch287.b287_cubic_p13_hrow_not_hcard
#print axioms Nock.RedTeam.Batch287.b287_cubic_p769_hrow_implies_hcard
#print axioms Nock.RedTeam.Batch287.b287_orbit_ω_order
#print axioms Nock.RedTeam.Batch287.b287_two_pow_ne_192
#print axioms Nock.RedTeam.Batch287.b287_alphaA_cannot_be_orbit_ω
#print axioms Nock.RedTeam.Batch287.b287_strictOrbit_order
#print axioms Nock.RedTeam.Batch287.b287_p61_fires
#print axioms Nock.RedTeam.Batch287.b287_p62_fires
#print axioms Nock.RedTeam.Batch287.b287_p62_claim_result
