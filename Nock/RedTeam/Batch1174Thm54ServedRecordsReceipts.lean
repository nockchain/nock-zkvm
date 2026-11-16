/-
  Nock/RedTeam/Batch1174Thm54ServedRecordsReceipts.lean

§A **Why the oracle is read at positional pairs**.  The C2 join node of an `OP1`
  row does not read the row's carrier `S`: two `OP1` rows with different carriers (hence different
  trace rows, `S` strictly increases along the BFS) give the SAME join tree at the same inputs
  (`join_s1_carrier_blind`).  So `Batch1111.ServedRecordsOK`, which quantifies over every `(u, s, f)`
  whose join node is merely a subtree of the root join, reads row `u`'s trace record against the
  structural inputs reached at ANOTHER row `u''`; discharging it needs `enc z f = enc z f_a → f = f_a`
  for a cross-row pair `(f, f_a)` that no priced event lists.  The positional pairs are the ones the
  induction consumes.

  §B **Non-vacuity of link (iv)** on a HAND-BUILT five-row memory trace over `ZMod 31` (not a
  generated trace; labelled as such): an OP0-style read of axis `2` of the cell subject `[4 7]` —
  `read_root(e=5) → decompose → (verify_child(e=5) → halt 4, halt 7)`.  Every hypothesis of
  `Batch1170.slot_of_paths` holds (tiling, BFS validity, exponent injectivity of both classes, R4's
  path equation `V = R ++ bitsOf 1 (fun _ => false)`), and the conclusion is
  `Noun.slot 2 [4 7] = some 4` (`nonvacuous_slot_of_paths`).

  -- the paper
-/
import Nock.RedTeam.Batch1172Thm54ServedRecordsAtTraces

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1174

open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.WalkTilingEvents (memRowStateOf foOfMem)
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.RedTeam.Batch554

/-! ## §A  The `OP1` join node is carrier-blind -/

section Blind

variable {K : Type} [Field K] (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)

/-- **Two `OP1` rows with different carriers give the same C2 join node.** -/
theorem join_s1_carrier_blind (n : ℕ) (row1 row2 : (State × DTcomp K) × ℕ)
    (h1 : row1.1.1 = .s1) (h2 : row2.1.1 = .s1) (s f : Noun) :
    c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1) (fun l => l.2) sv ax n
        (.node row1 []) s f =
      c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1) (fun l => l.2) sv ax n
        (.node row2 []) s f := by
  have hrow : ∀ S1 S2 : ℕ, c2SkeletonRow sv ax .s1 S1 s f [] = c2SkeletonRow sv ax .s1 S2 s f [] := by
    intro S1 S2
    dsimp only [c2SkeletonRow]
    congr 1
    funext i hi
    rcases i with ⟨_ | _ | _ | i, hi3⟩ <;> rfl
  cases n with
  | zero => simp only [c2JoinFuel, c2JoinKids, h1, h2, List.map_nil]; rw [hrow]
  | succ n => simp only [c2JoinFuel, c2JoinKids, h1, h2, List.map_nil]; rw [hrow]

end Blind

/-! ## §B  Link (iv) on a hand-built five-row memory trace -/

section NonVacuity

instance fact31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- Row traces (0-indexed rows; 1-indexed rows `1..5` of the walk). -/
def trEx : ℕ → ℕ → ZMod 31
  | 0, 2 => 1 | 0, 181 => 5         -- row 1: read_root, exponent 5
  | 1, 0 => 1                        -- row 2: decompose
  | 2, 181 => 5                      -- row 3: verify_child, exponent 5
  | 3, 1 => 1 | 3, 180 => 7          -- row 4: halt, atom 7
  | 4, 1 => 1 | 4, 180 => 4          -- row 5: halt, atom 4
  | _, _ => 0

def envsEx : Fin 5 → Env (ZMod 31) := fun i => ⟨trEx i.val, fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem st0 : memRowStateOf (envsEx 0) = .read_root := by decide
theorem st1 : memRowStateOf (envsEx 1) = .decompose := by decide
theorem st2 : memRowStateOf (envsEx 2) = .verify_child := by decide
theorem st3 : memRowStateOf (envsEx 3) = .halt := by decide
theorem st4 : memRowStateOf (envsEx 4) = .halt := by decide

theorem exp0 : rowExp envsEx 0 = 5 := by
  show RecordCarrier.natLift ((5 : ℕ) : ZMod 31) = 5
  exact RecordCarrier.natLift_natCast (by rw [ZMod.ringChar_zmod_n]; norm_num)

theorem exp2 : rowExp envsEx 2 = 5 := by
  show RecordCarrier.natLift ((5 : ℕ) : ZMod 31) = 5
  exact RecordCarrier.natLift_natCast (by rw [ZMod.ringChar_zmod_n]; norm_num)

theorem fo_eq (i : ℕ) : foOfMem envsEx i =
    if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 1 else 0 := by
  unfold foOfMem
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simp
  · rw [dif_pos ⟨by omega, by omega⟩]; simp only [Nat.add_sub_cancel]; rw [show (⟨0, _⟩ : Fin 5) = 0 from rfl, st0]; rfl
  · rw [dif_pos ⟨by omega, by omega⟩]; rw [show (⟨2 - 1, _⟩ : Fin 5) = 1 from rfl, st1]; rfl
  · rw [dif_pos ⟨by omega, by omega⟩]; rw [show (⟨3 - 1, _⟩ : Fin 5) = 2 from rfl, st2]; rfl
  · rw [dif_pos ⟨by omega, by omega⟩]; rw [show (⟨4 - 1, _⟩ : Fin 5) = 3 from rfl, st3]; rfl
  · rw [dif_pos ⟨by omega, by omega⟩]; rw [show (⟨5 - 1, _⟩ : Fin 5) = 4 from rfl, st4]; rfl
  · rw [dif_neg (by omega)]; simp

theorem sf_val (n : ℕ) (hn : n ≤ 5) : Sf (foOfMem envsEx) n =
    if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 3 else 4 := by
  interval_cases n <;> simp [Sf, Finset.sum_Icc_succ_top, fo_eq]

theorem hSfEx : 1 + Sf (foOfMem envsEx) 5 = 5 := by rw [sf_val 5 le_rfl]; rfl

theorem hvalidEx : BFSValidF 1 (foOfMem envsEx) 5 := by
  intro i h1 h2
  rw [sf_val (i - 1) (by omega)]
  interval_cases i <;> simp

theorem hREx : ExpInjOn envsEx .read_root := by
  intro r r' hs hs' _
  fin_cases r <;> fin_cases r' <;> first | rfl | (exfalso; revert hs; decide) | (exfalso; revert hs'; decide)

theorem hVEx : ExpInjOn envsEx .verify_child := by
  intro r r' hs hs' _
  fin_cases r <;> fin_cases r' <;> first | rfl | (exfalso; revert hs; decide) | (exfalso; revert hs'; decide)

/-- The decoded memory tree at root row `1`. -/
theorem treeEx (envsK : Fin 5 → Env (ZMod 31)) :
    decodedMTreeOfEnvs envsK envsEx 1 1 =
      .read 5 (.decompose (.verify 5 0 .halt) .halt) := by
  have c11 : childIdx envsEx 1 1 1 = 2 := by unfold childIdx; rw [sf_val 0 (by omega)]; rfl
  have c21 : childIdx envsEx 1 2 1 = 3 := by unfold childIdx; rw [sf_val 1 (by omega)]; rfl
  have c22 : childIdx envsEx 1 2 2 = 4 := by unfold childIdx; rw [sf_val 1 (by omega)]; rfl
  have c31 : childIdx envsEx 1 3 1 = 5 := by unfold childIdx; rw [sf_val 2 (by omega)]; rfl
  rw [tree_read_of envsK envsEx 1 1 ⟨le_rfl, by omega⟩ st0, c11, if_pos (by omega),
    tree_decompose_of envsK envsEx 1 2 ⟨by omega, by omega⟩ st1, c21, c22, if_pos (by omega),
    if_pos (by omega),
    tree_verify_of envsK envsEx 1 3 ⟨by omega, by omega⟩ st2, c31, if_pos (by omega),
    tree_halt_of envsK envsEx 1 4 ⟨by omega, by omega⟩ st3,
    tree_halt_of envsK envsEx 1 5 ⟨by omega, by omega⟩ st4]
  have e0 : rowExp envsEx ⟨1 - 1, by omega⟩ = 5 := exp0
  have e2 : rowExp envsEx ⟨3 - 1, by omega⟩ = 5 := exp2
  rw [e0, e2]

theorem rowAt_read : RowAt envsEx .read_root 5 1 := ⟨by omega, le_rfl, st0, exp0⟩
theorem rowAt_verify : RowAt envsEx .verify_child 5 3 := ⟨by omega, by omega, st2, exp2⟩

/-- **Non-vacuity of link (iv)** (hand-built trace): every hypothesis of `slot_of_paths` holds and
the verify row's pre-`z` noun is the slot at axis `2` of the read row's. -/
theorem nonvacuous_slot_of_paths (envsK : Fin 5 → Env (ZMod 31)) :
    Noun.slot 2 (preZNounOfEnvs (ZMod 31) 31 1 envsEx (by decide) 1) =
      some (preZNounOfEnvs (ZMod 31) 31 1 envsEx (by decide) 3) := by
  have hrp : rpaths 5 (decodedMTreeOfEnvs envsK envsEx 1 1) = [[]] := by
    rw [treeEx]; simp [rpaths]
  have hvp : vpaths 5 (decodedMTreeOfEnvs envsK envsEx 1 1) = [[] ++ bitsOf 1 (fun _ => false)] := by
    rw [treeEx]; simp [vpaths, bitsOf]
  have h := Batch1170.slot_of_paths envsK envsEx (by decide) 1 31 hSfEx hvalidEx 5 1
    (fun _ => false) 1 le_rfl (by omega) hREx hVEx hrp hvp rowAt_read rowAt_verify
  simpa [StrategyOfTracesR0.certAxis] using h

end NonVacuity

end Nock.RedTeam.Batch1174

#print axioms Nock.RedTeam.Batch1174.join_s1_carrier_blind
#print axioms Nock.RedTeam.Batch1174.nonvacuous_slot_of_paths
