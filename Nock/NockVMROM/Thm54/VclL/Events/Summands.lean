/-
  Nock/NockVMROM/Thm54/VclL/Events/Summands.lean

  **The VCL-L summand list and
  `epsilon_vcll_eq`.**

  * `vclMemSummands δ Dc V` (what V2 puts in `MF.summands V _`): the table all-pairs census (V0 T2,
    `vclCensusSummand`) and the dyck-root event (V0 repair (b), `vclCellDyckRootSummand`), both over
    the tower seed `(z₁, z₂)` = `frameVCL` coins `2, 3`, at `Λ_chip = 2^110`.  The decoded table and
    the skeleton nouns are functions of the B0 columns of both sides (`Dc`, V2's decoder), guarded
    by the row-count majorants `D = V.memRows 0` and `3 + 19N` (`guardLen`: past the majorant the
    list is empty), so `card_le` is premise-free (rule 8(b)) and `readsOn` is `dep = ∅` from
    `b0Tr_staged` alone.  V2's obligation: on an accepted trace the decoded lists are within the
    majorants (then the guard is the identity, `guardLen_of_le`).
  * `epsilon_vcll_eq`: at any VCL-L-shaped `CF` / `MF` (frame `frameVCL`, shape `shapeVCL`, three
    accumulators of widths `6 / 10 / 8`), given (i) `MF.summands = vclMemSummands`, (ii) V4's
    compute summands with `epsilonOf = computeWork N / |𝕂|` (the named compute hypothesis),
    (iii) a two-coin seed (`Z.dep.card = 2`), (iv) the window bound `2^110`, and (v) the
    per-accumulator record totals `reqBound a + respBound a = 3D + 2 / 2N + P + D / N + P`,
    `epsilonOf (allSummands V x y (jointSummandsStd CF MF)) = boundVCL |𝕂| N D P Λ 2^110` with
    `Λ = leafBoundF (ringChar Kfp) N claim`.
-/
import Nock.NockVMROM.Thm54.VclL.Events.Bound
import Nock.NockVMROM.Thm54.P8Core.VclL.DyckRoot
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JointSummands
import Nock.NockVMROM.Thm54.VclL.RecordViewVCL

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Events

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.T0Tower
open scoped Polynomial

/-! ## 1. Guarded lists -/

/-- A list truncated to empty past a majorant. -/
def guardLen {α : Type*} (l : List α) (n : ℕ) : List α := if l.length ≤ n then l else []

theorem guardLen_length_le {α : Type*} (l : List α) (n : ℕ) : (guardLen l n).length ≤ n := by
  unfold guardLen; split_ifs with h
  · exact h
  · simp

theorem guardLen_of_le {α : Type*} {l : List α} {n : ℕ} (h : l.length ≤ n) : guardLen l n = l := by
  simp [guardLen, h]

/-! ## 2. The memory summands -/

section Mem

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  (δ : K) [Fact (¬ IsSquare δ)] {q : ℕ} {hC hT hP wT wP : ℕ} {rT : Fin wT → ℕ} {rP : Fin wP → ℕ} {C : TableSpec}

/-- The cell table's row count `D` (table `0` of `shapeVCL`). -/
def cellRows (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) : ℕ := V.memRows ⟨0, show 0 < 2 by decide⟩

/-- The path chip's row count `P` (table `1` of `shapeVCL`). -/
def pathRows (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) : ℕ := V.memRows ⟨1, show 1 < 2 by decide⟩

/-- **V2's B0 decoder, as the summands read it**: the decoded cell table and the census's
skeleton nouns, both functions of the B0 columns of both sides (by type). -/
structure VclB0Decode (F : Type) [Field F] (C : TableSpec) (q hT hP wT wP : ℕ)
    (rT : Fin wT → ℕ) (rP : Fin wP → ℕ) where
  rows : B0Pair F C (shapeVCL hT hP wT wP rT rP) → List (VclL.CellRowB0 q)
  skel : B0Pair F C (shapeVCL hT hP wT wP rT rP) → List Noun

variable (Dc : VclB0Decode F C q hT hP wT wP rT rP)

/-- The guarded table at the traces. -/
def rowsAt (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (tr : Traces F C (shapeVCL hT hP wT wP rT rP)) :
    List (VclL.CellRowB0 q) :=
  guardLen (Dc.rows (b0Tr tr)) (cellRows V)

/-- The guarded skeleton nouns at the traces (majorant `3 + 19N`). -/
def skelAt (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (tr : Traces F C (shapeVCL hT hP wT wP rT rP)) :
    List Noun :=
  guardLen (Dc.skel (b0Tr tr)) (3 + 19 * V.N)

theorem rowsAt_const (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP))
    (Q : Coins frameVCL K → Traces F C (shapeVCL hT hP wT wP rT rP)) (hQ : TracesStaged frameVCL C _ Q)
    (χ χ' : Coins frameVCL K) : rowsAt Dc V (Q χ) = rowsAt Dc V (Q χ') := by
  unfold rowsAt; rw [b0Tr_staged hQ χ χ']

theorem skelAt_const (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP))
    (Q : Coins frameVCL K → Traces F C (shapeVCL hT hP wT wP rT rP)) (hQ : TracesStaged frameVCL C _ Q)
    (χ χ' : Coins frameVCL K) : skelAt Dc V (Q χ) = skelAt Dc V (Q χ') := by
  unfold skelAt; rw [b0Tr_staged hQ χ χ']

/-- The table all-pairs census at `frameVCL` (V0 T2), weight `pairCount (D + 3 + 19N)(2Λ_chip − 1)`. -/
noncomputable def vclCensusAt (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    BadSummand frameVCL K (Traces F C (shapeVCL hT hP wT wP rT rP)) (TracesStaged frameVCL C _) :=
  VclL.vclCensusSummand δ (TracesStaged frameVCL C _) (rowsAt Dc V) (skelAt Dc V) (cellRows V) V.N
    (fun _ => guardLen_length_le _ _) (fun _ => guardLen_length_le _ _)
    (fun Q hQ χ χ' => ⟨rowsAt_const Dc V Q hQ χ χ', skelAt_const Dc V Q hQ χ χ'⟩)

/-- The dyck-root event at `frameVCL` (V0 repair (b)), weight `D (2Λ_chip − 1)`. -/
noncomputable def vclDyckAt (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    BadSummand frameVCL K (Traces F C (shapeVCL hT hP wT wP rT rP)) (TracesStaged frameVCL C _) :=
  VclL.vclCellDyckRootSummand δ (TracesStaged frameVCL C _) (rowsAt Dc V) (cellRows V)
    (fun _ => guardLen_length_le _ _) (fun Q hQ χ χ' => rowsAt_const Dc V Q hQ χ χ')

/-- **The VCL-L memory summands** (`MF.summands V _`): census and dyck; NO IO summand (option (a)). -/
noncomputable def vclMemSummands (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    List (BadSummand frameVCL K (Traces F C (shapeVCL hT hP wT wP rT rP)) (TracesStaged frameVCL C _)) :=
  [vclCensusAt δ Dc V, vclDyckAt δ Dc V]

theorem vclCensusAt_coins (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    (vclCensusAt δ Dc V).coins.card = 2 :=
  (VclL.vclCensusSummand_shape δ _ _ _ _ _ _ _ _).1

theorem vclCensusAt_dep (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) : (vclCensusAt δ Dc V).dep = ∅ :=
  rfl

theorem vclCensusAt_weight (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    (vclCensusAt δ Dc V).weight =
      VclL.pairCount (cellRows V + (3 + 19 * V.N)) * (2 * VclL.fuelChip - 1) := rfl

theorem vclDyckAt_coins (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    (vclDyckAt δ Dc V).coins.card = 2 :=
  (VclL.vclCellDyckRootSummand_shape δ _ _ _ _ _).1

theorem vclDyckAt_dep (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) : (vclDyckAt δ Dc V).dep = ∅ :=
  rfl

theorem vclDyckAt_weight (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    (vclDyckAt δ Dc V).weight = cellRows V * (2 * VclL.fuelChip - 1) := rfl

theorem memSeedWork_fuelChip (N D : ℕ) :
    VclL.pairCount (D + (3 + 19 * N)) * (2 * VclL.fuelChip - 1) + D * (2 * VclL.fuelChip - 1) =
      memSeedWork N D (2 ^ 110) := by
  unfold memSeedWork VclL.fuelChip
  rw [Nat.add_assoc]

/-- `ε` of two summands over two coins each. -/
theorem epsilonOf_pair {Φ : CoinFrame} {K' : Type} [Fintype K'] [DecidableEq K'] {Tr : Type}
    {Staged : (Coins Φ K' → Tr) → Prop} (s₁ s₂ : BadSummand Φ K' Tr Staged)
    (h₁ : s₁.coins.card = 2) (h₂ : s₂.coins.card = 2) :
    epsilonOf [s₁, s₂] = ((s₁.weight + s₂.weight : ℕ) : ℚ) / (Fintype.card K' : ℚ) ^ 2 := by
  simp only [epsilonOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h₁, h₂,
    Nat.cast_add]
  ring

/-- The memory summands' share of `ε`: `memSeedWork N D 2^110 / |𝕂|²`. -/
theorem epsilonOf_vclMemSummands (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) :
    epsilonOf (vclMemSummands δ Dc V) =
      ((memSeedWork V.N (cellRows V) (2 ^ 110) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := by
  rw [vclMemSummands, epsilonOf_pair _ _ (vclCensusAt_coins δ Dc V) (vclDyckAt_coins δ Dc V),
    vclCensusAt_weight, vclDyckAt_weight, memSeedWork_fuelChip]

end Mem

/-! ## 3. `epsilon_vcll_eq` -/

section Eps

theorem epsilonOf_append {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
    {Staged : (Coins Φ K → Tr) → Prop} (l₁ l₂ : List (BadSummand Φ K Tr Staged)) :
    epsilonOf (l₁ ++ l₂) = epsilonOf l₁ + epsilonOf l₂ := by
  simp [epsilonOf, List.map_append, List.sum_append]

abbrev mVCL : Fin 3 → ℕ := RV.mVCL

def mVCL10 : Fin 3 → ℕ := ![5, 10, 8]

/-- The per-accumulator record totals (validity, export, path) at `kc = 3` (record 0 is the
formula-cell export lookup on every row, DESIGN §1). -/
def totVCL (N D P : ℕ) : Fin 3 → ℕ := ![3 * D + 2, 3 * N + P + D, N + P]

/-- The record totals at the side slot: each cell row provides two export records (`2D`). -/
def totVCLS (N D P : ℕ) : Fin 3 → ℕ := ![3 * D + 2, 3 * N + P + 2 * D, N + P]

section Hist10
variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp] [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  (δ : K) [Fact (¬ IsSquare δ)] {q : ℕ} {hC hT hP wT wP : ℕ} {rT : Fin wT → ℕ} {rP : Fin wP → ℕ}
  {C : TableSpec}
  {R : RecordView F K Kio Kfp Key C (shapeVCL hT hP wT wP rT rP) hC mVCL10} {Z : SeedSpec frameVCL K Kfp}
  {I : IOCoinSpec frameVCL K Kio}
  (CF : CompSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)
  (MF : MemSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)
  (Dc : VclB0Decode F C q hT hP wT wP rT rP)

/-- The IO coins are four frame coins (`I.dep.card = 4`, `ioSpecVCL`) in
`Kio` with `|Kio| = |𝕂|²` (`Quad δ`, `quad_card`); each IO summand's mass is
`ioFailureUnionBound (m a) k₁ k₂ 1 / |𝕂|²` by `ioSummand_mass_ext`.  `inlinePairCount = 0`
(`inlineRecords := 0` at the repaired chip, DESIGN §1) makes the inline census weight `0`. -/
theorem epsilon_vcll_eq_w10 (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (x : CF.Msg0)
    (y : MF.Msg0)
    (hMF : MF.summands V y = vclMemSummands δ Dc V)
    (hCF : epsilonOf (CF.summands V x) = (computeWork V.N : ℚ) / (Fintype.card K : ℚ))
    (hZ : Z.dep.card = 2)
    (hW : MF.windowBound V y = 2 ^ 110)
    (hI : I.dep.card = 4) (hKio : Fintype.card Kio = Fintype.card K ^ 2)
    (hinl : CF.inlinePairCount = 0)
    (htot : ∀ a, (CF.reqBound V a + MF.internalBound V a) + MF.respBound V a =
      totVCL V.N (cellRows V) (pathRows V) a) :
    epsilonOf (allSummands (CF := CF) (MF := MF) V x y (jointSummandsStd CF MF)) =
      boundVCL' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  have hio : ∀ a, (((ioSummand CF MF V x y a).weight : ℕ) : ℚ) /
        (Fintype.card K : ℚ) ^ (ioSummand CF MF V x y a).coins.card =
      (ioFailureUnionBound (mVCL10 a) 0 (totVCL V.N (cellRows V) (pathRows V) a) 1 : ℚ) /
        (Fintype.card K : ℚ) ^ 2 := by
    intro a
    rw [ioSummand_mass_ext CF MF V x y a hI hKio, ioFailureUnionBound_eq_zero_add, htot a]
  have hWw : windowW MF V y = max (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
    rw [windowW, hW]
  have hcoin : ∀ a, (ioSummand CF MF V x y a).coins.card = 4 := fun _ => hI
  unfold allSummands
  rw [epsilonOf_append, epsilonOf_append, hCF, hMF, epsilonOf_vclMemSummands]
  simp only [jointSummandsStd, jointSummands, epsilonOf, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.ofFn_succ, List.ofFn_zero]
  simp only [zeroSummand, lowSummand, censusSummand, recSummand, rootSummand, inlineSummand,
    seedSummand, hZ, hinl, hWw]
  simp only [hio]
  simp only [boundVCL', boundGen, ioWorkKp, jointSeedWork, mVCL10, totVCL]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_two,
    Matrix.tail_cons]
  push_cast
  ring

end Hist10

section Side
variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp] [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  (δ : K) [Fact (¬ IsSquare δ)] {q : ℕ} {hC hT hP wT wP : ℕ} {rT : Fin wT → ℕ} {rP : Fin wP → ℕ}
  {C : TableSpec}
  {R : RecordView F K Kio Kfp Key C (shapeVCL hT hP wT wP rT rP) hC mVCL} {Z : SeedSpec frameVCL K Kfp}
  {I : IOCoinSpec frameVCL K Kio}
  (CF : CompSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)
  (MF : MemSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)
  (Dc : VclB0Decode F C q hT hP wT wP rT rP)

/-- The IO coins are four frame coins (`I.dep.card = 4`, `ioSpecVCL`) in
`Kio` with `|Kio| = |𝕂|²` (`Quad δ`, `quad_card`); each IO summand's mass is
`ioFailureUnionBound (m a) k₁ k₂ 1 / |𝕂|²` by `ioSummand_mass_ext`.  `inlinePairCount = 0`
(`inlineRecords := 0` at the repaired chip, DESIGN §1) makes the inline census weight `0`. -/
theorem epsilon_vcll_eq (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (x : CF.Msg0)
    (y : MF.Msg0)
    (hMF : MF.summands V y = vclMemSummands δ Dc V)
    (hCF : epsilonOf (CF.summands V x) = (computeWork V.N : ℚ) / (Fintype.card K : ℚ))
    (hZ : Z.dep.card = 2)
    (hW : MF.windowBound V y = 2 ^ 110)
    (hI : I.dep.card = 4) (hKio : Fintype.card Kio = Fintype.card K ^ 2)
    (hinl : CF.inlinePairCount = 0)
    (htot : ∀ a, (CF.reqBound V a + MF.internalBound V a) + MF.respBound V a =
      totVCLS V.N (cellRows V) (pathRows V) a) :
    epsilonOf (allSummands (CF := CF) (MF := MF) V x y (jointSummandsStd CF MF)) =
      boundVCL'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  have hio : ∀ a, (((ioSummand CF MF V x y a).weight : ℕ) : ℚ) /
        (Fintype.card K : ℚ) ^ (ioSummand CF MF V x y a).coins.card =
      (ioFailureUnionBound (mVCL a) 0 (totVCLS V.N (cellRows V) (pathRows V) a) 1 : ℚ) /
        (Fintype.card K : ℚ) ^ 2 := by
    intro a
    rw [ioSummand_mass_ext CF MF V x y a hI hKio, ioFailureUnionBound_eq_zero_add, htot a]
  have hWw : windowW MF V y = max (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
    rw [windowW, hW]
  have hcoin : ∀ a, (ioSummand CF MF V x y a).coins.card = 4 := fun _ => hI
  unfold allSummands
  rw [epsilonOf_append, epsilonOf_append, hCF, hMF, epsilonOf_vclMemSummands]
  simp only [jointSummandsStd, jointSummands, epsilonOf, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.ofFn_succ, List.ofFn_zero]
  simp only [zeroSummand, lowSummand, censusSummand, recSummand, rootSummand, inlineSummand,
    seedSummand, hZ, hinl, hWw]
  simp only [hio]
  simp only [boundVCL'', boundGen, ioWorkKpS, jointSeedWork, mVCL, RV.mVCL, totVCLS]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_two,
    Matrix.tail_cons]
  push_cast
  ring

end Side

end Eps

end Nock.NockVMROM.Thm54.VclL.Events
