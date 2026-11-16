/-
  The IO layer without Kfp.  `ioEventAtG` and
  `ioSummandG` are `ioEventAt` / `ioSummand` (JointSummands.lean) restated over `CompIO`/`MemIO`;
  F2 checks they agree by `rfl` at a family.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.CompCore

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Nock.NockVMROM.Thm54.SVFrameG

open Nock Nock.Framework Nock.Walk Nock.ComputeTable Nock.MemoryTable Nock.FieldEmbedding
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open scoped Polynomial

variable {F K Kio : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F]
  [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {Φ : CoinFrame} {hC : ℕ} {S : MemShape} {C : TableSpec} {nAcc : ℕ} {m : Fin nAcc → ℕ}
  {I : IOCoinSpec Φ K Kio}
  (CF : CompIO (m := m) F K Kio Φ hC S C nAcc I) (MF : MemIO (m := m) F K Kio Φ hC S C nAcc I)

open Classical in
/-- The IO failure event of accumulator `a` at the traces' record lists (empty past the bounds). -/
def ioEventAtG (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc)
    (tr : Traces F C S) (χ : Coins Φ K) : Finset (Kio × Kio) :=
  if (CF.reqRecords V x tr.1 χ a ++ MF.internal V y tr.2 χ a).length ≤
        CF.reqBound V a + MF.internalBound V a ∧
      (MF.respRecords V y tr.2 χ a).length ≤ MF.respBound V a
  then FiniteIO.IOFailureEventW (CF.reqRecords V x tr.1 χ a ++ MF.internal V y tr.2 χ a)
    (liftWts (MF.respRecords V y tr.2 χ a))
  else ∅

theorem ioEventAtG_card_le (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc)
    (tr : Traces F C S) (χ : Coins Φ K) :
    (ioEventAtG CF MF V x y a tr χ).card ≤
      FiniteIO.ioFailureUnionBound (m a) (CF.reqBound V a + MF.internalBound V a) (MF.respBound V a)
        (Fintype.card Kio) := by
  unfold ioEventAtG
  split_ifs with h
  · refine (FiniteIO.IOFailureEventW_card_le _ _).trans (ioFailureUnionBound_mono h.1 ?_)
    rw [liftWts_length]; exact h.2
  · simp

open Classical in
def ioSummandG (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc) :
    BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) where
  coins := I.dep
  dep := coinsBelow Φ (max CF.recRound MF.respRound)
  disj := by
    rw [Finset.disjoint_left]
    intro i hi hdep
    simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hdep
    have h1 := CF.recRound_le_io i hi
    have h2 := MF.respRound_le_io i hi
    omega
  badSet tr χ := Finset.univ.filter fun v => I.pair (extIO I v) ∈ ioEventAtG CF MF V x y a tr χ
  weight := FiniteIO.ioFailureUnionBound (m a) (CF.reqBound V a + MF.internalBound V a)
    (MF.respBound V a) (Fintype.card Kio)
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn (fun v => I.pair (extIO I v)) ?_ ?_)
      (ioEventAtG_card_le CF MF V x y a tr χ)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj I h
  readsOn Q hQ χ χ' hdep := by
    have hin : ∀ i : Fin Φ.n, Φ.sampledAfter i < max CF.recRound MF.respRound → χ i = χ' i :=
      fun i hi => hdep i (by simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
    have hreq : CF.reqRecords V x (Q χ).1 χ = CF.reqRecords V x (Q χ').1 χ' :=
      CF.reqRecords_round V x _ _ χ χ' (fun j hj => hQ.1 j χ χ' (fun i hi => hin i (by omega)))
        (fun i hi => hin i (by omega))
    have hresp : MF.respRecords V y (Q χ).2 χ = MF.respRecords V y (Q χ').2 χ' :=
      MF.respRecords_round V y _ _ χ χ' (fun t j hj => hQ.2 t j χ χ' (fun i hi => hin i (by omega)))
        (fun i hi => hin i (by omega))
    show (Finset.univ.filter fun v => I.pair (extIO I v) ∈ ioEventAtG CF MF V x y a (Q χ) χ) =
      Finset.univ.filter fun v => I.pair (extIO I v) ∈ ioEventAtG CF MF V x y a (Q χ') χ'
    have hint : MF.internal V y (Q χ).2 χ = MF.internal V y (Q χ').2 χ' :=
      MF.internal_round V y _ _ χ χ' (fun t j hj => hQ.2 t j χ χ' (fun i hi => hin i (by omega)))
        (fun i hi => hin i (by omega))
    unfold ioEventAtG
    rw [hreq, hresp, hint]


end Nock.NockVMROM.Thm54.SVFrameG

end
