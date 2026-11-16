/-
  NockvmE2E/Exec/E2EW0.lean   (Coder W; proof-only)

  `OpsU` (the pi-free, g-free instance fact about the flat batched-opening list), `w0link_of_opsU`, `base_link`, `hW0_of_opsU`,
  and `UniLinksN`/`uniLinks'_of_N`/`hU_of_N`: the pi-free replacements of `Resid.hW0` / `Resid.hU`.
-/
import NockvmE2E.Exec.E2EMain
import NockvmE2E.Exec.E2EResid

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2EW0
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid

section Ops
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriDeep NockvmE2E.Exec.Cover NockvmE2E.Exec.E2ELR NockvmE2E.Rap
variable (XI : ExecInst)
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
structure OpsU (vTOf : Array (Array VF.K3) → ι × Fin r → KC) (colN : ι ⊕ Fin P.nq → ℕ)
    (rk : ∀ b, {c : ι ⊕ Fin P.nq // P.colRoundX c = b} ≃ Fin (Wb XI b)) (encB : B ↪ DgJ8) : Prop where
  hopsF : ∀ (cs ζ : VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3), VShape XI vT vQ →
    List.Forall₂ (fun (o : ℕ × ℕ × VF.K3 × VF.K3) (j : Fin (m + 1)) =>
      o.2.1 < XI.r + 2 ∧ toKV o.2.2.1 = toKV cs ^ (j : ℕ) ∧
      toKV (openPts XI ζ)[o.2.1]! = Sum.elim (fun ck => A.pt ck.1 ck.2 (toKV ζ)) (fun _ => toKV ζ) (e j) ∧
      toKV o.2.2.2 = Sum.elim (vTOf vT) (fun q => toKV vQ[q.1]!) (e j) ∧
      o.1 = colN (colOf P e j))
      (openingList XI cs vT vQ).toList (List.finRange (m + 1))
  hcolB : ∀ c, XI.blockOf[colN c]! = P.colRoundX c
  hcR : ∀ c, P.colRoundX c < 4
  hrkV : ∀ b (c : {c : ι ⊕ Fin P.nq // P.colRoundX c = b}), ((rk b c : Fin _) : ℕ) = (blockLayout XI).2[colN c.1]!
  hencB : ∀ v : ℕ, v < NockvmE2E.Exec.p → ∃ b : B, encB b = dgOf [v, 0, 0, 0, 0] ∧ algebraMap B KC b = homV.ψ (UInt64.ofNat v)


end Ops

/-! ## non-vacuity of `OpsU` (kernel): the toy instance `r = 1`, `nc = 1`, `nq = 1`, `m = 1` -/

section Toy
open NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriDeep NockvmE2E.Rap

def toyX : ExecInst :=
  { nD := 2, dShift := 7, dGen := 2, hN := 4, hGen := 1, hShift := 1, r := 1, k := 1, d := 1, l := 4, nc := 1, nq := 1,
    colKind := #[0], blockOf := #[0, 1], pre := #[#[]], pubOf := #[], ppt := VF.K3.one,
    nCoins := #[0, 0], derived := #[], tabs := #[], pubMode := 1 }

def toyΦ : CoinFrame := ⟨2, fun i => i.val⟩

noncomputable def toyP : DeepParams toyΦ KC Unit (Fin (2 ^ toyX.nD) → ZMod NockvmE2E.Exec.p) (fun _ => 0) where
  R := 0
  nq := 1
  ns := 0
  a := ⟨0, by decide⟩
  z := ⟨1, by decide⟩
  ha := rfl
  hz := rfl
  hcol := fun _ => le_rfl
  H := ∅
  D := ∅
  toPoly := fun _ => 0
  hβ := fun _ => by simp
  Cp := fun _ _ _ => 0
  hC := fun _ _ _ => by simp
  hCcoin := fun _ _ _ => rfl

noncomputable def toyA : AirShape toyP 1 where
  off := fun _ => 1
  Cv := fun _ _ _ _ => 0
  pt := fun _ _ y => y
  hCv := fun _ _ i _ => i.elim0

def toyE : Fin 2 ≃ (Unit × Fin 1) ⊕ Fin toyP.nq where
  toFun j := if j.val = 0 then Sum.inl ((), 0) else Sum.inr ⟨0, Nat.one_pos⟩
  invFun s := Sum.elim (fun _ => 0) (fun _ => 1) s
  left_inv := by decide
  right_inv := by decide


noncomputable def toyVTOf : Array (Array VF.K3) → Unit × Fin 1 → KC := fun vT _ => toKV (vT[0]!)[0]!
def toyColN : Unit ⊕ Fin toyP.nq → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem toy_blk (b : ℕ) : NockvmE2E.Exec.Cover.Wb toyX b = if b = 0 ∨ b = 1 then 1 else 0 := by
  by_cases hb : b < 4
  · interval_cases b <;> decide
  · have : ¬ b < (blockLayout toyX).1.size := by rw [blockLayout_size]; exact hb
    unfold Wb
    rw [getElem!_neg _ b this]
    simp; omega

theorem toy_card (b : ℕ) : Fintype.card {c : Unit ⊕ Fin toyP.nq // toyP.colRoundX c = b} = Wb toyX b := by
  rw [toy_blk]
  by_cases h0 : b = 0
  · subst h0; decide
  by_cases h1 : b = 1
  · subst h1; decide
  · rw [if_neg (by omega)]
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨c, hc⟩ => ?_⟩
    rcases c with ⟨⟩ | k
    · exact h0 hc.symm
    · exact h1 hc.symm

noncomputable def toyRk : ∀ b, {c : Unit ⊕ Fin toyP.nq // toyP.colRoundX c = b} ≃ Fin (Wb toyX b) :=
  fun b => Fintype.equivFinOfCardEq (toy_card b)

noncomputable def toyEncB : ZMod NockvmE2E.Exec.p ↪ DgJ8 :=
  ⟨fun b => dgOf [b.val, 0, 0, 0, 0], fun a b h => by
    have := congrFun h 0
    simpa [dgOf] using this⟩

theorem toy_hencB (v : ℕ) (hv : v < NockvmE2E.Exec.p) :
    ∃ b : ZMod NockvmE2E.Exec.p, toyEncB b = dgOf [v, 0, 0, 0, 0] ∧ algebraMap (ZMod NockvmE2E.Exec.p) KC b = homV.ψ (UInt64.ofNat v) := by
  refine ⟨(v : ZMod NockvmE2E.Exec.p), ?_, ?_⟩
  · show dgOf [((v : ZMod NockvmE2E.Exec.p)).val, 0, 0, 0, 0] = _
    rw [ZMod.val_natCast_of_lt hv]
  · have h64 : v < 2 ^ 64 := lt_trans hv (by unfold NockvmE2E.Exec.p; norm_num)
    show _ = NockvmE2E.Exec.VL.psiV _
    unfold NockvmE2E.Exec.VL.psiV NockvmE2E.Exec.VL.zv
    rw [UInt64.toNat_ofNat_of_lt' h64]

/-- **non-vacuity of `OpsU`** (kernel): the toy instance `r = 1`, `nc = 1`, `nq = 1`, `m = 1` -/
theorem toyOps : OpsU toyX toyP toyA toyE toyVTOf toyColN toyRk toyEncB where
  hopsF := by
    intro cs ζ vT vQ _
    have h : (openingList toyX cs vT vQ).toList = [(0, 0, VF.K3.one, (vT[0]!)[0]!), (1, 2, VF.K3.mul VF.K3.one cs, vQ[0]!)] := rfl
    rw [h]
    have h2 : List.finRange 2 = [0, 1] := rfl
    rw [h2]
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · refine ⟨by show 0 < 1 + 2; decide, ?_, ?_, rfl, rfl⟩
      · simp [toKV_one]
      · show toKV (VF.K3.mul ζ VF.K3.one) = toKV ζ
        rw [toKV_mul, toKV_one, mul_one]
    · refine ⟨by show 2 < 1 + 2; decide, ?_, rfl, rfl, rfl⟩
      · show toKV (VF.K3.mul VF.K3.one cs) = toKV cs ^ 1
        rw [toKV_mul, toKV_one, one_mul, pow_one]
  hcolB := by rintro (⟨⟩ | k) <;> rfl
  hcR := by
    rintro (⟨⟩ | k)
    · show 0 < 4; decide
    · show 1 < 4; decide
  hrkV := by
    rintro b ⟨c, hc⟩
    subst hc
    have hw : Wb toyX (toyP.colRoundX c) = 1 := by
      rcases c with ⟨⟩ | k
      · show Wb toyX 0 = 1
        rw [toy_blk]; simp
      · show Wb toyX 1 = 1
        rw [toy_blk]; simp
    have h : ((toyRk _ ⟨c, rfl⟩ : Fin _) : ℕ) < 1 := by
      have := (toyRk _ ⟨c, rfl⟩).2
      omega
    show ((toyRk _ ⟨c, rfl⟩ : Fin _) : ℕ) = _
    rcases c with ⟨⟩ | k
    · show _ = (blockLayout toyX).2[0]!
      rw [Nat.lt_one_iff.mp h]; decide
    · show _ = (blockLayout toyX).2[1]!
      rw [Nat.lt_one_iff.mp h]; decide
  hencB := toy_hencB
end Toy

section Can
open NockvmE2E.Exec.V NockvmE2E.Exec.VL

theorem foldl_inv' {α β : Type} (Pr : β → Prop) (f : β → α → β) : ∀ (l : List α) (b : β), Pr b →
    (∀ b a, a ∈ l → Pr b → Pr (f b a)) → Pr (l.foldl f b)
  | [], b, h, _ => h
  | a :: l, b, h, hf => foldl_inv' Pr f l _ (hf b a (by simp) h) (fun b' a' ha' => hf b' a' (List.mem_cons_of_mem _ ha'))

theorem canon_vT_get' (vT : Array (Array VF.K3)) (hvT : ∀ a ∈ vT, ∀ x ∈ a, canon3 x) (c j : ℕ) : canon3 (vT[c]!)[j]! := by
  apply canon_getBang
  by_cases hcc : c < vT.size
  · rw [getElem!_pos vT c hcc]; exact hvT _ (Array.getElem_mem hcc)
  · rw [getElem!_neg vT c hcc]; intro x hx; exact absurd hx (Array.not_mem_empty x)

/-- coefficients and claimed values of the flat opening list are canonical -/
theorem openingList_can (XI : ExecInst) (cs : VF.K3) (hcs : canon3 cs) (vT : Array (Array VF.K3)) (vQ : Array VF.K3)
    (hvT : ∀ a ∈ vT, ∀ x ∈ a, canon3 x) (hvQ : ∀ x ∈ vQ, canon3 x) :
    ∀ o ∈ (openingList XI cs vT vQ).toList, canon3 o.2.2.1 ∧ canon3 o.2.2.2 := by
  have hQ := canon_getBang vQ hvQ
  have hT := canon_vT_get' vT hvT
  let Pst : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3 → Prop :=
    fun st => (∀ o ∈ st.1.toList, canon3 o.2.2.1 ∧ canon3 o.2.2.2) ∧ canon3 st.2
  have key : Pst ((List.range (XI.nc + XI.nq)).foldl
    (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) c =>
      match kindG XI c with
      | 0 | 1 => (List.range XI.r).foldl
          (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) o => (st.1.push (c, o, st.2, (vT[c]!)[o]!), VF.K3.mul st.2 cs)) st
      | 2 => (List.range XI.r).foldl
          (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) _ => (st.1.push (c, XI.r, st.2, (vT[c]!)[0]!), VF.K3.mul st.2 cs)) st
      | 3 => (st.1.push (c, XI.r + 1, st.2, vQ[c - XI.nc]!), VF.K3.mul st.2 cs)
      | _ => st)
    (#[], VF.K3.one)) := by
    apply foldl_inv'
    · exact ⟨by simp, canon3_one⟩
    · intro st c _ hst
      have hpush : ∀ (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) (c' o : ℕ) (v : VF.K3), Pst st → canon3 v →
          Pst (st.1.push (c', o, st.2, v), VF.K3.mul st.2 cs) := by
        intro st c' o v hs hv
        refine ⟨?_, canon3_mul _ _⟩
        intro o' ho'
        rw [Array.toList_push, List.mem_append] at ho'
        rcases ho' with h | h
        · exact hs.1 o' h
        · rw [List.mem_singleton] at h; subst h; exact ⟨hs.2, hv⟩
      show Pst (match kindG XI c with
      | 0 | 1 => (List.range XI.r).foldl
          (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) o => (st.1.push (c, o, st.2, (vT[c]!)[o]!), VF.K3.mul st.2 cs)) st
      | 2 => (List.range XI.r).foldl
          (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) _ => (st.1.push (c, XI.r, st.2, (vT[c]!)[0]!), VF.K3.mul st.2 cs)) st
      | 3 => (st.1.push (c, XI.r + 1, st.2, vQ[c - XI.nc]!), VF.K3.mul st.2 cs)
      | _ => st)
      split
      · exact foldl_inv' Pst _ _ _ hst (fun st' o _ h => hpush st' c o _ h (hT _ _))
      · exact foldl_inv' Pst _ _ _ hst (fun st' o _ h => hpush st' c o _ h (hT _ _))
      · exact foldl_inv' Pst _ _ _ hst (fun st' o _ h => hpush st' c _ _ h (hT _ _))
      · exact hpush _ _ _ _ hst (hQ _)
      · exact hst
  intro o ho
  exact key.1 o ho

theorem openPts_can (XI : ExecInst) (hppt : canon3 XI.ppt) (ζ : VF.K3) (hζ : canon3 ζ) :
    ∀ q : ℕ, canon3 (openPts XI ζ)[q]! := by
  intro q
  apply canon_getBang
  unfold openPts
  let Pst : Array VF.K3 × VF.K3 → Prop := fun st => (∀ x ∈ st.1, canon3 x) ∧ canon3 st.2
  have key : Pst ((List.range XI.r).foldl
      (fun (st : Array VF.K3 × VF.K3) _ => (st.1.push (VF.K3.mul ζ st.2), VF.K3.smul XI.hGen st.2)) (#[], VF.K3.one)) := by
    apply foldl_inv'
    · exact ⟨by simp, canon3_one⟩
    · intro st _ _ hst
      refine ⟨?_, canon3_smul _ _⟩
      intro x hx
      rw [Array.mem_push] at hx
      rcases hx with h | h
      · exact hst.1 x h
      · rw [h]; exact canon3_mul _ _
  intro x hx
  rw [Array.mem_push] at hx
  rcases hx with h | h
  · rw [Array.mem_push] at h
    rcases h with h | h
    · exact key.1 x h
    · rw [h]; exact hppt
  · rw [h]; exact hζ

end Can

section ValRS
open NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Merkle.Fri

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι Pt F Dg : Type} {colRound : ι → ℕ} [Fintype ι] [DecidableEq ι]
  [Fintype Pt] [DecidableEq Pt] [Fintype F] [DecidableEq F]
  [Finite Dg] [DecidableEq Dg]
  (md : PointMaskData colRound Pt F Dg)
  (R : RapStatement Φ K ι (Pt → F) colRound)
  [DecidableEq R.Mfin] [Finite R.Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound (Pt → F) r))
  (Ifin : OracleInterface R.Mfin) (S : Set Pt) (T : ι → Pt → F)

/-- the decoded opened value at every selected leaf of a covered position is `T` -/
def ValR : (r k : ℕ) →
    OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k)) → Prop
  | _, 0, _ => True
  | r, k + 1, (o, os) =>
      (∀ (c : {c : ι // colRound c = r}), ∀ x ∈ S, ∀ hs : o.selector.get (md.pos r (c, x)) = true,
        cast (md.hF r c) (codecDec (md.ne r) (md.enc r) (selectedValueAt o.values (md.pos r (c, x)) hs)) = T c.1 x) ∧
        ValR r.succ k os

/-- columns of an earlier block are not touched -/
theorem finalOfBK_fst_of_lt : (k r : ℕ) → (tr : Tr ι (Pt → F)) → (χ : Coins Φ K) →
    (q : (protocol (baseRounds Dg (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))).tree.ExecutionPath) →
    (c : ι) → colRound c < r → (RapP.finalOfBK md.toRapMaskData R I Ifin r k tr χ q).1 c = tr c
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, r, tr, χ, q, c, h => by
      show (RapP.finalOfBK md.toRapMaskData R I Ifin (r + 1) k (setCols r q.1 tr) (setBlock r q.2.1 χ) q.2.2).1 c = tr c
      rw [finalOfBK_fst_of_lt k (r + 1) _ _ q.2.2 c (by omega)]
      exact setCols_of_ne _ _ (by omega)

/-- **`finalOfBK_valR`**: with the selectors covering `S` and the decoded opened values equal to `T` on `S`, the trace written for
a column of the opened blocks is `T` on `S` -/
theorem finalOfBK_valR : (k r : ℕ) →
    (os : OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))) →
    (p : (protocol (MA.preRoundsK Dg (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))).tree.ExecutionPath) →
    (q : (protocol (baseRounds Dg (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))).tree.ExecutionPath) →
    (tr : Tr ι (Pt → F)) → (χ : Coins Φ K) →
    MA.AgreesPre (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k) os p q →
    CoversR md R I Ifin S r k os → ValR md R I Ifin S T r k os →
    ∀ c, r ≤ colRound c → colRound c < r + k → ∀ x ∈ S,
      (RapP.finalOfBK md.toRapMaskData R I Ifin r k tr χ q).1 c x = T c x
  | 0, r, _, _, _, _, _, _, _, _, c, h1, h2, x, hx => by omega
  | k + 1, r, (o, os), p, q, tr, χ, hq, ⟨hcov, hC⟩, ⟨hV, hVs⟩, c, h1, h2, x, hx => by
      obtain ⟨hc, hw, hrest⟩ := hq
      show (RapP.finalOfBK md.toRapMaskData R I Ifin (r + 1) k (setCols r q.1 tr) (setBlock r q.2.1 χ) q.2.2).1 c x = T c x
      by_cases h : colRound c = r
      · rw [finalOfBK_fst_of_lt md R I Ifin k (r + 1) _ _ q.2.2 c (by omega)]
        simp only [setCols, h, ↓reduceDIte]
        have hs := hcov ⟨c, h⟩ x hx
        have e1 := congrArg (fun v => selectedValueAt v (md.pos r (⟨c, h⟩, x)) hs) hw
        simp only [selectedValueAt_map, Fri.selectedValueAt_selectedValues] at e1
        rw [← hV ⟨c, h⟩ x hx hs, e1]
        exact (md.get_pos r q.1 ⟨c, h⟩ x).symm
      · exact finalOfBK_valR k r.succ os p.2.2 q.2.2 _ _ hrest hC hVs c (by omega) (by omega) x hx

/-- `ValR` of the embedded openings from the per-tree facts on `mkOpeningD (ts.getD (b - r) _) (md.skel b)` -/
theorem valR_openAll (S : Set Pt) (T : ι → Pt → F)
    (md : PointMaskData colRound Pt F DgJ8) (R : RapStatement Φ K ι (Pt → F) colRound)
    [DecidableEq R.Mfin] [Finite R.Mfin] (I : (r : ℕ) → OracleInterface (Cols colRound (Pt → F) r))
    (Ifin : OracleInterface R.Mfin) : (k r : ℕ) → (ts : List (FTree DgJ8)) →
    (∀ b, r ≤ b → b < r + k → ∀ (c : {c : ι // colRound c = b}), ∀ x ∈ S,
      ∀ (o : BatchOpening DgJ8 (md.skel b)),
      o = mkOpeningD (ts.getD (b - r) ⟨fun _ => false, fun _ => default, [], default⟩) (md.skel b) →
      ∀ hs : o.selector.get (md.pos b (c, x)) = true,
        cast (md.hF b c) (codecDec (md.ne b) (md.enc b) (selectedValueAt o.values (md.pos b (c, x)) hs)) = T c.1 x) →
    ValR md R I Ifin S T r k (openAllOf _ ts)
  | 0, _, _, _ => trivial
  | k + 1, r, ts, h => ⟨fun c x hx hs => h r le_rfl (by omega) c x hx _
        (by simp only [Nat.sub_self]; cases ts <;> rfl) hs,
      valR_openAll S T md R I Ifin k r.succ ts.tail (fun b hb1 hb2 c x hx o ho hs => h b (by omega) (by omega) c x hx o (by
        have e : ts.getD (b - r) ⟨fun _ => false, fun _ => default, [], default⟩ =
            ts.tail.getD (b - (r + 1)) ⟨fun _ => false, fun _ => default, [], default⟩ := by
          have e1 : b - r = (b - (r + 1)) + 1 := by omega
          rw [e1]; cases ts <;> simp
        rw [e]; exact ho) hs)⟩

end ValRS

section MdX
open NockvmE2E.Exec.Layout NockvmE2E.Exec.Cover NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.SM

theorem cast_dec_enc {A B D : Type} (e : A = B) (ne : Nonempty A) (encB : B ↪ D) (b : B) :
    cast e (codecDec ne ((Equiv.cast e).toEmbedding.trans encB) (encB b)) = b := by
  subst e
  simpa using codecDec_enc ne encB b

/-- **`mdX_dec_enc`**: in a block of positive width the codec decodes the encoding of a base element -/
theorem mdX_dec_enc {κ B Dg : Type} [Nonempty B] (XI : ExecInst) (hn1 : 1 ≤ XI.nD) (colR : κ → ℕ)
    (rk : ∀ r, {c : κ // colR c = r} ≃ Fin (Wb XI r)) (encB : B ↪ Dg) (r : ℕ) (h : 0 < Wb XI r)
    (c : {c : κ // colR c = r}) (b : B) :
    cast ((mdX XI hn1 colR rk encB).hF r c)
      (codecDec ((mdX XI hn1 colR rk encB).ne r) ((mdX XI hn1 colR rk encB).enc r) (encB b)) = b := by
  unfold mdX layoutPointMd
  simp only [dif_pos h]
  exact cast_dec_enc (if_pos h) _ encB b

end MdX

section RapOpen
open NockvmE2E.Exec.SM NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.V

/-- (twin of `E2EResid.tree_open` for the RAP trees `j < 4` of positive width; reuses `E2EResid.embed_tree_open`) the accepted
flat tree `j` is opened by `mkOpeningD` with the dense selector and the leaf values -/
theorem tree_open_rap (XI : ExecInst) (FS : FSFn) (zF : List ℕ) (π : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (hok : FlatOk XI (Hof skels h) FS zF π) (hlen : skels.length = 4 + XI.k)
    (hsk : ∀ j (hj : j < skels.length), skels.get ⟨j, hj⟩ = skelFlat XI j) (j : Fin skels.length) (h4 : j.1 < 4)
    (hW : 0 < (blockLayout XI).1[j.1]!) :
    ∃ pr, mkOpeningD (ftree XI π j.1) (skels.get j) =
      ⟨selOf (ftree XI π j.1).isSel (skels.get j) 0,
        valsOf (ftree XI π j.1).lv (skels.get j) (selOf (ftree XI π j.1).isSel (skels.get j) 0) 0, pr⟩ := by
  have hj4 : j.1 < 4 + XI.k := hlen ▸ j.2
  have hne : ¬ (j.1 < 4 ∧ (blockLayout XI).1[j.1]! = 0) := fun hh => by omega
  have hc := flatOk_trees XI (Hof skels h) FS zF π hok j.1 (List.mem_range.mpr hj4)
  obtain ⟨_, hgo⟩ := treeCheck_root XI (Hof skels h) π _ _ _ j.1 hc hne
  have hsp : WfSpec (if j.1 < 4 then ragSpec (blockLayout XI).1[j.1]! (2 ^ (XI.nD - 1))
      else friSpec (2 ^ (XI.nD - (j.1 - 3)))) ∧
      1 ≤ (if j.1 < 4 then ragSpec (blockLayout XI).1[j.1]! (2 ^ (XI.nD - 1))
        else friSpec (2 ^ (XI.nD - (j.1 - 3)))).total := by
    simp only [h4, ite_true]
    refine ⟨wf_ragSpec _ _ hW, ?_⟩
    simp only [ragSpec]
    exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (by omega)) hW
  have hlim := flatOk_limbs XI (Hof skels h) FS zF π hok
  have hcl : ∀ r, dgOk (if j.1 < 4 then [(π.vals[j.1]!)[r]!, 0, 0, 0, 0]
      else [(π.vals[j.1]!)[3 * r]!, (π.vals[j.1]!)[3 * r + 1]!, (π.vals[j.1]!)[3 * r + 2]!, 0, 0]) = true := by
    intro r
    have hz : NockvmE2E.Exec.VF.based 0 = true := by simp [NockvmE2E.Exec.VF.based, PN_eq]; exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
    split <;> simp [dgOk, NockvmE2E.Exec.VF.based, PN_eq, arr_get_lt (a := π.vals) hlim.2.2.2, hz] <;>
      exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
  exact embed_tree_open skels h j _ hsp.1 (hsk j.1 j.2) hsp.2 _ (selsOf_pw XI π j.1 hj4) _ _ _ hcl
    (sibs_ok (flatOk_allCanon XI _ FS zF π hok) j.1) (by simpa using hgo)

/-- the opened value at a selected leaf of an accepted RAP tree of positive width is the tree's leaf value -/
theorem open_val_rap (XI : ExecInst) (FS : FSFn) (zF : List ℕ) (π : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (hok : FlatOk XI (Hof skels h) FS zF π) (hlen : skels.length = 4 + XI.k)
    (hsk : ∀ j (hj : j < skels.length), skels.get ⟨j, hj⟩ = skelFlat XI j) (j : Fin skels.length) (h4 : j.1 < 4)
    (hW : 0 < (blockLayout XI).1[j.1]!)
    (tr : FTree DgJ8) (htr : tr = ftree XI π j.1) (sk : Skeleton) (hs : sk = skels.get j) :
    ∀ t (ht : (mkOpeningD tr sk).selector.get t = true),
      selectedValueAt (mkOpeningD tr sk).values t ht = tr.lv (leafNum t) := by
  subst htr hs
  obtain ⟨pr, hpr⟩ := tree_open_rap XI FS zF π skels h hok hlen hsk j h4 hW
  intro t ht
  revert ht
  rw [hpr]
  intro ht
  exact (selectedValueAt_valsOf _ t _ 0 ht).trans (by rw [Nat.zero_add])

end RapOpen

section Closed

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (Op : Type) [Finite Op] [DecidableEq Op]
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin nb
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.Layout NockvmE2E.Exec.SF

set_option hygiene false in
local notation "Q0" => q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p

variable (vTOf : Array (Array VF.K3) → ι × Fin r → KC) (colN : ι ⊕ Fin P.nq → ℕ)
  (rk : ∀ b, {c : ι ⊕ Fin P.nq // P.colRoundX c = b} ≃ Fin (Wb XI b)) (encB : B ↪ DgJ8)

/-- **`W0Link` from `OpsU`** (π-free instance fact) + the per-path links the acceptance supplies -/
theorem w0link_of_opsU (hok : FlatOk XI H FS zF π) (O : OpsU XI P A e vTOf colN rk encB)
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (hG : ∀ i : Fin (m + 1), G (MA.sndB Dg (RM) (BM) (Q0)).2.1 i = toKV (csOf XI FS zF π) ^ (i : ℕ))
    (hζ : toKV (zetaOf XI FS zF π) = chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0) P.z)
    (hVT : (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)).2.1 = vTOf π.vT)
    (hQ : ∀ q : Fin P.nq, toKV π.vQ[q.1]! = (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)).2.2 q)
    (hbase : ∀ (j : Fin XI.l) (g : ℕ) (hR : Rd XI.nD π.pos[j.1]! 0 g) (col : ι ⊕ Fin P.nq),
      homV.ψ (baseAtOf XI π (colN col) g) =
        liftW ((trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) col) ⟨g, by simpa using hR.1⟩) :
    W0Link XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L Op decode z p := by
  have hsh := vshape_of_flat XI H FS zF π hok
  have hac := allCanon_of_flatOk XI H FS zF π hok
  obtain ⟨_, _, _, _, hvT, hvQ, _, hvals⟩ := allCanon_parts XI zF π (flatOk_allCanon XI H FS zF π hok)
  have hcanO : ∀ g, ∀ o ∈ (openingList XI (csOf XI FS zF π) π.vT π.vQ).toList,
      homV.C o.2.2.1 ∧ homV.C o.2.2.2 ∧ homV.Cg (baseAtOf XI π o.1 g) := by
    intro g o ho
    have h12 := openingList_can XI _ (canon3_ofLimbs _ (hac.chal 6)) π.vT π.vQ hvT hvQ o ho
    refine ⟨h12.1, h12.2, ?_⟩
    show canon (baseAtOf XI π o.1 g)
    unfold baseAtOf
    exact canon_ofNat _ (arr_get_lt hvals _ _)
  have hcanP : ∀ q, q < XI.r + 2 → homV.C (openPts XI (zetaOf XI FS zF π))[q]! := fun q _ =>
    openPts_can XI (instCan_of_flatOk XI H FS zF π hok).ppt _ (canon3_zetaOf XI FS zF π hac.chal) q
  intro j g hg
  have hn32 := nD_le_of_verify XI H FS zF π hv
  have hshift : XI.dShift = 7 := (flatOk_params XI H FS zF π hok).1
  have hgen := flatOk_dGen XI H FS zF π hok
  have hg1 : g < 2 ^ XI.nD := by simpa using hg.1
  have hnD : 0 < XI.nD := by have := (flat_shape XI H FS zF π hok).1; omega
  let u : Fin (2 ^ (XI.nD - 0)) := ⟨g, by simpa using hg1⟩
  have hy : ((((ωS).subdomain 0).equivToFinset u).val) = Yp (homV.ψ XI.dShift) (homV.ψ XI.dGen) 0 g := by
    show _ = Yp (psiV XI.dShift) (psiV XI.dGen) 0 g
    rw [psiV_shift XI hshift, hgen]
    exact pt_val XI.nD hn32 0 0 hnD rfl u
  have hω : ωS ⟨g, hg1⟩ = homV.ψ XI.dShift * homV.ψ XI.dGen ^ g := by
    show _ = psiV XI.dShift * psiV XI.dGen ^ g
    rw [psiV_shift XI hshift, hgen, Inst.smoothDomain_apply]
  have hy2 : ((((ωS).subdomain 0).equivToFinset u).val) = ωS ⟨g, hg1⟩ := by
    rw [hy, hω]; simp [Yp]
  have hops := (O.hopsF (csOf XI FS zF π) (zetaOf XI FS zF π) π.vT π.vQ hsh).imp
    (S := fun (o : ℕ × ℕ × VF.K3 × VF.K3) (jj : Fin (m + 1)) =>
      o.2.1 < XI.r + 2 ∧ homV.φ o.2.2.1 = toKV (csOf XI FS zF π) ^ (jj : ℕ) ∧
        homV.φ (openPts XI (zetaOf XI FS zF π))[o.2.1]! = ptOf P A e (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) jj ∧
        homV.φ o.2.2.2 = valOf P R0 e (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) jj ∧
        homV.ψ (baseAtOf XI π o.1 g) = liftW ((trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) (colOf P e jj)) ⟨g, hg1⟩)
    (fun o jj ⟨h1, h2, h3, h4, h5⟩ => by
      refine ⟨h1, h2, ?_, ?_, ?_⟩
      · show toKV _ = _
        rw [h3]; unfold ptOf; rw [← hζ]
      · show toKV _ = _
        rw [h4]; unfold valOf
        rcases e jj with ck | q
        · simp [hVT]
        · simp [hQ]
      · rw [h5]; exact hbase j g hg (colOf P e jj))
  refine ⟨((ωS).subdomain 0).equivToFinset u, hy, ?_⟩
  have := initialOracle_combined s1 P A R0 e G (MA.sndB Dg (RM) (BM) (Q0)).2.1 (toKV (csOf XI FS zF π)) hG XI
    (openPts XI (zetaOf XI FS zF π)) (openingList XI (csOf XI FS zF π) π.vT π.vQ).toList (baseAtOf XI π)
    (trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0))
    (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0))
    (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) ⟨g, hg1⟩ _ hy2 hω hops (hcanO g) hcanP
  refine this.trans ?_
  unfold Wf word0Of
  simp only [ite_true]
  rw [deepWord_eq]

end Closed

section PRE
open NockvmE2E.Exec.E2ELR NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA
section UL

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst

variable (XI : ExecInst) (hn : XI.nD ≤ 32)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD hn
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ XI.nD)
variable (Op : Type) [Finite Op] [DecidableEq Op]
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ωS) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L


variable (decode : Op → OpenAll Dg (merkleSkels (MC)))
  {Op' : Type}

set_option quotPrecheck false in
set_option hygiene false in
local notation "PATH" => (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath
set_option hygiene false in
local notation "CHI" p => chiQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)
set_option hygiene false in
local notation "FINM" p => finMQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)

set_option hygiene false in
local notation "FM" => Fri.friMerkleMask s1 d XI.l L Dg enc

structure UniLinksN (dY : List ℕ → Dg) (ds : MDec (MC)) (vTOf : Array (Array VF.K3) → ι × Fin r → KC) : Prop where
  hPa : Φ.sampledAfter P.a = 2
  hPz : Φ.sampledAfter P.z = 3
  /-- α = the K3 of the limbs of block 2's challenge -/
  hαC : ∀ c : Block Φ KC 2, toKV (VF.K3.ofLimbs (ds.2.2.2.1.encC c)) = c ⟨P.a, hPa⟩
  /-- ζ = the K3 of the limbs of block 3's challenge -/
  hζC : ∀ c : Block Φ KC 3, toKV (VF.K3.ofLimbs (ds.2.2.2.2.1.encC c)) = c ⟨P.z, hPz⟩
  /-- the `Mfin` decoder reads `vQ` and `vT` -/
  hQU : ∀ vT vQ, VShape XI vT vQ → ∀ j : Fin P.nq, (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)).2.2 j = toKV vQ[j.1]!
  hVT : ∀ vT vQ, VShape XI vT vQ → (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)).2.1 = vTOf vT
  hlenU : ∀ slots ζ vT, (termsAt XI slots ζ vT).length = P.ns
  hdagU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
    CanonIn (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) ζ vT →
    ∀ i : Fin P.ns, (termsAt XI (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) ζ vT)[i.1]? =
      some (A.Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOf vT))
  hptsU : ∀ (ζ : VF.K3) (ck : ι × Fin r), ∃ pt ∈ (openPts XI ζ).toList, toKV pt = A.pt ck.1 ck.2 (toKV ζ)
  hRVU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
    VShape XI vT vQ →
    PR (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) (pubAt XI vT) →
    RestV (ds.1.decM []) (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3)
  hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i)
  he : P.e = 3
  hnq : XI.nq = P.nq
  hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j

end UL
end PRE

section PRE
open NockvmE2E.Exec.E2ELR NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA
section UL

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ XI.nD)
variable (Op : Type) [Finite Op] [DecidableEq Op]
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ωS) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L


variable (decode : Op → OpenAll Dg (merkleSkels (MC)))
  {Op' : Type}

set_option quotPrecheck false in
set_option hygiene false in
local notation "PATH" => (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath
set_option hygiene false in
local notation "CHI" p => chiQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)
set_option hygiene false in
local notation "FINM" p => finMQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)

set_option hygiene false in
local notation "FM" => Fri.friMerkleMask s1 d XI.l L Dg enc

variable (dY : List ℕ → Dg) (ds : MDec (MC)) (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
theorem uniLinks'_of_N
    (U : UniLinksN XI (nD_le_of_verify XI H FS zF π hv) P A R0 Rest RestV e I0 I Ifin d Dg enc md L PR dY ds vTOf) :
    UniLinks' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L PR dY ds vTOf :=
  ⟨U.hPa, U.hPz, U.hαC, U.hζC, U.hQU, U.hVT, U.hlenU, U.hdagU, U.hptsU, U.hRVU, U.hH, U.he, U.hnq, U.hcw⟩
end UL
end PRE

section Main
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM

variable (XI0 : ExecInst) (hn32 : (XI170 XI0).nD ≤ 32)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD hn32
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ (XI170 XI0).nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ (XI170 XI0).nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ (XI170 XI0).nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData P.colRoundX (Fin (2 ^ (XI170 XI0).nD)) B DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ (XI170 XI0).nD)
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 d (XI170 XI0).l DgJ8 enc L

set_option hygiene false in
local notation "GG" => CoreDefinitions.univariatePowersGenerator KC m
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))

theorem hU_of_N {Statement Salt : Type} (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
    (U : UniLinksN (XI170 XI0) hn32 P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf (mdAppend (RM) (BM) da (dsb, dsm)) vTOf) :
    ∀ g z π (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π),
    UniLinks' (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
      (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv
      P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf (mdAppend (RM) (BM) da (dsb, dsm)) vTOf :=
  fun g z π hv => uniLinks'_of_N _ _ _ _ _ hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf _ vTOf U

theorem base_link {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt]
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32)
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC) (colN : ι ⊕ Fin P.nq → ℕ) (O : OpsU (XI170 XI0) P A e vTOf colN rk encB)
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)
    (z : Statement × Salt) (π : FlatProof)
    (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π)
    (j : Fin (XI170 XI0).l) (x : ℕ) (hR : Rd (XI170 XI0).nD π.pos[j.1]! 0 x) (col : ι ⊕ Fin P.nq) :
    homV.ψ (baseAtOf (XI170 XI0) π (colN col) x) =
      liftW ((trQ P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L
        (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (OPN) id
          (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))) col)
        ⟨x, by simpa using hR.1⟩ := by
  classical
  have hok := (verifyFlat_iff (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π).mp hv
  have hr : π.roots.size = 4 + (XI170 XI0).k := by
    obtain ⟨_, _, _, _, h5, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    exact h5.1.1
  have hroots : pathRootsK DgJ8 (OPN) (MC) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π) =
      (rootsOf π, openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) := by
    unfold EP
    rw [pathRootsK_embed dgOf z (MC) (mdAppend (RM) (BM) da (dsb, dsm)) _ _ (fun k => g (.inr k)),
      merkleMsgs_msC (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L rfl hr]
  have hlist := hsk_list (S := KC) (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L encB rk hmd hL rfl
  have hlen : (merkleSkels (MC)).length = 4 + (XI170 XI0).k := by rw [hlist]; simp
  have hsk : ∀ j (hj : j < (merkleSkels (MC)).length), (merkleSkels (MC)).get ⟨j, hj⟩ = skelFlat (XI170 XI0) j := by
    intro j hj; simp [hlist]
  have hsel := selLinkC_embed (S := KC) (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L encB rk hmd hL rfl
    (fun q => g (.inl q)) rfl
  have hq0 : q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (OPN) id (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π) =
      q0Of (MC) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π) :=
    congrArg (fun r : List DgJ8 × OPN => q0Of (MC) r.2 (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)) hroots
  have hok' : FlatOk (XI170 XI0) (Hof (merkleSkels (MC)) (fun q => g (.inl q))) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π := hok
  have hlim := flatOk_limbs (XI170 XI0) _ _ (encZ z) π hok
  have hvalsp : ∀ a r, (π.vals[a]!)[r]! < NockvmE2E.Exec.p := fun a r =>
    arr_get_lt (a := π.vals) (fun v hv x hx => hlim.2.2.2 v hv x hx) a r
  have hmdsk : ∀ b, b < 4 → md.skel b = skelFlat (XI170 XI0) b := by
    intro b hb
    subst hmd
    simp only [skelFlat, hb, ite_true]
    rfl
  -- the audited trace values at the read set
  obtain ⟨vAt, hvAt⟩ : ∃ f : ι ⊕ Fin P.nq → Fin (2 ^ (XI170 XI0).nD) → ℕ, ∀ c x, f c x =
      (π.vals[P.colRoundX c]!)[lb (selsOf (XI170 XI0) π)[P.colRoundX c]!
        ((x.val % 2 ^ ((XI170 XI0).nD - 1)) * 2 * Wb (XI170 XI0) (P.colRoundX c) +
          (x.val / 2 ^ ((XI170 XI0).nD - 1)) * Wb (XI170 XI0) (P.colRoundX c) + (rk (P.colRoundX c) ⟨c, rfl⟩).val)]! :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ι ⊕ Fin P.nq → Fin (2 ^ (XI170 XI0).nD) → B, ∀ c x,
      encB (T c x) = dgOf [vAt c x, 0, 0, 0, 0] ∧ algebraMap B KC (T c x) = homV.ψ (UInt64.ofNat (vAt c x)) :=
    ⟨fun c x => Classical.choose (O.hencB (vAt c x) (by rw [hvAt]; exact hvalsp _ _)),
     fun c x => Classical.choose_spec (O.hencB (vAt c x) (by rw [hvAt]; exact hvalsp _ _))⟩
  set ω := openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π) with hω
  have hag := (Agrees_append (RM) (BM) ω (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π) (q0Of (MC) ω (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))).mp (NockvmE2E.Exec.SL.agree_q0 (MC) ω (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))
  have hpre : AgreesPre (RapP.rapMerkleMask Φ KC md.toRapMaskData (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I Ifin 0 4)
      (fstOpen (RM) (BM) ω) (fstK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.2 (fstB DgJ8 (RM) (BM) (q0Of (MC) ω (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))).2.2 := hag.1.2.2
  let S : Set (Fin (2 ^ (XI170 XI0).nD)) := {y | ∃ j : Fin (XI170 XI0).l, Rd (XI170 XI0).nD π.pos[j.1]! 0 y.val}
  have hcov : CoversR md (Rok (P.statement R0 Rest) (friPlan (ω := ωS) P A R0 Rest RestV e)) I Ifin S 0 4 (fstOpen (RM) (BM) ω) := by
    refine coversR_of md (Rok (P.statement R0 Rest) (friPlan (ω := ωS) P A R0 Rest RestV e)) I Ifin S (QR (XI170 XI0) π) ?_ 4 0 _ hsel.1
    intro r c x hx
    obtain ⟨j, hj⟩ := hx
    have hn1 : 1 ≤ (XI170 XI0).nD := by
      have := (flat_shape (XI170 XI0) _ _ (encZ z) π hok).1; omega
    have hmem : π.pos[j.1]! ∈ π.pos.toList := by
      have hsz := (flat_shape (XI170 XI0) _ _ (encZ z) π hok).2
      have : j.1 < π.pos.size := by rw [hsz]; exact j.2
      rw [getElem!_pos π.pos j.1 this]; simp
    have hW : 0 < Wb (XI170 XI0) r := lt_of_le_of_lt (Nat.zero_le _) (rk r c).2
    have hr := lt4_of_pos (XI170 XI0) r hW
    subst hmd
    refine ⟨hr, ?_⟩
    rw [mdX_leafNum (XI170 XI0) hn1 _ rk encB r hW c x, selsR (XI170 XI0) π r hr]
    have hx2 : x.val / 2 ^ ((XI170 XI0).nD - 1) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [mul_comm]; exact lt_of_lt_of_eq x.2 (pow_half _ hn1)
    have := leafPos_mem_treeSel (XI170 XI0) (Wb (XI170 XI0) r) r π.pos hr (π.pos[j.1]!) (rk r c).val hmem (rk r c).2 _ hx2
    have hj2 : x.val % 2 ^ ((XI170 XI0).nD - 1) = π.pos[j.1]! % 2 ^ ((XI170 XI0).nD - 1) := by
      simpa using hj.2
    rw [Nat.mod_mod, ← hj2] at this
    exact this
  have hval : ValR md (Rok (P.statement R0 Rest) (friPlan (ω := ωS) P A R0 Rest RestV e)) I Ifin S T 0 4 (fstOpen (RM) (BM) ω) := by
    have e1 : fstOpen (RM) (BM) ω = openAllOf (merkleSkels (RM)) (flatTrees (XI170 XI0) π) := fstOpen_openAllOf _ _ _
    rw [e1]
    refine valR_openAll S T md (Rok (P.statement R0 Rest) (friPlan (ω := ωS) P A R0 Rest RestV e)) I Ifin 4 0 (flatTrees (XI170 XI0) π) ?_
    intro b _ hb c x hx o ho hs
    obtain ⟨c, hc⟩ := c
    subst hc
    have hb4 : P.colRoundX c < 4 := by omega
    have hj : P.colRoundX c < (merkleSkels (MC)).length := by omega
    have hW : 0 < (blockLayout (XI170 XI0)).1[P.colRoundX c]! := lt_of_le_of_lt (Nat.zero_le _) (rk _ ⟨c, rfl⟩).2
    have hget : (flatTrees (XI170 XI0) π).getD (P.colRoundX c - 0) ⟨fun _ => false, fun _ => default, [], default⟩ =
        ftree (XI170 XI0) π (P.colRoundX c) := by
      rw [Nat.sub_zero]; exact ftree_getD (XI170 XI0) π _ (by omega)
    have hsL : md.skel (P.colRoundX c) = (merkleSkels (MC)).get ⟨P.colRoundX c, hj⟩ := (hmdsk _ hb4).trans (hsk _ hj).symm
    have hv := open_val_rap (XI170 XI0) _ _ π (merkleSkels (MC)) _ hok' hlen hsk ⟨P.colRoundX c, hj⟩ hb4 hW
      _ hget _ hsL
    subst ho
    rw [hv _ hs, hget]
    subst hmd
    rw [mdX_leafNum (XI170 XI0) hn1 _ rk encB _ hW ⟨c, rfl⟩ x]
    have hlv : ∀ i, (ftree (XI170 XI0) π (P.colRoundX c)).lv i =
        dgOf [(π.vals[P.colRoundX c]!)[lb (selsOf (XI170 XI0) π)[P.colRoundX c]! i]!, 0, 0, 0, 0] := by
      intro i
      simp [ftree, ftreeOf, hb4]
    rw [hlv]
    have h1 := (hT c x).1
    rw [hvAt] at h1
    rw [← h1]
    exact mdX_dec_enc (XI170 XI0) hn1 P.colRoundX rk encB _ hW ⟨c, rfl⟩ (T c x)
  have hkey := finalOfBK_valR md (Rok (P.statement R0 Rest) (friPlan (ω := ωS) P A R0 Rest RestV e)) I Ifin S T 4 0 (fstOpen (RM) (BM) ω) (fstK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.2
    (fstB DgJ8 (RM) (BM) (q0Of (MC) ω (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))).2.2 (fun _ => default) (fun _ => default) hpre hcov hval col (Nat.zero_le _)
    (by have := O.hcR col; omega) ⟨x, by simpa using hR.1⟩ ⟨j, hR⟩
  have hx1 : x < 2 ^ (XI170 XI0).nD := by simpa using hR.1
  have hb : baseAtOf (XI170 XI0) π (colN col) x = UInt64.ofNat (vAt col ⟨x, hx1⟩) := by
    rw [hvAt]
    unfold baseAtOf
    simp only []
    rw [O.hcolB col, ← O.hrkV _ ⟨col, rfl⟩]
  rw [hq0, hb]
  refine Eq.trans ?_ (congrArg (algebraMap B KC) hkey).symm
  exact ((hT col ⟨x, hx1⟩).2).symm

theorem hW0_of_opsU {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt]
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32)
    (U : UniLinksN (XI170 XI0) hn32 P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf (mdAppend (RM) (BM) da (dsb, dsm)) vTOf)
    (colN : ι ⊕ Fin P.nq → ℕ) (O : OpsU (XI170 XI0) P A e vTOf colN rk encB)
    (hcsC : ∀ c : KC, toKV (VF.K3.ofLimbs (dsb.encC c)) = c) :
    ∀ g z π (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π),
    E2EFri.W0Link (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
      (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d GG DgJ8 enc md L (OPN) id z
      (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π) := by
  classical
  intro g z π hv
  have hok := (verifyFlat_iff (XI170 XI0) _ _ (encZ z) π).mp hv
  have hr : π.roots.size = 4 + (XI170 XI0).k := by
    obtain ⟨_, _, _, _, h5, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    exact h5.1.1
  have hmsd := embedMsgs_dec dgOf (MC) (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π))
    (openAllOf (merkleSkels (MC)) []) (msgsOf (XI170 XI0) π).toList
    (by rw [length_msgsOf (XI170 XI0) π hr, length_msC (XI170 XI0) _ _ (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L rfl])
  have hlenm : (msgsOf (XI170 XI0) π).size = 9 + (XI170 XI0).k := by
    have := length_msgsOf (XI170 XI0) π hr
    simpa using this
  have hch : E2ELR.ChalsDec (XI170 XI0) _ _ (encZ z) π hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L (OPN) dgOf
      (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) [])
      (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π) := by
    intro i hi hnl
    exact chalsOf_dec (XI170 XI0) π encZ decZ hz _ (mDecs dgOf (MC) (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) []))
      (fun k => g (.inr k)) z _ hmsd _ (fun _ _ => rfl) i (by omega) hnl
  obtain ⟨hm0, hm5⟩ := E2ELR.embed_msgs (XI170 XI0) _ _ (encZ z) π hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L (OPN) dgOf
    (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) z (fun k => g (.inr k))
  have D := deepLinkC_of' (XI170 XI0) _ _ (encZ z) π hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L (OPN) PR id _ dgOf
    (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) []) vTOf
    (uniLinks'_of_N _ _ _ _ _ hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf _ vTOf U) hok hch hm5
  have hsh := E2ELR.vshape_of_flat (XI170 XI0) _ _ (encZ z) π hok
  have hVT : (finMQ P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L
      (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (OPN) id
        (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))).2.1 = vTOf π.vT := by
    refine Eq.trans ?_ (U.hVT _ _ hsh)
    exact congrArg (fun x => x.2.1) hm5
  have hG : ∀ i : Fin (m + 1), GG (MA.sndB DgJ8 (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (OPN) id
        (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))).2.1 i
      = toKV (csOf (XI170 XI0) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π) ^ (i : ℕ) := by
    intro i
    have h6 := hch 6 (by omega) (by simp [roundNl])
    have h1 : (encPathD (compiledRoundsK DgJ8 (OPN) (MC))
        (mDecs dgOf (MC) (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) [])) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).getD 6 [] =
        dsb.encC (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.1 :=
      E2EFri.encPathD_append_getD dgOf (openAllOf (merkleSkels (MC)) []) (RM) (BM) da (dsb, dsm) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π) 0
    have hcs : toKV (csOf (XI170 XI0) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π) =
        (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.1 := by
      have hcs' : csOf (XI170 XI0) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π =
          VF.K3.ofLimbs (dsb.encC (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.1) :=
        congrArg VF.K3.ofLimbs (h6.trans h1)
      exact (congrArg toKV hcs').trans (hcsC _)
    have hq : ((MA.sndB DgJ8 (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (OPN) id (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π))).2.1 : KC) =
        (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.1 := by
      unfold q0P
      rw [sndB_q0Of]
      rfl
    have key : ∀ c : KC, GG c i = c ^ (i : ℕ) := fun c => rfl
    refine (key _).trans ?_
    exact congrArg (fun c : KC => c ^ (i : ℕ)) (hq.trans hcs.symm)
  exact w0link_of_opsU (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
    (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d GG DgJ8 enc md L (OPN) vTOf colN rk encB hok O id z _
    hG D.hζ hVT D.hQ (fun j x hR col => base_link XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ da dsb dsm encB rk hn1 hmd hL vTOf colN O g z π hv j x hR col)

/-- assembly check: `Resid` from `UniLinksN` + `OpsU` + `hcsC` + the five  fields -/
theorem resid_of {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt]
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32)
    (U : UniLinksN (XI170 XI0) hn32 P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf (mdAppend (RM) (BM) da (dsb, dsm)) vTOf)
    (colN : ι ⊕ Fin P.nq → ℕ) (O : OpsU (XI170 XI0) P A e vTOf colN rk encB)
    (hcsC : ∀ c : KC, toKV (VF.K3.ofLimbs (dsb.encC c)) = c)
    (RC : Resid XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ da dsb dsm vTOf) :
    Resid XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ da dsb dsm vTOf :=
  { RC with
    hU := hU_of_N XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ da dsb dsm vTOf U
    hW0 := hW0_of_opsU XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ hz da dsb dsm vTOf encB rk hn1 hmd hL U colN O hcsC }

end Main

end NockvmE2E.Exec.E2EW0
#print axioms NockvmE2E.Exec.E2EW0.foldl_inv'
#print axioms NockvmE2E.Exec.E2EW0.canon_vT_get'
#print axioms NockvmE2E.Exec.E2EW0.openingList_can
#print axioms NockvmE2E.Exec.E2EW0.openPts_can
#print axioms NockvmE2E.Exec.E2EW0.finalOfBK_fst_of_lt
#print axioms NockvmE2E.Exec.E2EW0.finalOfBK_valR
#print axioms NockvmE2E.Exec.E2EW0.valR_openAll
#print axioms NockvmE2E.Exec.E2EW0.cast_dec_enc
#print axioms NockvmE2E.Exec.E2EW0.mdX_dec_enc
#print axioms NockvmE2E.Exec.E2EW0.tree_open_rap
#print axioms NockvmE2E.Exec.E2EW0.open_val_rap
#print axioms NockvmE2E.Exec.E2EW0.w0link_of_opsU
#print axioms NockvmE2E.Exec.E2EW0.uniLinks'_of_N
#print axioms NockvmE2E.Exec.E2EW0.hU_of_N
#print axioms NockvmE2E.Exec.E2EW0.base_link
#print axioms NockvmE2E.Exec.E2EW0.hW0_of_opsU
#print axioms NockvmE2E.Exec.E2EW0.resid_of
#print axioms NockvmE2E.Exec.E2EW0.toy_blk
#print axioms NockvmE2E.Exec.E2EW0.toy_card
#print axioms NockvmE2E.Exec.E2EW0.toy_hencB
#print axioms NockvmE2E.Exec.E2EW0.toyOps
