/-
  NockvmE2E/Exec/Sound.lean   (proof-only)

  `verifyFlatE_ok_iff`: the (total) flat verifier accepts iff the Prop `FlatOk` (a transcription of its `Except` chain with every
  `ckE b m >>= _` read as `b = true ∧ _`, `forM` as `∀`).  Everything downstream (Merkle, DeepCheck, OffDom, FRI) is read off `FlatOk`.
-/
import NockvmE2E.Exec.Verify
import NockvmE2E.Exec.VLink
import NockvmE2E.Exec.SoundMerkle
import NockvmE2E.Exec.SoundLocal
import NockvmE2E.Exec.SoundFri
import NockvmE2E.Exec.Embed
import Mathlib.Data.List.Basic
set_option autoImplicit false

namespace NockvmE2E.Exec.V

theorem ckE_bind (b : Bool) (m : String) (f : Unit → Except String Unit) :
    (ckE b m >>= f) = .ok () ↔ b = true ∧ f () = .ok () := by
  unfold ckE; cases b <;> simp [bind, Except.bind, pure, Except.pure]

theorem bind_unit_ok (e : Except String Unit) (f : Unit → Except String Unit) :
    (e >>= f) = .ok () ↔ e = .ok () ∧ f () = .ok () := by
  cases e <;> simp [bind, Except.bind]

theorem bind_ok {α : Type} (e : Except String α) (f : α → Except String Unit) :
    (e >>= f) = .ok () ↔ ∃ r, e = .ok r ∧ f r = .ok () := by
  cases e <;> simp [bind, Except.bind]

theorem ckE_ok (b : Bool) (m : String) : ckE b m = .ok () ↔ b = true := by
  unfold ckE; cases b <;> simp [pure, Except.pure]

theorem forM_ok {α : Type} (l : List α) (f : α → Except String Unit) :
    l.forM f = .ok () ↔ ∀ x ∈ l, f x = .ok () := by
  induction l with
  | nil => simp [List.forM, pure, Except.pure]
  | cons a l ih =>
    simp only [List.forM_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    cases h : f a <;> simp [bind, Except.bind, h]

open NockvmE2E.Exec.VF

/-- `verifyFlatE` accepts, as a proposition (transcribed from `Verify.lean`, multi-chip ) -/
def FlatOk (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) : Prop :=
  let nB := 4
  let k := XI.k
  let ncq := XI.nc + XI.nq
  allCanon XI z π = true ∧
  (XI.colKind.size == XI.nc && XI.blockOf.size == ncq && XI.pre.size == XI.nc && XI.nCoins.size == 2) = true ∧
  (XI.nD ≥ k + 1 && XI.nq % 3 == 0 && XI.r ≥ 1 && XI.hN ≥ 1 && XI.l ≥ 1) = true ∧
  paramsOk XI = true ∧
  (π.roots.size == nB + k && π.vals.size == nB + k && π.sibs.size == nB + k) = true ∧
  (π.vT.size == XI.nc && π.vQ.size == XI.nq && π.pfinal.size == XI.d && π.pos.size == XI.l) = true ∧
  (∀ c ∈ List.range XI.nc,
    (π.vT[c]!.size == vTLen XI c) = true) ∧
  tabsOk XI = true ∧
  (π.pos.all (· < 2 ^ XI.nD)) = true ∧
  let pfEnc := π.pfinal.toList.flatMap VF.K3.limbs
  let msgs : Array (List Nat) :=
    #[[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg π.vT π.vQ, [], []] ++ π.roots.extract nB (nB + k) ++ #[pfEnc]
  let nlOf := roundNl XI
  let chals : Array (List Nat) := (Array.range msgs.size).map fun i =>
    if nlOf i == 0 then [] else FS (z :: (msgs.extract 0 (i + 1)).toList) (nlOf i)
  (chals.all (·.all based)) = true ∧
  let coins0 := k3s chals[1]! XI.nCoins[0]!
  let coins1 := k3s chals[2]! XI.nCoins[1]!
  let alpha := VF.K3.ofLimbs chals[3]!
  let zeta := VF.K3.ofLimbs chals[4]!
  let cs := VF.K3.ofLimbs chals[6]!
  let alphas : Array VF.K3 := (Array.range (k + 1)).map fun w => VF.K3.ofLimbs chals[7 + w]!
  let xs : Array Nat := chals[8 + k]!.toArray.map (· % 2 ^ XI.nD)
  (π.pos == xs) = true ∧
  let half0 := 2 ^ (XI.nD - 1)
  let (W, rank) := blockLayout XI
  (∀ c ∈ List.range ncq, decide (XI.blockOf[c]! < nB) = true) ∧
  let sels : Array (Array Nat) := (Array.range (nB + k)).map fun j => treeSel XI (W.getD j 0) j π.pos
  (∀ j ∈ List.range (nB + k), treeCheck XI H π W half0 sels j = .ok ()) ∧
  let slots : Array VF.K3 := XI.derived.toList.foldl (fun (slots : Array VF.K3) (be : Nat × Nat) => slots.push (VF.K3.pow slots[be.1]! be.2)) (coins0 ++ coins1)
  let zh := ((List.range XI.hN).foldl
    (fun (st : VF.K3 × VF.G) _ => (VF.K3.mul st.1 (VF.K3.sub zeta (VF.K3.ofG st.2)), VF.mul st.2 XI.hGen)) (VF.K3.one, XI.hShift)).1
  let omZ := VF.K3.smul XI.hGen zeta
  let curNxt := (List.range XI.nc).foldl
    (fun (st : Array VF.K3 × Array VF.K3) c =>
      match XI.colKind[c]! with
      | 0 => (st.1.set! c (π.vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (π.vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (VF.K3.hornerG XI.pre[c]! zeta), st.2.set! c (VF.K3.hornerG XI.pre[c]! omZ))
      | _ => st)
    (Array.replicate ncq VF.K3.zero, Array.replicate ncq VF.K3.zero)
  (∀ c ∈ XI.pubOf.toList, (decide (c < XI.nc) && XI.colKind[c]! == 2) = true ∧ ((π.vT[c]!)[0]!).isBase = true) ∧
  let pub : Array G := XI.pubOf.map fun c => ((π.vT[c]!)[0]!).c0
  (!zh.isZero) = true ∧
  let lhs := (XI.tabs.foldl (fun (st : VF.K3 × VF.K3) t =>
    let cur := curNxt.1.extract t.col0 (t.col0 + t.nc)
    let nxt := curNxt.2.extract t.col0 (t.col0 + t.nc)
    let cvals := evalDag t.chip { cur := cur, next := nxt, pub := pub.extract t.pubBase (t.pubBase + t.npub), chal := slots,
                                  bc := t.chip.baseCols }
    let (s, pw) := cvals.foldl (fun (a : VF.K3 × VF.K3) v => (VF.K3.add a.1 (VF.K3.mul a.2 v), VF.K3.mul a.2 alpha)) (VF.K3.zero, st.2)
    let mult := ((List.range (XI.hN - t.hN)).foldl
      (fun (a : VF.K3 × VF.G) _ => (VF.K3.mul a.1 (VF.K3.sub zeta (VF.K3.ofG a.2)), VF.mul a.2 XI.hGen))
      (VF.K3.one, VF.mul XI.hShift (VF.pow XI.hGen t.hN))).1
    (VF.K3.add st.1 (VF.K3.mul s mult), pw)) (VF.K3.zero, VF.K3.one)).1
  let zN := VF.K3.pow zeta XI.hN
  let qsum := (List.range XI.nq).foldl
    (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3)) (VF.K3.pow zN (j / 3))) π.vQ[j]!)) VF.K3.zero
  (lhs == VF.K3.mul zh qsum) = true ∧
  let pts := openPts XI zeta
  let dN := 2 ^ XI.nD
  (∀ pt ∈ pts.toList, (pt.pow dN != VF.K3.ofG (VF.pow XI.dShift dN)) = true) ∧
  XI.pubCheck slots pub = true ∧
  inpCanOk XI.pubIn = true ∧
  (∀ c ∈ List.range XI.nc, (XI.colKind[c]! != 1 || (List.range XI.r).all (fun o => (π.vT[c]!)[o]! == VF.K3.hornerG XI.pre[c]! (pts[o]!))) = true) ∧
  let ops := openingList XI cs π.vT π.vQ
  let baseAt (c idx : Nat) : G :=
    let b := XI.blockOf[c]!
    let leafPos := (idx % half0) * 2 * W[b]! + (idx / half0) * W[b]! + rank[c]!
    UInt64.ofNat (π.vals[b]!)[lb sels[b]! leafPos]!
  let word0 := deepWord XI pts ops baseAt
  ∀ q ∈ π.pos.toList,
    let g0 := q % half0
    ∃ r, friSteps XI π.vals sels alphas q (List.range' 1 k)
      (foldK3 (word0 g0) (word0 (g0 + half0)) (yAt XI 0 g0) alphas[0]!) g0 = .ok r ∧
    (r.1 == VF.K3.horner π.pfinal (VF.K3.ofG (yAt XI (k + 1) r.2))) = true

theorem verifyFlatE_ok_iff (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    verifyFlatE XI H FS z π = .ok () ↔ FlatOk XI H FS z π := by
  unfold verifyFlatE FlatOk
  simp only [bind_unit_ok, forM_ok, ckE_ok]
  simp only [bind_ok, ckE_ok]
  exact Iff.rfl

theorem verifyFlat_iff (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    verifyFlat XI H FS z π = true ↔ FlatOk XI H FS z π := by
  rw [← verifyFlatE_ok_iff]
  unfold verifyFlat
  cases verifyFlatE XI H FS z π with
  | error e => simp
  | ok u => cases u; simp

/-- the Merkle step of one non-empty tree, read off `treeCheck`: the verifier's own `goRoot` consumed the whole frontier and returned
the committed root. -/
theorem treeCheck_root (XI : ExecInst) (H : HFn) (π : FlatProof) (W : Array Nat) (half0 : Nat) (sels : Array (Array Nat)) (j : Nat)
    (h : treeCheck XI H π W half0 sels j = .ok ()) (hne : ¬ (j < 4 ∧ W[j]! = 0)) :
    let sp := if j < 4 then ragSpec W[j]! half0 else friSpec (2 ^ (XI.nD - (j - 3)))
    let per := if j < 4 then 1 else 3
    let vs := π.vals[j]!
    let leaf (r : Nat) : Dg5 :=
      if j < 4 then [vs[r]!, 0, 0, 0, 0] else [vs[3 * r]!, vs[3 * r + 1]!, vs[3 * r + 2]!, 0, 0]
    vs.size = sels[j]!.size * per ∧
    goRoot H sp j sels[j]! leaf (π.sibs[j]!.toList.toArray) 1 0 sp.total 0 = some (π.roots[j]!, (π.sibs[j]!).size) := by
  unfold treeCheck at h
  have hne' : ¬ (j < 4 ∧ W[j]! = 0) := hne
  simp only [bind_unit_ok, ckE_ok] at h
  obtain ⟨h1, h2⟩ := h
  by_cases hj : j < 4 ∧ W[j]! = 0
  · exact absurd hj hne'
  · have hj' : ¬ ((decide (j < 4) && W[j]! == 0) = true) := by simpa using hj
    simp only [hj', Bool.false_eq_true, ite_false] at h2
    refine ⟨by simpa using h1, ?_⟩
    split at h2
    · simp [throw, throwThe, MonadExceptOf.throw] at h2
    · rename_i root s heq
      simp only [bind_unit_ok, ckE_ok] at h2
      obtain ⟨h3, h4⟩ := h2
      have e1 : s = π.sibs[j]!.size := by simpa using h3
      have e2 : root = π.roots[j]! := by simpa using h4
      rw [heq, e1, e2]

end NockvmE2E.Exec.V

namespace NockvmE2E.Exec.VL
open NockvmE2E.Exec

/-- **`SF.Hom` for the verifier's field, fully discharged from VLink (no arguments)**: `C := canon3`, `Cg := canon`; `φ_add`/`φ_sub` hold on
canonical operands (`toKV_add`/`toKV_sub`), everything else on arbitrary limbs. -/
noncomputable def homV : SF.Hom KC where
  φ := toKV
  ψ := psiV
  C := canon3
  Cg := canon
  C_add := canon3_add
  C_sub := canon3_sub
  C_mul := canon3_mul
  C_smul := canon3_smul
  C_inv := canon3_inv
  C_zero := canon3_zero
  C_ofG := canon3_ofG
  Cg_mul := mul_lt
  φ_add := toKV_add
  φ_sub := toKV_sub
  φ_mul := toKV_mul
  φ_smul := toKV_smul
  φ_ofG := toKV_ofG
  φ_zero := toKV_zero
  φ_one := toKV_one
  φ_inv := toKV_inv
  ψ_mul := psiV_mul
  ψ_pow := psiV_pow
  ψ_inv := psiV_inv
  ψ_two := psiV_two

end NockvmE2E.Exec.VL

#print axioms NockvmE2E.Exec.VL.homV

/-! ## L7 on the verifier's own `K3` (no `VHom`): folds with canonical bookkeeping, `Z_H`, the quotient sum -/
namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VL NockvmE2E.Exec

section Folds
variable (αV : VF.K3) (α : KC) (hα : toKV αV = α)
include hα

/-- the DEEP fold `Σ α^i cv_i` as the verifier computes it, from ANY running state `(acc, ap)` (so `ap = α^off` gives a table slice) -/
theorem foldl_deepK : ∀ (cv : List VF.K3) (acc ap : VF.K3), canon3 acc → canon3 ap → (∀ v ∈ cv, canon3 v) →
    toKV (cv.foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV)) (acc, ap)).1 =
      toKV acc + toKV ap * ∑ i : Fin cv.length, α ^ i.1 * toKV (cv.get i)
  | [], acc, ap, _, _, _ => by simp
  | v :: cv, acc, ap, hacc, hap, hcv => by
      simp only [List.foldl_cons]
      rw [foldl_deepK cv _ _ (canon3_add _ _ hacc (canon3_mul _ _)) (canon3_mul _ _)
        (fun w hw => hcv w (List.mem_cons_of_mem _ hw))]
      erw [Fin.sum_univ_succ]
      rw [toKV_add _ _ hacc (canon3_mul _ _), toKV_mul, toKV_mul, hα]
      simp only [List.get_eq_getElem, Fin.val_zero, pow_zero, one_mul, Fin.val_succ,
        List.getElem_cons_succ, List.getElem_cons_zero, pow_succ]
      have : ∑ x : Fin cv.length, α ^ x.1 * α * toKV cv[x.1] = α * ∑ x : Fin cv.length, α ^ x.1 * toKV cv[x.1] := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
      rw [this]; ring

/-- **table slice**: the fold of a table's constraint values started at `ap = α^off` is `α^off · Σ α^i cv_i` -/
theorem deepSlice (off : ℕ) (cv : List VF.K3) (acc : VF.K3) (hacc : canon3 acc) (hcv : ∀ v ∈ cv, canon3 v) :
    toKV (cv.foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV))
        (acc, VF.K3.pow αV off)).1 =
      toKV acc + α ^ off * ∑ i : Fin cv.length, α ^ i.1 * toKV (cv.get i) := by
  rw [foldl_deepK αV α hα cv acc _ hacc (canon3_pow _ _) hcv, toKV_pow, hα]

end Folds

theorem canon_qsum (zN : VF.K3) (vQ : Array VF.K3) :
    ∀ (n : ℕ) (acc : VF.K3), canon3 acc →
      canon3 ((List.range n).foldl
        (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3)) (VF.K3.pow zN (j / 3))) vQ[j]!)) acc) := by
  intro n
  induction n with
  | zero => intro acc h; simpa using h
  | succ n ih =>
    intro acc hacc
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact canon3_add _ _ (ih acc hacc) (canon3_mul _ _)


section Tables
variable (αV : VF.K3) (α : KC) (hα : toKV αV = α)
include hα
/-- **per-table term** (for the multi-table fold): a table's constraint values multiplied by `m_t = mult_t(ζ)`, folded from the running
state `(acc, α^off)`, contribute `α^off · m_t · Σ_i α^i cv_i`; tables chain by `List.foldl_append`. -/
theorem deepTable (m : VF.K3) (off : ℕ) (cv : List VF.K3) (acc : VF.K3) (hacc : canon3 acc) :
    toKV ((cv.map (VF.K3.mul m)).foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV))
        (acc, VF.K3.pow αV off)).1 =
      toKV acc + α ^ off * (toKV m * ∑ i : Fin cv.length, α ^ i.1 * toKV (cv.get i)) := by
  rw [foldl_deepK αV α hα _ acc _ hacc (canon3_pow _ _) (fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact canon3_mul _ _), toKV_pow, hα]
  congr 2
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (finCongr (List.length_map _)) _ _ fun i => ?_
  simp only [List.get_eq_getElem, List.getElem_map, toKV_mul, finCongr_apply, Fin.val_cast]
  ring
end Tables

/-- the verifier's quotient sum `Σ_j (gen^(j%3) · zN^(j/3)) · vQ_j` -/
theorem foldl_qsumK (zN : VF.K3) (vQ : Array VF.K3) :
    ∀ (n : ℕ) (acc : VF.K3), canon3 acc →
      toKV ((List.range n).foldl
        (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3)) (VF.K3.pow zN (j / 3))) vQ[j]!)) acc) =
        toKV acc + ∑ j ∈ Finset.range n, toKV VF.K3.gen ^ (j % 3) * toKV zN ^ (j / 3) * toKV vQ[j]! := by
  intro n
  induction n with
  | zero => intro acc _; simp
  | succ n ih =>
    intro acc hacc
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ]
    rw [toKV_add _ _ (canon_qsum zN vQ n acc hacc) (canon3_mul _ _), ih acc hacc, toKV_mul, toKV_mul, toKV_pow, toKV_pow]
    ring
/-- the verifier's `Z_H(ζ)` loop is `∏_{i<hN} (ζ - hShift·hGen^i)` -/
theorem zh_prod (zeta : VF.K3) (hz : canon3 zeta) (hS hG : UInt64) (hSc : canon hS) : ∀ N : ℕ,
    toKV ((List.range N).foldl
      (fun (st : VF.K3 × UInt64) _ => (VF.K3.mul st.1 (VF.K3.sub zeta (VF.K3.ofG st.2)), VF.mul st.2 hG))
      (VF.K3.one, hS)).1 = ∏ i ∈ Finset.range N, (toKV zeta - psiV hS * psiV hG ^ i) ∧
    canon ((List.range N).foldl
      (fun (st : VF.K3 × UInt64) _ => (VF.K3.mul st.1 (VF.K3.sub zeta (VF.K3.ofG st.2)), VF.mul st.2 hG))
      (VF.K3.one, hS)).2 ∧
    psiV ((List.range N).foldl
      (fun (st : VF.K3 × UInt64) _ => (VF.K3.mul st.1 (VF.K3.sub zeta (VF.K3.ofG st.2)), VF.mul st.2 hG))
      (VF.K3.one, hS)).2 = psiV hS * psiV hG ^ N := by
  intro N
  induction N with
  | zero => exact ⟨by simp [toKV_one], hSc, by simp⟩
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨?_, mul_lt _ _, ?_⟩
    · simp only []
      rw [toKV_mul, toKV_sub _ _ hz (canon3_ofG _ h2), toKV_ofG, h1, h3, Finset.prod_range_succ]
    · simp only []
      rw [psiV_mul, h3]; ring


/-! ##  pass 4: the multi-table DeepCheck fold (Horner form) -/
section Multi

/-- `Σ_i α^i l_i` in Horner form -/
noncomputable def hornerA (α : KC) (l : List KC) : KC := l.foldr (fun v acc => v + α * acc) 0

theorem hornerA_append (α : KC) (l1 l2 : List KC) :
    hornerA α (l1 ++ l2) = hornerA α l1 + α ^ l1.length * hornerA α l2 := by
  induction l1 with
  | nil => simp [hornerA]
  | cons v l ih =>
    simp only [hornerA, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem hornerA_map_mul (α c : KC) (l : List KC) : hornerA α (l.map (c * ·)) = c * hornerA α l := by
  induction l with
  | nil => simp [hornerA]
  | cons v l ih =>
    simp only [hornerA, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih]; ring

theorem sumFin_eq_hornerA (α : KC) (l : List KC) : ∑ i : Fin l.length, α ^ i.1 * l.get i = hornerA α l := by
  induction l with
  | nil => simp [hornerA]
  | cons v l ih =>
    erw [Fin.sum_univ_succ]
    simp only [hornerA, List.foldr_cons] at ih ⊢
    rw [← ih, Finset.mul_sum]
    simp only [List.get_eq_getElem, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, List.getElem_cons_succ,
      List.getElem_cons_zero, pow_succ]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring

/-- the fold of one table's constraint values from the running state `(acc, ap)`: canonical, and in `KC` a Horner step -/
theorem foldl_deepH (αV : VF.K3) : ∀ (cv : List VF.K3) (acc ap : VF.K3), canon3 acc → canon3 ap → (∀ v ∈ cv, canon3 v) →
    canon3 (cv.foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV)) (acc, ap)).1 ∧
    canon3 (cv.foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV)) (acc, ap)).2 ∧
    toKV (cv.foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV)) (acc, ap)).1 =
      toKV acc + toKV ap * hornerA (toKV αV) (cv.map toKV) ∧
    toKV (cv.foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV)) (acc, ap)).2 =
      toKV ap * toKV αV ^ cv.length
  | [], acc, ap, ha, hp, _ => ⟨ha, hp, by simp [hornerA], by simp⟩
  | v :: cv, acc, ap, ha, hp, hcv => by
      simp only [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4⟩ := foldl_deepH αV cv _ _ (canon3_add _ _ ha (canon3_mul _ _)) (canon3_mul _ _)
        (fun w hw => hcv w (List.mem_cons_of_mem _ hw))
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [h3, toKV_add _ _ ha (canon3_mul _ _), toKV_mul, toKV_mul]
        simp only [List.map_cons, hornerA, List.foldr_cons]
        ring
      · rw [h4, toKV_mul]; simp only [List.length_cons]; ring

/-- one table of the verifier's DeepCheck fold: `(acc, α^off) ↦ (acc + mult_t · Σ α^(off+i) cv_i, α^(off+len))` -/
def tabStep (αV : VF.K3) (cv : TabInst → Array VF.K3) (mult : TabInst → VF.K3) (st : VF.K3 × VF.K3) (t : TabInst) :
    VF.K3 × VF.K3 :=
  let (s, pw) := (cv t).foldl (fun (a : VF.K3 × VF.K3) v => (VF.K3.add a.1 (VF.K3.mul a.2 v), VF.K3.mul a.2 αV)) (VF.K3.zero, st.2)
  (VF.K3.add st.1 (VF.K3.mul s (mult t)), pw)

/-- the constraint terms the tables contribute, in `KC`, in table order: `mult_t · cv_{t,i}` -/
noncomputable def termsK (αV : VF.K3) (cv : TabInst → Array VF.K3) (mult : TabInst → VF.K3) (ts : List TabInst) : List KC :=
  ts.flatMap fun t => ((cv t).toList.map toKV).map (toKV (mult t) * ·)

theorem tabs_fold (αV : VF.K3) (cv : TabInst → Array VF.K3) (mult : TabInst → VF.K3) :
    ∀ (ts : List TabInst) (acc pw : VF.K3), canon3 acc → canon3 pw → (∀ t ∈ ts, ∀ v ∈ (cv t).toList, canon3 v) →
      (∀ t ∈ ts, canon3 (mult t)) →
      canon3 (ts.foldl (tabStep αV cv mult) (acc, pw)).1 ∧ canon3 (ts.foldl (tabStep αV cv mult) (acc, pw)).2 ∧
      toKV (ts.foldl (tabStep αV cv mult) (acc, pw)).1 = toKV acc + toKV pw * hornerA (toKV αV) (termsK αV cv mult ts) ∧
      toKV (ts.foldl (tabStep αV cv mult) (acc, pw)).2 = toKV pw * toKV αV ^ (termsK αV cv mult ts).length
  | [], acc, pw, ha, hp, _, _ => ⟨ha, hp, by simp [termsK, hornerA], by simp [termsK]⟩
  | t :: ts, acc, pw, ha, hp, hcv, hm => by
      have hc1 : ∀ v ∈ (cv t).toList, canon3 v := hcv t (by simp)
      obtain ⟨f1, f2, f3, f4⟩ := foldl_deepH αV (cv t).toList VF.K3.zero pw canon3_zero hp hc1
      have hstep : tabStep αV cv mult (acc, pw) t =
          (VF.K3.add acc (VF.K3.mul ((cv t).toList.foldl (fun (p : VF.K3 × VF.K3) v =>
              (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV)) (VF.K3.zero, pw)).1 (mult t)),
           ((cv t).toList.foldl (fun (p : VF.K3 × VF.K3) v =>
              (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV)) (VF.K3.zero, pw)).2) := by
        simp only [tabStep, ← Array.foldl_toList]
      simp only [List.foldl_cons, hstep]
      obtain ⟨g1, g2, g3, g4⟩ := tabs_fold αV cv mult ts _ _ (canon3_add _ _ ha (canon3_mul _ _)) f2
        (fun u hu v hv => hcv u (List.mem_cons_of_mem _ hu) v hv) (fun u hu => hm u (List.mem_cons_of_mem _ hu))
      refine ⟨g1, g2, ?_, ?_⟩
      · rw [g3, toKV_add _ _ ha (canon3_mul _ _), toKV_mul, f3, f4, toKV_zero]
        have hT : termsK αV cv mult (t :: ts) = ((cv t).toList.map toKV).map (toKV (mult t) * ·) ++ termsK αV cv mult ts := by
          simp [termsK]
        rw [hT, hornerA_append, hornerA_map_mul, List.length_map, List.length_map]
        ring
      · have hT : termsK αV cv mult (t :: ts) = ((cv t).toList.map toKV).map (toKV (mult t) * ·) ++ termsK αV cv mult ts := by
          simp [termsK]
        rw [g4, f4, hT, List.length_append, List.length_map, List.length_map, pow_add]
        ring

section MultiDC
open NockvmE2E.Deep NockvmE2E.Rap Polynomial

/-- **L7, multi-table**: the verifier's folded DEEP test (`lhs = Z_H(ζ)·qsum`, with `lhs` the table-chained fold) implies `DeepCheck`, given
that the concatenated table terms `mult_t · cv_{t,i}` are the audited `A.Cv_i` (`hdag`, with the audited `Zout J.H (J.Ht (tabS i))` inside `A.Cv`). -/
theorem deepCheck_of_flatKm {Φ : CoinFrame} {ι β : Type} [Fintype KC] [DecidableEq KC] {colRound : ι → ℕ}
    (P : DeepParams Φ KC ι β colRound) {r : ℕ} (A : AirShape P r) (χ : Coins Φ KC) (α ζ : KC)
    (vT : ι × Fin r → KC) (vQ : Fin P.nq → KC)
    (αV lhsV zhV zNV : VF.K3) (terms : List KC) (vQV : Array VF.K3)
    (hα : toKV αV = α) (hl : toKV lhsV = hornerA α terms) (hlen : terms.length = P.ns)
    (hdag : ∀ i : Fin terms.length, terms.get i = A.Cv χ ζ (Fin.cast hlen i) vT)
    (hZ : toKV zhV = eval ζ P.Zpoly) (he : P.e = 3) (hzN : toKV zNV = ζ ^ P.H.card)
    (hqlen : vQV.size = P.nq) (hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j)
    (hQ : ∀ j : Fin P.nq, toKV vQV[j.1]! = vQ j)
    (h : lhsV = VF.K3.mul zhV ((List.range P.nq).foldl
        (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3)) (VF.K3.pow zNV (j / 3))) vQV[j]!))
        VF.K3.zero)) :
    DeepCheck P A χ α ζ vT vQ := by
  have h1 := congrArg toKV h
  rw [toKV_mul, foldl_qsumK zNV vQV P.nq _ canon3_zero, toKV_zero, zero_add, hl, hZ] at h1
  have hl' : hornerA α terms = ∑ i : Fin P.ns, α ^ i.1 * A.Cv χ ζ i vT := by
    rw [← sumFin_eq_hornerA]
    refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
    rw [hdag i]; rfl
  have hr : ∑ j ∈ Finset.range P.nq, toKV VF.K3.gen ^ (j % 3) * toKV zNV ^ (j / 3) * toKV vQV[j]! =
      ∑ j : Fin P.nq, P.cw j * ζ ^ (j.1 / P.e * P.H.card) * vQ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => toKV VF.K3.gen ^ (j % 3) * toKV zNV ^ (j / 3) * toKV vQV[j]!)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcw j, hQ j, hzN, he, ← pow_mul, mul_comm P.H.card]
  rw [hl', hr] at h1
  exact h1

end MultiDC
end Multi

section DC
open NockvmE2E.Deep NockvmE2E.Rap Polynomial
variable {Φ : CoinFrame} {ι β : Type} [Fintype KC] [DecidableEq KC] {colRound : ι → ℕ}

/-- **L7 on the verifier's `K3`**: `deepCheck_of_flat` with the realization `toKV` (no `VHom`): the verifier's folded DEEP test
`Σ α^i cv_i = Z_H(ζ) · qsum` implies `DeepCheck`, given canonical constraint values and the instance hypotheses. -/
theorem deepCheck_of_flatK (P : DeepParams Φ KC ι β colRound) {r : ℕ} (A : AirShape P r) (χ : Coins Φ KC) (α ζ : KC)
    (vT : ι × Fin r → KC) (vQ : Fin P.nq → KC)
    (αV zhV zNV : VF.K3) (cv : List VF.K3) (vQV : Array VF.K3)
    (hα : toKV αV = α) (hcan : ∀ v ∈ cv, canon3 v) (hlen : cv.length = P.ns)
    (hdag : ∀ i : Fin cv.length, toKV (cv.get i) = A.Cv χ ζ (Fin.cast hlen i) vT)
    (hZ : toKV zhV = eval ζ P.Zpoly) (he : P.e = 3) (hzN : toKV zNV = ζ ^ P.H.card)
    (hqlen : vQV.size = P.nq) (hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j)
    (hQ : ∀ j : Fin P.nq, toKV vQV[j.1]! = vQ j)
    (h : (cv.foldl (fun (p : VF.K3 × VF.K3) v => (VF.K3.add p.1 (VF.K3.mul p.2 v), VF.K3.mul p.2 αV))
            (VF.K3.zero, VF.K3.one)).1 =
      VF.K3.mul zhV ((List.range P.nq).foldl
        (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3)) (VF.K3.pow zNV (j / 3))) vQV[j]!))
        VF.K3.zero)) :
    DeepCheck P A χ α ζ vT vQ := by
  have h1 := congrArg toKV h
  rw [toKV_mul, foldl_deepK αV α hα cv _ _ canon3_zero canon3_one hcan,
    foldl_qsumK zNV vQV P.nq _ canon3_zero, toKV_zero, toKV_one, zero_add, one_mul, zero_add, hZ] at h1
  have hl : ∑ i : Fin cv.length, α ^ i.1 * toKV (cv.get i) = ∑ i : Fin P.ns, α ^ i.1 * A.Cv χ ζ i vT := by
    refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
    rw [hdag i]; rfl
  have hr : ∑ j ∈ Finset.range P.nq, toKV VF.K3.gen ^ (j % 3) * toKV zNV ^ (j / 3) * toKV vQV[j]! =
      ∑ j : Fin P.nq, P.cw j * ζ ^ (j.1 / P.e * P.H.card) * vQ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => toKV VF.K3.gen ^ (j % 3) * toKV zNV ^ (j / 3) * toKV vQV[j]!)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcw j, hQ j, hzN, he, ← pow_mul, mul_comm P.H.card]
  rw [hl, hr] at h1
  exact h1
end DC
end NockvmE2E.Exec.V

/-! ## the constraint DAG evaluates to canonical limbs (given canonical inputs) -/
namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VL NockvmE2E.Exec.Tr

/-- literals of a DAG expression are canonical limbs -/
def ExCan : Ex → Prop
  | .var _ _ => True
  | .cF v => canon v
  | .add a b => ExCan a ∧ ExCan b
  | .sub a b => ExCan a ∧ ExCan b
  | .mul a b => ExCan a ∧ ExCan b
  | .neg a => ExCan a
  | .pow a _ => ExCan a
  | .extVar _ _ => True
  | .chal _ => True
  | .ref _ => True

/-- canonical environment (out-of-range reads are the default `0`, which is canonical) -/
def EnvCan (env : DEnv) (memo : Array VF.K3) : Prop :=
  (∀ i : ℕ, canon3 env.cur[i]!) ∧ (∀ i : ℕ, canon3 env.next[i]!) ∧ (∀ i : ℕ, canon env.pub[i]!) ∧
    (∀ i : ℕ, canon3 env.chal[i]!) ∧ (∀ i : ℕ, canon3 memo[i]!)

theorem canon3_extV (a : Array VF.K3) (ha : ∀ i : ℕ, canon3 a[i]!) (bc e : ℕ) : canon3 (extV a bc e) := by
  unfold extV
  exact canon3_add _ _ (canon3_add _ _ (ha _) (canon3_mul _ _)) (canon3_mul _ _)

theorem canon3_evK (env : DEnv) (memo : Array VF.K3) (h : EnvCan env memo) : ∀ ex : Ex, ExCan ex → canon3 (evK env memo ex)
  | .var k i, _ => by
    rcases k with _ | _ | k
    · exact h.1 i
    · exact h.2.1 i
    · exact canon3_ofG _ (h.2.2.1 i)
  | .cF v, hc => canon3_ofG _ hc
  | .add a b, hc => canon3_add _ _ (canon3_evK env memo h a hc.1) (canon3_evK env memo h b hc.2)
  | .sub a b, hc => canon3_sub _ _ (canon3_evK env memo h a hc.1) (canon3_evK env memo h b hc.2)
  | .mul a b, _ => canon3_mul _ _
  | .neg a, hc => canon3_neg _ (canon3_evK env memo h a hc)
  | .pow a n, _ => canon3_pow _ _
  | .extVar k e, _ => by
    rcases k with _ | _ | k
    · exact canon3_extV _ h.1 _ _
    · exact canon3_extV _ h.2.1 _ _
    · exact ⟨h.2.2.1 _, h.2.2.1 _, h.2.2.1 _⟩
  | .chal i, _ => h.2.2.2.1 i
  | .ref i, _ => h.2.2.2.2 i

theorem canon_push (a : Array VF.K3) (x : VF.K3) (ha : ∀ i : ℕ, canon3 a[i]!) (hx : canon3 x) :
    ∀ i : ℕ, canon3 (a.push x)[i]! := by
  intro i
  by_cases hi : i < a.size + 1
  · have hi' : i < (a.push x).size := by simpa using hi
    rw [getElem!_pos (a.push x) i hi', Array.getElem_push]
    by_cases h2 : i < a.size
    · simp only [h2, dite_true]; rw [← getElem!_pos a i h2]; exact ha i
    · simp only [h2, dite_false]; exact hx
  · have : ¬ i < (a.push x).size := by simpa using hi
    rw [getElem!_neg (a.push x) i this]
    exact canon3_zero

theorem canon_memo (env : DEnv) (hcur : ∀ i : ℕ, canon3 env.cur[i]!) (hnext : ∀ i : ℕ, canon3 env.next[i]!)
    (hpub : ∀ i : ℕ, canon env.pub[i]!) (hchal : ∀ i : ℕ, canon3 env.chal[i]!) :
    ∀ (l : List Ex) (memo : Array VF.K3), (∀ i : ℕ, canon3 memo[i]!) → (∀ s ∈ l, ExCan s) →
      ∀ i : ℕ, canon3 (l.foldl (fun (memo : Array VF.K3) s => memo.push (evK env memo s)) memo)[i]! := by
  intro l
  induction l with
  | nil => intro memo hm _; simpa using hm
  | cons s l ih =>
    intro memo hm hl
    simp only [List.foldl_cons]
    exact ih _ (canon_push _ _ hm (canon3_evK env memo ⟨hcur, hnext, hpub, hchal, hm⟩ s (hl s (by simp)))) 
      (fun t ht => hl t (List.mem_cons_of_mem _ ht))

/-- **every constraint value of the chip DAG is a canonical `K3`** when the environment and the DAG literals are -/
theorem canon_evalDag (ch : Chip) (env : DEnv) (hcur : ∀ i : ℕ, canon3 env.cur[i]!) (hnext : ∀ i : ℕ, canon3 env.next[i]!)
    (hpub : ∀ i : ℕ, canon env.pub[i]!) (hchal : ∀ i : ℕ, canon3 env.chal[i]!)
    (hsh : ∀ s ∈ ch.shared.toList, ExCan s) (hcs : ∀ c ∈ ch.cons.toList, ExCan c.e) :
    ∀ v ∈ (evalDag ch env).toList, canon3 v := by
  intro v hv
  unfold evalDag at hv
  simp only [] at hv
  rw [Array.toList_map, List.mem_map] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  have hm := canon_memo env hcur hnext hpub hchal ch.shared.toList (Array.mkEmpty ch.shared.size)
    (fun i => by simp [getElem!_neg]; exact canon3_zero) hsh
  exact canon3_evK env _ ⟨hcur, hnext, hpub, hchal, hm⟩ c.e (hcs c hc)

/-! ## reading `FlatOk` off as named facts -/
section Facts
variable (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof)

def msgsOf : Array (List Nat) :=
  #[[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg π.vT π.vQ, [], []] ++ π.roots.extract 4 (4 + XI.k) ++
    #[π.pfinal.toList.flatMap VF.K3.limbs]
/-- the challenges the verifier re-derives from the key (message `i` ↦ the limbs squeezed after it) -/
def chalsOf : Array (List Nat) :=
  (Array.range (msgsOf XI π).size).map fun i =>
    if roundNl XI i == 0 then [] else FS (z :: ((msgsOf XI π).extract 0 (i + 1)).toList) (roundNl XI i)
def zetaOf : VF.K3 := VF.K3.ofLimbs (chalsOf XI FS z π)[4]!
def alphaOf : VF.K3 := VF.K3.ofLimbs (chalsOf XI FS z π)[3]!
def selsOf : Array (Array Nat) :=
  (Array.range (4 + XI.k)).map fun j => treeSel XI ((blockLayout XI).1.getD j 0) j π.pos
def zhOf : VF.K3 :=
  ((List.range XI.hN).foldl
    (fun (st : VF.K3 × VF.G) _ => (VF.K3.mul st.1 (VF.K3.sub (zetaOf XI FS z π) (VF.K3.ofG st.2)), VF.mul st.2 XI.hGen))
    (VF.K3.one, XI.hShift)).1
def slotsOf : Array VF.K3 :=
  XI.derived.toList.foldl (fun (slots : Array VF.K3) (be : Nat × Nat) => slots.push (VF.K3.pow slots[be.1]! be.2))
    (k3s (chalsOf XI FS z π)[1]! XI.nCoins[0]! ++ k3s (chalsOf XI FS z π)[2]! XI.nCoins[1]!)
def curNxtOf : Array VF.K3 × Array VF.K3 :=
  (List.range XI.nc).foldl
    (fun (st : Array VF.K3 × Array VF.K3) c =>
      match XI.colKind[c]! with
      | 0 => (st.1.set! c (π.vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (π.vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (VF.K3.hornerG XI.pre[c]! (zetaOf XI FS z π)),
              st.2.set! c (VF.K3.hornerG XI.pre[c]! (VF.K3.smul XI.hGen (zetaOf XI FS z π))))
      | _ => st)
    (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)
def pubOfProof : Array VF.G := XI.pubOf.map fun c => ((π.vT[c]!)[0]!).c0
/-- table `t`'s constraint values as the verifier computes them (its slice of the columns and publics, all coin slots) -/
def tabCv (t : TabInst) : Array VF.K3 :=
  evalDag t.chip { cur := (curNxtOf XI FS z π).1.extract t.col0 (t.col0 + t.nc),
                   next := (curNxtOf XI FS z π).2.extract t.col0 (t.col0 + t.nc),
                   pub := (pubOfProof XI π).extract t.pubBase (t.pubBase + t.npub), chal := slotsOf XI FS z π,
                   bc := t.chip.baseCols }
/-- `mult_t(ζ) = ∏_{i ∈ [hN_t, hN)} (ζ − hShift·hGen^i)` as the verifier computes it -/
def multOf (zeta : VF.K3) (t : TabInst) : VF.K3 :=
  ((List.range (XI.hN - t.hN)).foldl
    (fun (a : VF.K3 × VF.G) _ => (VF.K3.mul a.1 (VF.K3.sub zeta (VF.K3.ofG a.2)), VF.mul a.2 XI.hGen))
    (VF.K3.one, VF.mul XI.hShift (VF.pow XI.hGen t.hN))).1
/-- the verifier's `lhs` of the DeepCheck test -/
def lhsOf : VF.K3 :=
  (XI.tabs.foldl (tabStep (alphaOf XI FS z π) (tabCv XI FS z π) (multOf XI (zetaOf XI FS z π))) (VF.K3.zero, VF.K3.one)).1
def qsumOf : VF.K3 :=
  (List.range XI.nq).foldl
    (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3))
      (VF.K3.pow (VF.K3.pow (zetaOf XI FS z π) XI.hN) (j / 3))) π.vQ[j]!)) VF.K3.zero

set_option maxHeartbeats 2000000 in
/-- the DEEP test of the verifier, as equality of `K3`s -/
theorem flatOk_deep (hok : FlatOk XI H FS z π) :
    lhsOf XI FS z π = VF.K3.mul (zhOf XI FS z π) (qsumOf XI FS z π) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd, _⟩ := hok
  exact (VL.K3_beq_iff _ _).mp hd

/-- the verifier's check "ζ ∉ H": `Z_H(ζ) ≠ 0` as `K3` -/
theorem flatOk_zh (hok : FlatOk XI H FS z π) : (zhOf XI FS z π).isZero = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hz, _⟩ := hok
  have hz' : (!(zhOf XI FS z π).isZero) = true := hz
  simpa using hz'

/-- the Merkle part: every tree's `treeCheck` passed -/
theorem flatOk_trees (hok : FlatOk XI H FS z π) :
    ∀ j ∈ List.range (4 + XI.k), treeCheck XI H π (blockLayout XI).1 (2 ^ (XI.nD - 1)) (selsOf XI π) j = .ok () := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩ := hok
  exact ht

/-- the positions are the decoded FS query challenge -/
theorem flatOk_pos (hok : FlatOk XI H FS z π) :
    π.pos = ((chalsOf XI FS z π)[8 + XI.k]!).toArray.map (· % 2 ^ XI.nD) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hp, _⟩ := hok
  exact beq_iff_eq.mp hp

/-- off-domain test of every opening point -/
theorem flatOk_offdom (hok : FlatOk XI H FS z π) :
    ∀ pt ∈ (openPts XI (zetaOf XI FS z π)).toList, (pt.pow (2 ^ XI.nD) != VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD))) = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ho, _⟩ := hok
  exact ho

/-- the verifier's public relation passed (on the coin slots and the concatenated publics) -/
theorem flatOk_pub (hok : FlatOk XI H FS z π) : XI.pubCheck (slotsOf XI FS z π) (pubOfProof XI π) = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ := hok
  exact hp

/-- `Z_H(ζ)` of the verifier is `∏_{i<hN} (ζ - hShift·hGen^i)` -/
theorem toKV_zh (hz : canon3 (zetaOf XI FS z π)) (hS : VL.canon XI.hShift) :
    toKV (zhOf XI FS z π) = ∏ i ∈ Finset.range XI.hN, (toKV (zetaOf XI FS z π) - psiV XI.hShift * psiV XI.hGen ^ i) :=
  (zh_prod (zetaOf XI FS z π) hz XI.hShift XI.hGen hS XI.hN).1


end Facts

/-- **Merkle soundness of one flat tree** (L3 + L4 for the verifier's own `goRoot`): if `FlatOk` and the selection of tree `j` is strictly
increasing (it is, by construction of `treeSel`; stated as a hypothesis), the embedded VCVio opening reconstructs the committed root
`π.roots[j]` with node digest `H ([tagNode, j, heapNumber] ++ l ++ r)`. -/
theorem flatOk_merkle (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) (j : ℕ)
    (hj : j < 4 + XI.k) (hne : ¬ (j < 4 ∧ (blockLayout XI).1[j]! = 0))
    (hs : ((selsOf XI π)[j]!).toList.Pairwise (· < ·)) :
    let W := (blockLayout XI).1
    let sel := (selsOf XI π)[j]!
    let sp := if j < 4 then ragSpec W[j]! (2 ^ (XI.nD - 1)) else friSpec (2 ^ (XI.nD - (j - 3)))
    let vs := π.vals[j]!
    let leaf (r : Nat) : Dg5 :=
      if j < 4 then [vs[r]!, 0, 0, 0, 0] else [vs[3 * r]!, vs[3 * r + 1]!, vs[3 * r + 2]!, 0, 0]
    AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
      (fun a l r' => (fun i l r => H ([tagNode, j, i] ++ l ++ r)) (SM.heapIdx a 1) l r')
      (SM.mkOpening (fun i => sel[lb sel i]? == some i)
        (fun i => leaf (lb sel i)) (SM.skelOf sp sp.total sp.total) (π.sibs[j]!).toList).values
      (SM.mkOpening (fun i => sel[lb sel i]? == some i)
        (fun i => leaf (lb sel i)) (SM.skelOf sp sp.total sp.total) (π.sibs[j]!).toList).proof
      = π.roots[j]! := by
  intro W sel sp vs leaf
  have hc := flatOk_trees XI H FS z π hok j (List.mem_range.mpr hj)
  obtain ⟨_, hgo⟩ := treeCheck_root XI H π W (2 ^ (XI.nD - 1)) (selsOf XI π) j hc hne
  have hW : 1 ≤ (blockLayout XI).1[j]! ∨ ¬ j < 4 := by
    by_cases h4 : j < 4
    · left; by_contra h1; exact hne ⟨h4, by omega⟩
    · right; exact h4
  have hsp : SM.WfSpec sp ∧ 1 ≤ sp.total := by
    by_cases h4 : j < 4
    · have h1 : 1 ≤ (blockLayout XI).1[j]! := hW.resolve_right (by simpa using h4)
      simp only [sp, h4, ite_true]
      refine ⟨SM.wf_ragSpec _ _ h1, ?_⟩
      simp only [ragSpec]
      have : 0 < 2 ^ (XI.nD - 1) := Nat.two_pow_pos _
      exact Nat.mul_pos (Nat.mul_pos this (by omega)) h1
    · simp only [sp, h4, ite_false]
      exact ⟨SM.wf_friSpec _, by simp only [friSpec]; exact Nat.two_pow_pos _⟩
  exact SM.merkle_of_goRoot H sp hsp.1 j _ hs leaf _ _ hsp.2 hgo

end NockvmE2E.Exec.V


/-! ##  pass 3: `friSteps = walkKGo`, strictly increasing selections, canonicity of the verifier's values (`AllCanon`) -/
namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.VL NockvmE2E.Exec.Tr

section Sels

theorem insertD_pw (x : Nat) : ∀ l : List Nat, l.Pairwise (· < ·) →
    (insertD x l).Pairwise (· < ·) ∧ ∀ y, y ∈ insertD x l ↔ y = x ∨ y ∈ l := by
  intro l
  induction l with
  | nil => intro _; simp [insertD]
  | cons y ys ih =>
    intro h
    rw [List.pairwise_cons] at h
    obtain ⟨hy, hys⟩ := h
    unfold insertD
    by_cases h1 : x < y
    · simp only [h1, if_true]
      refine ⟨List.Pairwise.cons ?_ (List.Pairwise.cons hy hys), ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact h1
        · exact lt_trans h1 (hy b hb)
      · intro z; simp
    · by_cases h2 : x == y
      · have : x = y := by simpa using h2
        subst this
        simp only [h1, h2, if_false, if_true]
        refine ⟨List.Pairwise.cons hy hys, ?_⟩
        intro z; simp
      · simp only [h1, h2, if_false, Bool.false_eq_true]
        obtain ⟨ih1, ih2⟩ := ih hys
        have hxy : y < x := by
          have : x ≠ y := by simpa using h2
          omega
        refine ⟨List.Pairwise.cons ?_ ih1, ?_⟩
        · intro b hb
          rcases (ih2 b).mp hb with rfl | hb
          · exact hxy
          · exact hy b hb
        · intro z
          simp only [List.mem_cons, ih2]
          tauto

theorem sortedDistinct_pw (a : Array Nat) : (sortedDistinct a).toList.Pairwise (· < ·) := by
  unfold sortedDistinct
  simp only [List.toList_toArray]
  have : ∀ (l acc : List Nat), acc.Pairwise (· < ·) →
      (l.foldl (fun acc x => insertD x acc) acc).Pairwise (· < ·) := by
    intro l
    induction l with
    | nil => intro acc h; simpa using h
    | cons x l ih => intro acc h; exact ih _ (insertD_pw x acc h).1
  exact this _ _ List.Pairwise.nil

theorem blocks_pw (l : List Nat) (hl : l.Pairwise (· < ·)) (F : Nat → List Nat)
    (hF : ∀ g, (F g).Pairwise (· < ·)) (hlt : ∀ g g', g < g' → ∀ x ∈ F g, ∀ y ∈ F g', x < y) :
    (l.flatMap F).Pairwise (· < ·) := by
  rw [List.pairwise_flatMap]
  exact ⟨fun g _ => hF g, hl.imp_of_mem (fun {a b} ha hb h => hlt a b h)⟩

theorem treeSel_pw (XI : ExecInst) (Wb j : Nat) (pos : Array Nat) : (treeSel XI Wb j pos).toList.Pairwise (· < ·) := by
  unfold treeSel
  split
  · split
    · simp
    · simp only [Array.toList_flatMap, Array.toList_map, Array.toList_range]
      apply blocks_pw _ (sortedDistinct_pw _)
      · intro g
        exact List.pairwise_map.mpr ((List.pairwise_lt_range (n := 2 * Wb)).imp (fun {a b} h => by omega))
      · intro g g' h x hx y hy
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        rw [List.mem_range] at ha hb
        have := Nat.mul_le_mul_right (2 * Wb) (show g + 1 ≤ g' from h)
        nlinarith
  · simp only [Array.toList_flatMap]
    apply blocks_pw _ (sortedDistinct_pw _)
    · intro g; simp
    · intro g g' h x hx y hy; simp at hx hy; omega
end Sels


theorem horner_eq_hornerK (coef : Array VF.K3) (z : VF.K3) : VF.K3.horner coef z = SF.hornerK coef z := by
  unfold VF.K3.horner SF.hornerK
  have h1 : coef.toList.reverse = (List.range' 0 coef.size).map (fun i => coef[coef.size - 1 - i]!) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_reverse, Array.length_toList] at h1
      rw [List.getElem_reverse, List.getElem_map, List.getElem_range']
      simp only [Array.getElem_toList, Nat.zero_add, Nat.mul_one]
      rw [getElem!_pos coef _ (by omega)]
      simp
  rw [← List.foldl_map (g := fun (acc : VF.K3) (c : VF.K3) => VF.K3.add (VF.K3.mul acc z) c)
    (f := fun i => coef[coef.size - 1 - i]!), ← h1, List.foldl_reverse]

def friAtV (vals : Array (Array Nat)) (j r : Nat) : VF.K3 :=
  VF.K3.ofLimbs [(vals[j]!)[3 * r]!, (vals[j]!)[3 * r + 1]!, (vals[j]!)[3 * r + 2]!]
def faV (vals : Array (Array Nat)) (sels : Array (Array Nat)) (w g : Nat) : VF.K3 := friAtV vals (3 + w) (lb (sels[3 + w]!) (2 * g))
def fbV (vals : Array (Array Nat)) (sels : Array (Array Nat)) (w g : Nat) : VF.K3 := friAtV vals (3 + w) (lb (sels[3 + w]!) (2 * g + 1))

theorem step_aux {α : Type} (b : Bool) (m : String) (f : Except String α) (R : α → Prop) :
    (∃ res, (ckE b m >>= fun _ => f) = .ok res ∧ R res) ↔ b = true ∧ ∃ res, f = .ok res ∧ R res := by
  cases b <;> simp [ckE, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem friSteps_iff (XI : ExecInst) (vals sels : Array (Array Nat)) (alphas pfinal : Array VF.K3) (q : Nat) :
    ∀ r w prev pI, (∃ res, friSteps XI vals sels alphas q (List.range' w r) prev pI = .ok res ∧
        (res.1 == VF.K3.horner pfinal (VF.K3.ofG (yAt XI (XI.k + 1) res.2))) = true) ↔
      SF.walkKGo XI (faV vals sels) (fbV vals sels) alphas pfinal q r prev pI w = true := by
  intro r
  induction r with
  | zero =>
    intro w prev pI
    simp only [List.range'_zero, friSteps, SF.walkKGo, horner_eq_hornerK]
    simp [pure, Except.pure]
  | succ r ih =>
    intro w prev pI
    rw [List.range'_succ]
    simp only [friSteps, SF.walkKGo, Bool.and_eq_true, faV, fbV, friAtV]
    rw [step_aux]
    exact and_congr Iff.rfl (ih _ _ _)


theorem canon_of_lt (a : UInt64) (h : a.toNat < NockvmE2E.Exec.p) : canon a := h

theorem k3Ok_canon3 (x : VF.K3) (h : k3Ok x = true) : canon3 x := by
  unfold k3Ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hp : VF.P.toNat = NockvmE2E.Exec.p := by rw [P_toNat]; decide
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> unfold canon <;> rw [← hp] <;> first | exact (UInt64.lt_iff_toNat_lt.mp h0) | exact (UInt64.lt_iff_toNat_lt.mp h1) | exact (UInt64.lt_iff_toNat_lt.mp h2)

theorem canon_ofNat (x : Nat) (h : x < NockvmE2E.Exec.p) : canon (UInt64.ofNat x) := by
  unfold canon
  have : x < 2 ^ 64 := lt_trans h (by unfold NockvmE2E.Exec.p; decide)
  rw [UInt64.toNat_ofNat_of_lt' this]; exact h

theorem canon3_ofLimbs (l : List Nat) (h : ∀ x ∈ l, x < NockvmE2E.Exec.p) : canon3 (VF.K3.ofLimbs l) := by
  have hg : ∀ i, l.getD i 0 < NockvmE2E.Exec.p := by
    intro i
    by_cases hi : i < l.length
    · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; unfold NockvmE2E.Exec.p; decide
  exact ⟨canon_ofNat _ (hg 0), canon_ofNat _ (hg 1), canon_ofNat _ (hg 2)⟩

theorem canon_getBang (a : Array VF.K3) (h : ∀ x ∈ a, canon3 x) (i : ℕ) : canon3 a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]; exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]; exact canon3_zero

theorem canon_getBangG (a : Array UInt64) (h : ∀ x ∈ a, canon x) (i : ℕ) : canon a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]; exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]; exact Gold.zero_lt

theorem canon_set (a : Array VF.K3) (ha : ∀ i : ℕ, canon3 a[i]!) (c : ℕ) (x : VF.K3) (hx : canon3 x) :
    ∀ i : ℕ, canon3 (a.set! c x)[i]! := by
  intro i
  by_cases hi : i < a.size
  · have hi' : i < (a.set! c x).size := by simpa using hi
    rw [getElem!_pos _ i hi']
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds]
    · by_cases hc : c = i
      · simp [hc, hx]
      · simp [hc]; rw [← getElem!_pos a i hi]; exact ha i
    · exact hi
  · have : ¬ i < (a.set! c x).size := by simpa using hi
    rw [getElem!_neg _ i this]; exact canon3_zero

theorem arr_all_iff {α : Type} (a : Array α) (f : α → Bool) : a.all f = true ↔ ∀ x ∈ a, f x = true := by
  rw [Array.all_eq_true']

theorem exCan_of_exCanon : ∀ e : Tr.Ex, exCanon e = true → ExCan e
  | .var _ _, _ => trivial
  | .cF v, h => by
      have hpp : NockvmE2E.Exec.p = VF.PN := by unfold NockvmE2E.Exec.p VF.PN; decide
      simp only [exCanon, based, decide_eq_true_eq] at h
      show v.toNat < NockvmE2E.Exec.p
      rw [hpp]; exact h
  | .add a b, h => by
      simp only [exCanon, Bool.and_eq_true] at h
      exact ⟨exCan_of_exCanon a h.1, exCan_of_exCanon b h.2⟩
  | .sub a b, h => by
      simp only [exCanon, Bool.and_eq_true] at h
      exact ⟨exCan_of_exCanon a h.1, exCan_of_exCanon b h.2⟩
  | .mul a b, h => by
      simp only [exCanon, Bool.and_eq_true] at h
      exact ⟨exCan_of_exCanon a h.1, exCan_of_exCanon b h.2⟩
  | .neg a, h => exCan_of_exCanon a (by simpa [exCanon] using h)
  | .pow a _, h => exCan_of_exCanon a (by simpa [exCanon] using h)
  | .extVar _ _, _ => trivial
  | .chal _, _ => trivial
  | .ref _, _ => trivial

/-- **the instance and proof limbs, read off the verifier's first check** (`allCanon`): every canonicity fact the soundness chain uses -/
theorem allCanon_parts (XI : ExecInst) (z : List Nat) (π : FlatProof) (h : allCanon XI z π = true) :
    canon XI.hShift ∧ canon3 XI.ppt ∧ (∀ c : ℕ, ∀ g ∈ XI.pre[c]!, canon g) ∧
    (∀ t ∈ XI.tabs.toList, (∀ s ∈ t.chip.shared.toList, ExCan s) ∧ (∀ c ∈ t.chip.cons.toList, ExCan c.e)) ∧
    (∀ a ∈ π.vT, ∀ x ∈ a, canon3 x) ∧ (∀ x ∈ π.vQ, canon3 x) ∧ (∀ x ∈ π.pfinal, canon3 x) ∧
    (∀ a ∈ π.vals, ∀ x ∈ a, x < NockvmE2E.Exec.p) := by
  unfold allCanon at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hS⟩, hP⟩, hpre⟩, htabs⟩, hz⟩, hroots⟩, hvT⟩, hvQ⟩, hpf⟩, hvals⟩, hsibs⟩ := h
  have hpp : NockvmE2E.Exec.p = VF.PN := by unfold NockvmE2E.Exec.p VF.PN; decide
  have hS' := hS
  refine ⟨?_, k3Ok_canon3 _ hP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold based at hS'
    show XI.hShift.toNat < NockvmE2E.Exec.p
    rw [hpp]; simpa using hS'
  · intro c g hg
    have hc : ∀ x ∈ XI.pre[c]!, based x.toNat = true := by
      by_cases hcc : c < XI.pre.size
      · rw [getElem!_pos XI.pre c hcc] at hg ⊢
        intro x hx
        exact (arr_all_iff _ _).mp ((arr_all_iff _ _).mp hpre _ (Array.getElem_mem hcc)) x hx
      · rw [getElem!_neg XI.pre c hcc] at hg; exact absurd hg (Array.not_mem_empty g)
    have := hc g hg
    unfold based at this
    show g.toNat < NockvmE2E.Exec.p
    rw [hpp]; simpa using this
  · intro t ht
    have h1 := (arr_all_iff _ _).mp htabs t (Array.mem_def.mpr ht)
    unfold chipCanon at h1
    simp only [Bool.and_eq_true] at h1
    refine ⟨fun s hs => exCan_of_exCanon _ ((arr_all_iff _ _).mp h1.1 s (Array.mem_def.mpr hs)),
      fun c hc => exCan_of_exCanon _ ((arr_all_iff _ _).mp h1.2 c (Array.mem_def.mpr hc))⟩
  · intro a ha x hx
    have h1 := (arr_all_iff _ _).mp hvT a ha
    exact k3Ok_canon3 x ((arr_all_iff _ _).mp h1 x hx)
  · intro x hx; exact k3Ok_canon3 x ((arr_all_iff _ _).mp hvQ x hx)
  · intro x hx; exact k3Ok_canon3 x ((arr_all_iff _ _).mp hpf x hx)
  · intro a ha x hx
    have h1 := (arr_all_iff _ _).mp hvals a ha
    have h2 := (arr_all_iff _ _).mp h1 x hx
    unfold based at h2
    rw [hpp]; simpa using h2

theorem flatOk_allCanon (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    allCanon XI z π = true := hok.1

theorem flatOk_limbs (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    (∀ a ∈ π.vT, ∀ x ∈ a, canon3 x) ∧ (∀ x ∈ π.vQ, canon3 x) ∧ (∀ x ∈ π.pfinal, canon3 x) ∧
    (∀ a ∈ π.vals, ∀ x ∈ a, x < NockvmE2E.Exec.p) := by
  obtain ⟨_, _, _, _, h1, h2, h3, h4⟩ := allCanon_parts XI z π hok.1
  exact ⟨h1, h2, h3, h4⟩

/-- canonical-limb facts on the INSTANCE data; read off `allCanon` (`instCan_of_flatOk`) -/
structure InstCan (XI : ExecInst) : Prop where
  hShift : canon XI.hShift
  ppt : canon3 XI.ppt
  pre : ∀ c : ℕ, ∀ g ∈ XI.pre[c]!, canon g
  shared : ∀ t ∈ XI.tabs.toList, ∀ s ∈ t.chip.shared.toList, ExCan s
  cons : ∀ t ∈ XI.tabs.toList, ∀ c ∈ t.chip.cons.toList, ExCan c.e

/-- every limb of a Fiat-Shamir challenge is `< p` (read off the verifier's FS-limb check: `chalCan_of_flatOk`) -/
def ChalCan (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) : Prop :=
  ∀ i : ℕ, ∀ x ∈ (chalsOf XI FS z π)[i]!, x < NockvmE2E.Exec.p

/-- **`AllCanon`**: instance data and challenge limbs; BOTH are now consequences of `FlatOk` (`allCanon_of_flatOk`) -/
structure AllCanon (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) : Prop where
  inst : InstCan XI
  chal : ChalCan XI FS z π

theorem instCan_of_flatOk (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    InstCan XI := by
  obtain ⟨h1, h2, h3, h4, _⟩ := allCanon_parts XI z π hok.1
  exact ⟨h1, h2, h3, fun t ht => (h4 t ht).1, fun t ht => (h4 t ht).2⟩

theorem chalCan_of_flatOk (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    ChalCan XI FS z π := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := hok
  have hc' : ((chalsOf XI FS z π).all (·.all based)) = true := hc
  have hpp : NockvmE2E.Exec.p = VF.PN := by unfold NockvmE2E.Exec.p VF.PN; decide
  intro i x hx
  by_cases hi : i < (chalsOf XI FS z π).size
  · rw [getElem!_pos _ i hi] at hx
    have := (List.all_eq_true.mp ((arr_all_iff _ _).mp hc' _ (Array.getElem_mem hi))) x hx
    unfold based at this
    rw [hpp]; simpa using this
  · rw [getElem!_neg _ i hi] at hx
    exact absurd hx List.not_mem_nil

theorem allCanon_of_flatOk (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    AllCanon XI FS z π := ⟨instCan_of_flatOk XI H FS z π hok, chalCan_of_flatOk XI H FS z π hok⟩

theorem canon3_zetaOf (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) (h : ChalCan XI FS z π) :
    canon3 (zetaOf XI FS z π) := canon3_ofLimbs _ (h 4)
theorem canon3_alphaOf (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) (h : ChalCan XI FS z π) :
    canon3 (alphaOf XI FS z π) := canon3_ofLimbs _ (h 3)

theorem canon_k3s (l : List Nat) (hl : ∀ x ∈ l, x < NockvmE2E.Exec.p) (n : ℕ) : ∀ x ∈ k3s l n, canon3 x := by
  intro x hx
  unfold k3s at hx
  obtain ⟨i, _, rfl⟩ := Array.mem_map.mp hx
  exact canon3_ofLimbs _ (fun y hy => hl y (List.mem_of_mem_drop hy))

theorem canon_hornerG (z : VF.K3) : ∀ l : List UInt64, (∀ x ∈ l, canon x) →
    canon3 (l.foldr (fun c acc => VF.K3.add (VF.K3.mul acc z) (VF.K3.ofG c)) VF.K3.zero)
  | [], _ => canon3_zero
  | c :: l, h => canon3_add _ _ (canon3_mul _ _) (canon3_ofG _ (h c (by simp)))

theorem canon_slots (XI : ExecInst) (init : Array VF.K3) (hi : ∀ x ∈ init, canon3 x) :
    ∀ x ∈ XI.derived.toList.foldl (fun (slots : Array VF.K3) (be : Nat × Nat) => slots.push (VF.K3.pow slots[be.1]! be.2)) init,
      canon3 x := by
  have : ∀ (l : List (Nat × Nat)) (a : Array VF.K3), (∀ x ∈ a, canon3 x) →
      ∀ x ∈ l.foldl (fun (slots : Array VF.K3) (be : Nat × Nat) => slots.push (VF.K3.pow slots[be.1]! be.2)) a, canon3 x := by
    intro l
    induction l with
    | nil => intro a h; simpa using h
    | cons be l ih =>
      intro a h
      apply ih
      intro x hx
      rcases Array.mem_push.mp hx with hx | rfl
      · exact h x hx
      · exact canon3_pow _ _
  exact this _ _ hi

theorem canon_curNxt (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) (hvT : ∀ a ∈ π.vT, ∀ x ∈ a, canon3 x)
    (hc : InstCan XI) (hz : canon3 (zetaOf XI FS z π)) :
    (∀ i : ℕ, canon3 (curNxtOf XI FS z π).1[i]!) ∧ (∀ i : ℕ, canon3 (curNxtOf XI FS z π).2[i]!) := by
  have hvTc : ∀ c : ℕ, ∀ j : ℕ, canon3 (π.vT[c]!)[j]! := by
    intro c j
    apply canon_getBang
    by_cases hcc : c < π.vT.size
    · rw [getElem!_pos π.vT c hcc]; exact hvT _ (Array.getElem_mem hcc)
    · rw [getElem!_neg π.vT c hcc]; intro x hx; exact absurd hx (Array.not_mem_empty x)
  have hrep : ∀ i : ℕ, canon3 (Array.replicate (XI.nc + XI.nq) VF.K3.zero)[i]! := by
    intro i; apply canon_getBang; intro x hx; rw [Array.mem_replicate] at hx; rw [hx.2]; exact canon3_zero
  have hHor : ∀ c : ℕ, ∀ w : VF.K3, canon3 (VF.K3.hornerG XI.pre[c]! w) := by
    intro c w
    unfold VF.K3.hornerG
    exact canon_hornerG w _ (fun x hx => hc.pre c x (by simpa using hx))
  unfold curNxtOf
  have : ∀ (l : List ℕ) (st : Array VF.K3 × Array VF.K3), (∀ i : ℕ, canon3 st.1[i]!) → (∀ i : ℕ, canon3 st.2[i]!) →
      (∀ i : ℕ, canon3 (l.foldl (fun (st : Array VF.K3 × Array VF.K3) c =>
      match XI.colKind[c]! with
      | 0 => (st.1.set! c (π.vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (π.vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (VF.K3.hornerG XI.pre[c]! (zetaOf XI FS z π)),
              st.2.set! c (VF.K3.hornerG XI.pre[c]! (VF.K3.smul XI.hGen (zetaOf XI FS z π))))
      | _ => st) st).1[i]!) ∧
      (∀ i : ℕ, canon3 (l.foldl (fun (st : Array VF.K3 × Array VF.K3) c =>
      match XI.colKind[c]! with
      | 0 => (st.1.set! c (π.vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (π.vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (VF.K3.hornerG XI.pre[c]! (zetaOf XI FS z π)),
              st.2.set! c (VF.K3.hornerG XI.pre[c]! (VF.K3.smul XI.hGen (zetaOf XI FS z π))))
      | _ => st) st).2[i]!) := by
    intro l
    induction l with
    | nil => intro st h1 h2; exact ⟨h1, h2⟩
    | cons c l ih =>
      intro st h1 h2
      simp only [List.foldl_cons]
      apply ih
      · rcases h : XI.colKind[c]! with _ | _ | k <;> simp only [h]
        · exact canon_set _ h1 _ _ (hvTc _ _)
        · exact canon_set _ h1 _ _ (hHor _ _)
        · exact h1
      · rcases h : XI.colKind[c]! with _ | _ | k <;> simp only [h]
        · exact canon_set _ h2 _ _ (by split <;> first | exact hvTc _ _ | exact canon3_zero)
        · exact canon_set _ h2 _ _ (hHor _ _)
        · exact h2
  exact this _ _ hrep hrep

theorem canon_vT_get (π : FlatProof) (hvT : ∀ a ∈ π.vT, ∀ x ∈ a, canon3 x) (c j : ℕ) : canon3 (π.vT[c]!)[j]! := by
  apply canon_getBang
  by_cases hcc : c < π.vT.size
  · rw [getElem!_pos π.vT c hcc]; exact hvT _ (Array.getElem_mem hcc)
  · rw [getElem!_neg π.vT c hcc]; intro x hx; exact absurd hx (Array.not_mem_empty x)

theorem canon_extract (a : Array VF.K3) (ha : ∀ i : ℕ, canon3 a[i]!) (s e : ℕ) : ∀ i : ℕ, canon3 (a.extract s e)[i]! := by
  intro i
  by_cases hi : i < (a.extract s e).size
  · rw [getElem!_pos _ i hi, Array.getElem_extract]
    have h2 : s + i < a.size := by
      have := hi; simp only [Array.size_extract] at this; omega
    rw [← getElem!_pos a (s + i) h2]; exact ha _
  · rw [getElem!_neg _ i hi]; exact canon3_zero

theorem canon_extractG (a : Array VF.G) (ha : ∀ i : ℕ, canon a[i]!) (s e : ℕ) : ∀ i : ℕ, canon (a.extract s e)[i]! := by
  intro i
  by_cases hi : i < (a.extract s e).size
  · rw [getElem!_pos _ i hi, Array.getElem_extract]
    have h2 : s + i < a.size := by
      have := hi; simp only [Array.size_extract] at this; omega
    rw [← getElem!_pos a (s + i) h2]; exact ha _
  · rw [getElem!_neg _ i hi]; exact Gold.zero_lt

/-- **`hcan` discharged, per table**: every constraint value of table `t` is canonical, from `FlatOk` alone (proof limbs, `allCanon`, FS-limb check) -/
theorem tabCv_canon (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π)
    (t : TabInst) (ht : t ∈ XI.tabs.toList) : ∀ v ∈ (tabCv XI FS z π t).toList, canon3 v := by
  have hc := allCanon_of_flatOk XI H FS z π hok
  obtain ⟨hvT, hvQ, hpf, hvals⟩ := flatOk_limbs XI H FS z π hok
  have hz := canon3_zetaOf XI FS z π hc.chal
  obtain ⟨hcur, hnext⟩ := canon_curNxt XI FS z π hvT hc.inst hz
  unfold tabCv
  refine canon_evalDag _ _ (canon_extract _ hcur _ _) (canon_extract _ hnext _ _) ?_ ?_
    (hc.inst.shared t ht) (hc.inst.cons t ht)
  · refine canon_extractG _ (fun i => ?_) _ _
    apply canon_getBangG
    intro x hx
    unfold pubOfProof at hx
    obtain ⟨c, _, rfl⟩ := Array.mem_map.mp hx
    exact (canon_vT_get π hvT c 0).1
  · intro i
    apply canon_getBang
    unfold slotsOf
    apply canon_slots
    intro x hx
    rcases Array.mem_append.mp hx with hx | hx
    · exact canon_k3s _ (hc.chal 1) _ x hx
    · exact canon_k3s _ (hc.chal 2) _ x hx

theorem canon3_multFold (hG : VF.G) (zeta : VF.K3) (N : ℕ) (st : VF.K3 × VF.G) (h : canon3 st.1) :
    canon3 ((List.range N).foldl
      (fun (a : VF.K3 × VF.G) _ => (VF.K3.mul a.1 (VF.K3.sub zeta (VF.K3.ofG a.2)), VF.mul a.2 hG)) st).1 := by
  induction N generalizing st with
  | zero => simpa using h
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact canon3_mul _ _

theorem canon3_multOf (XI : ExecInst) (zeta : VF.K3) (t : TabInst) : canon3 (multOf XI zeta t) :=
  canon3_multFold _ _ _ _ canon3_one

theorem selsOf_pw (XI : ExecInst) (π : FlatProof) (j : ℕ) (hj : j < 4 + XI.k) :
    ((selsOf XI π)[j]!).toList.Pairwise (· < ·) := by
  unfold selsOf
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [Array.getElem_map, Array.getElem_range]
  exact treeSel_pw _ _ _ _

section HZ
open NockvmE2E.Deep NockvmE2E.Rap Polynomial
variable {Φ : CoinFrame} {ι β : Type} [Fintype KC] [DecidableEq KC] {colRound : ι → ℕ}

omit [Fintype KC] in
/-- `hZ` from the trace-domain link: if `P.H` is exactly the image of `i ↦ hShift·hGen^i` (`i < hN`) and that map is injective on `[0,hN)` -/
theorem hZ_of_H (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) (P : DeepParams Φ KC ι β colRound) (ζ : KC)
    (hz : canon3 (zetaOf XI FS z π)) (hS : canon XI.hShift) (hζ : toKV (zetaOf XI FS z π) = ζ)
    (hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i))
    (hinj : Set.InjOn (fun i => psiV XI.hShift * psiV XI.hGen ^ i) (Finset.range XI.hN : Set ℕ)) :
    toKV (zhOf XI FS z π) = eval ζ P.Zpoly := by
  rw [toKV_zh XI FS z π hz hS, hζ]
  unfold DeepParams.Zpoly
  rw [eval_prod, hH, Finset.prod_image hinj]
  simp [eval_sub, eval_C, eval_X]
end HZ
end NockvmE2E.Exec.V


/-! ### pass 3 consequences -/
namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.VL

/-- **`flatOk_merkle` without the sortedness hypothesis**: the selection of every tree is strictly increasing by construction of `treeSel`. -/
theorem flatOk_merkle' (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) (j : ℕ)
    (hj : j < 4 + XI.k) (hne : ¬ (j < 4 ∧ (blockLayout XI).1[j]! = 0))
    :
    let W := (blockLayout XI).1
    let sel := (selsOf XI π)[j]!
    let sp := if j < 4 then ragSpec W[j]! (2 ^ (XI.nD - 1)) else friSpec (2 ^ (XI.nD - (j - 3)))
    let vs := π.vals[j]!
    let leaf (r : Nat) : Dg5 :=
      if j < 4 then [vs[r]!, 0, 0, 0, 0] else [vs[3 * r]!, vs[3 * r + 1]!, vs[3 * r + 2]!, 0, 0]
    AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
      (fun a l r' => (fun i l r => H ([tagNode, j, i] ++ l ++ r)) (SM.heapIdx a 1) l r')
      (SM.mkOpening (fun i => sel[lb sel i]? == some i)
        (fun i => leaf (lb sel i)) (SM.skelOf sp sp.total sp.total) (π.sibs[j]!).toList).values
      (SM.mkOpening (fun i => sel[lb sel i]? == some i)
        (fun i => leaf (lb sel i)) (SM.skelOf sp sp.total sp.total) (π.sibs[j]!).toList).proof
      = π.roots[j]! := by
  exact flatOk_merkle XI H FS z π hok j hj hne (selsOf_pw XI π j hj)


/-- the verifier's per-query FRI check (`friSteps` over words `1..k`, then the final polynomial) is `walkK` -/
theorem fri_query_iff_walkK (XI : ExecInst) (vals sels : Array (Array Nat)) (alphas pfinal : Array VF.K3) (q : Nat)
    (word0 : Nat → VF.K3) :
    (∃ res, friSteps XI vals sels alphas q (List.range' 1 XI.k)
        (foldK3 (word0 (q % 2 ^ (XI.nD - 1))) (word0 (q % 2 ^ (XI.nD - 1) + 2 ^ (XI.nD - 1)))
          (yAt XI 0 (q % 2 ^ (XI.nD - 1))) alphas[0]!) (q % 2 ^ (XI.nD - 1)) = .ok res ∧
      (res.1 == VF.K3.horner pfinal (VF.K3.ofG (yAt XI (XI.k + 1) res.2))) = true) ↔
    SF.walkK XI word0 (faV vals sels) (fbV vals sels) alphas pfinal q = true :=
  friSteps_iff XI vals sels alphas pfinal q XI.k 1 _ _

/-- limbs of challenges produced by a Fiat-Shamir function with limbs `< p` are canonical -/
theorem chalCan_of_FS (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof)
    (hFS : ∀ key n, ∀ x ∈ FS key n, x < NockvmE2E.Exec.p) : ChalCan XI FS z π := by
  intro i x hx
  unfold chalsOf at hx
  by_cases hi : i < ((Array.range (msgsOf XI π).size).map fun i =>
      if roundNl XI i == 0 then [] else FS (z :: ((msgsOf XI π).extract 0 (i + 1)).toList) (roundNl XI i)).size
  · rw [getElem!_pos _ i hi, Array.getElem_map] at hx
    split at hx
    · simp at hx
    · exact hFS _ _ x hx
  · rw [getElem!_neg _ i hi] at hx
    exact absurd hx List.not_mem_nil

/-! ### non-vacuity of `AllCanon` / `InstCan` / `ChalCan` (a trivial instance and the constant-`1` Fiat-Shamir function) -/
def toyInst : ExecInst :=
  { nD := 3, dShift := 3, dGen := 2, hN := 1, hGen := 1, hShift := 1, r := 2, k := 1, d := 1, l := 1, nc := 0, nq := 0,
    colKind := #[], blockOf := #[], pre := #[], pubOf := #[], ppt := VF.K3.one, nCoins := #[0, 0], derived := #[],
    tabs := #[], pubMode := 1 }

theorem toyInst_canon : InstCan toyInst where
  hShift := by unfold canon; decide
  ppt := canon3_one
  pre := fun c g hg => by
    exfalso
    rw [getElem!_neg toyInst.pre c (by simp [toyInst])] at hg
    exact Array.not_mem_empty g hg
  shared := fun t ht => by simp [toyInst] at ht
  cons := fun t ht => by simp [toyInst] at ht

theorem toy_allCanon (z : List Nat) (π : FlatProof) : AllCanon toyInst (fun _ n => List.replicate n 1) z π :=
  ⟨toyInst_canon, chalCan_of_FS _ _ _ _ (fun _ n x hx => by
    have := List.eq_of_mem_replicate hx; subst this; unfold NockvmE2E.Exec.p; decide)⟩


section DC3
open NockvmE2E.Deep NockvmE2E.Rap Polynomial
variable {Φ : CoinFrame} {ι β : Type} [Fintype KC] [DecidableEq KC] {colRound : ι → ℕ}

/-- the table terms `mult_t · cv_{t,i}` of the verifier, in `KC`, in table order (what the audited `A.Cv_i` must equal) -/
noncomputable def termsOfK (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) : List KC :=
  termsK (alphaOf XI FS z π) (tabCv XI FS z π) (multOf XI (zetaOf XI FS z π)) XI.tabs.toList

/-- the verifier's `lhs` read in `KC`: the Horner form of the table terms -/
theorem toKV_lhsOf (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    toKV (lhsOf XI FS z π) = hornerA (toKV (alphaOf XI FS z π)) (termsOfK XI FS z π) := by
  have := tabs_fold (alphaOf XI FS z π) (tabCv XI FS z π) (multOf XI (zetaOf XI FS z π)) XI.tabs.toList VF.K3.zero VF.K3.one
    canon3_zero canon3_one (fun t ht => tabCv_canon XI H FS z π hok t ht) (fun t _ => canon3_multOf XI _ t)
  obtain ⟨_, _, h3, _⟩ := this
  unfold lhsOf termsOfK
  rw [← Array.foldl_toList, h3, toKV_zero, toKV_one, zero_add, one_mul]

/-- **L10 core, multi-table, every canonicity side condition read off `FlatOk`**: the verifier accepts ⇒ `DeepCheck`.
Hypotheses that remain (instance/J-8 side): `hα`/`hζ` (audited coins = decoded blocks), `hlen`/`hdag` (the table terms are the audited `A.Cv`; the
multiplier `mult_t` of the verifier is the audited `Zout`, see `toKV_multOf`), `hH`/`hinj` (the trace domain), `he`/`hnq`/`hqlen`/`hcw`/`hQ`. -/
theorem deepCheck_of_flatOk' (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof)
    (P : DeepParams Φ KC ι β colRound) {r : ℕ} (A : AirShape P r) (χ : Coins Φ KC) (α ζ : KC)
    (vT : ι × Fin r → KC) (vQ : Fin P.nq → KC) (hok : FlatOk XI H FS z π)
    (hα : toKV (alphaOf XI FS z π) = α) (hζ : toKV (zetaOf XI FS z π) = ζ)
    (hlen : (termsOfK XI FS z π).length = P.ns)
    (hdag : ∀ i : Fin (termsOfK XI FS z π).length, (termsOfK XI FS z π).get i = A.Cv χ ζ (Fin.cast hlen i) vT)
    (hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i))
    (hinj : Set.InjOn (fun i => psiV XI.hShift * psiV XI.hGen ^ i) (Finset.range XI.hN : Set ℕ))
    (he : P.e = 3) (hnq : XI.nq = P.nq) (hqlen : π.vQ.size = P.nq)
    (hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j)
    (hQ : ∀ j : Fin P.nq, toKV π.vQ[j.1]! = vQ j) : DeepCheck P A χ α ζ vT vQ := by
  have hc := allCanon_of_flatOk XI H FS z π hok
  have hz := canon3_zetaOf XI FS z π hc.chal
  have hcard : P.H.card = XI.hN := by
    rw [hH, Finset.card_image_of_injOn hinj, Finset.card_range]
  have h := flatOk_deep XI H FS z π hok
  unfold qsumOf at h
  rw [hnq] at h
  refine deepCheck_of_flatKm P A χ α ζ vT vQ _ _ _ _ _ π.vQ hα (by rw [← hα]; exact toKV_lhsOf XI H FS z π hok) hlen hdag
    (hZ_of_H XI FS z π P ζ hz hc.inst.hShift hζ hH hinj) he ?_ hqlen hcw hQ h
  rw [toKV_pow, hζ, hcard]

end DC3

/-! ### the multiplier `mult_t` and `ζ ∉ H` -/
theorem canon_inj (a b : UInt64) (ha : canon a) (hb : canon b) (h : zv a = zv b) : a = b := by
  unfold zv at h
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact UInt64.toNat_inj.mp this

theorem toKV_inj (x y : VF.K3) (hx : canon3 x) (hy : canon3 y) (h : toKV x = toKV y) : x = y := by
  rw [toKV_eq_toK, toKV_eq_toK] at h
  have h' := Exec.K3.toK_injective h
  have e0 : Gold.ofU64 x.c0 = Gold.ofU64 y.c0 := congrArg Exec.K3.c0 h'
  have e1 : Gold.ofU64 x.c1 = Gold.ofU64 y.c1 := congrArg Exec.K3.c1 h'
  have e2 : Gold.ofU64 x.c2 = Gold.ofU64 y.c2 := congrArg Exec.K3.c2 h'
  have z0 : zv x.c0 = zv y.c0 := by
    have := congrArg Gold.toZ e0; rwa [Gold.ofU64_toZ, Gold.ofU64_toZ] at this
  have z1 : zv x.c1 = zv y.c1 := by
    have := congrArg Gold.toZ e1; rwa [Gold.ofU64_toZ, Gold.ofU64_toZ] at this
  have z2 : zv x.c2 = zv y.c2 := by
    have := congrArg Gold.toZ e2; rwa [Gold.ofU64_toZ, Gold.ofU64_toZ] at this
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  have q0 : a0 = b0 := canon_inj _ _ hx.1 hy.1 z0
  have q1 : a1 = b1 := canon_inj _ _ hx.2.1 hy.2.1 z1
  have q2 : a2 = b2 := canon_inj _ _ hx.2.2 hy.2.2 z2
  subst q0 q1 q2
  rfl

section Mult

theorem toKV_multFold (zeta : VF.K3) (hz : canon3 zeta) (hS hG : UInt64) (hSc : canon hS) : ∀ N : ℕ,
    toKV ((List.range N).foldl
      (fun (st : VF.K3 × UInt64) _ => (VF.K3.mul st.1 (VF.K3.sub zeta (VF.K3.ofG st.2)), VF.mul st.2 hG))
      (VF.K3.one, hS)).1 = ∏ i ∈ Finset.range N, (toKV zeta - psiV hS * psiV hG ^ i) :=
  fun N => (zh_prod zeta hz hS hG hSc N).1

/-- `mult_t(ζ) = ∏_{i<hN-hN_t} (ζ − hShift·hGen^(hN_t+i))` (the audited `Zout H H_t` evaluated at ζ, with `H_t` the first `hN_t` orbit points) -/
theorem toKV_multOf (XI : ExecInst) (zeta : VF.K3) (hz : canon3 zeta) (hS : canon XI.hShift) (t : TabInst) :
    toKV (multOf XI zeta t) =
      ∏ i ∈ Finset.range (XI.hN - t.hN), (toKV zeta - psiV XI.hShift * psiV XI.hGen ^ (t.hN + i)) := by
  have hc : canon (VF.mul XI.hShift (VF.pow XI.hGen t.hN)) := mul_lt _ _
  unfold multOf
  rw [toKV_multFold zeta hz _ XI.hGen hc, psiV_mul, psiV_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-- the verifier's check `ζ ∉ H` makes every `Z_H` factor nonzero: `toKV zh ≠ 0` -/
theorem toKV_zh_ne (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    toKV (zhOf XI FS z π) ≠ 0 := by
  have hc := allCanon_of_flatOk XI H FS z π hok
  have hz := canon3_zetaOf XI FS z π hc.chal
  intro h0
  have hzc : canon3 (zhOf XI FS z π) := by
    unfold zhOf; exact canon3_multFold _ _ _ _ canon3_one
  have := toKV_inj _ _ hzc canon3_zero (by rw [h0, toKV_zero])
  have hz0 := flatOk_zh XI H FS z π hok
  rw [this] at hz0
  simp [VF.K3.isZero, VF.K3.zero] at hz0

/-- **`mult_t(ζ) ≠ 0`** for every table, from the ζ ∉ H check -/
theorem toKV_multOf_ne (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π)
    (t : TabInst) (ht : t.hN ≤ XI.hN) : toKV (multOf XI (zetaOf XI FS z π) t) ≠ 0 := by
  have hc := allCanon_of_flatOk XI H FS z π hok
  have hz := canon3_zetaOf XI FS z π hc.chal
  have h1 := toKV_zh_ne XI H FS z π hok
  rw [toKV_zh XI FS z π hz hc.inst.hShift, Finset.prod_ne_zero_iff] at h1
  rw [toKV_multOf XI _ hz hc.inst.hShift, Finset.prod_ne_zero_iff]
  intro i hi
  exact h1 (t.hN + i) (by simp only [Finset.mem_range] at hi ⊢; omega)

end Mult



theorem vals_get_lt (vals : Array (Array Nat)) (hvals : ∀ a ∈ vals, ∀ x ∈ a, x < NockvmE2E.Exec.p) (j i : ℕ) :
    (vals[j]!)[i]! < NockvmE2E.Exec.p := by
  have hj : ∀ x ∈ vals[j]!, x < NockvmE2E.Exec.p := by
    by_cases hc : j < vals.size
    · rw [getElem!_pos vals j hc]; exact hvals _ (Array.getElem_mem hc)
    · rw [getElem!_neg vals j hc]; intro x hx; exact absurd hx (Array.not_mem_empty x)
  by_cases hi : i < (vals[j]!).size
  · rw [getElem!_pos _ i hi]; exact hj _ (Array.getElem_mem hi)
  · rw [getElem!_neg _ i hi]; unfold NockvmE2E.Exec.p; decide

theorem canon3_friAtV (vals : Array (Array Nat)) (hvals : ∀ a ∈ vals, ∀ x ∈ a, x < NockvmE2E.Exec.p) (j r : ℕ) :
    canon3 (friAtV vals j r) := by
  unfold friAtV
  apply canon3_ofLimbs
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact vals_get_lt vals hvals _ _

/-- **L9 verifier side with the full `Hom`**: a passing `walkK` (= the verifier's per-query FRI check, `fri_query_iff_walkK`) gives the flat
`Walk` read in `KC` through `VL.homV`, with canonicity from `FlatOk` (`vals`, `pfinal`) and the DEEP word (`hw0`: `deepWord` is canonical). -/
theorem walkK_sound_V (XI : ExecInst) (word0 : ℕ → VF.K3) (vals sels : Array (Array Nat)) (alphas pfinal : Array VF.K3) (q : ℕ)
    (hvals : ∀ a ∈ vals, ∀ x ∈ a, x < NockvmE2E.Exec.p) (hpf : ∀ x ∈ pfinal, canon3 x)
    (hw0 : ∀ i, canon3 (word0 i)) (h : SF.walkK XI word0 (faV vals sels) (fbV vals sels) alphas pfinal q = true) :
    SF.Walk (homV.ψ XI.dShift) (homV.ψ XI.dGen) XI.nD XI.k
      (fun w i => homV.φ (SF.Wf XI word0 (faV vals sels) (fbV vals sels) w i)) (fun i => homV.φ alphas[i]!)
      (SF.hornerF (fun j => homV.φ pfinal[j]!) pfinal.size) q :=
  SF.walkK_sound homV XI word0 (faV vals sels) (fbV vals sels) alphas pfinal q hw0
    (fun w g => canon3_friAtV vals hvals _ _) (fun w g => canon3_friAtV vals hvals _ _)
    (fun j hj => by
      by_cases hc : j < pfinal.size
      · rw [getElem!_pos pfinal j hc]; exact hpf _ (Array.getElem_mem hc)
      · omega) h


theorem foldl_canon3 {α : Type} (l : List α) (f : VF.K3 → α → VF.K3) (acc : VF.K3) (h0 : canon3 acc)
    (hf : ∀ a x, canon3 a → canon3 (f a x)) : canon3 (l.foldl f acc) := by
  induction l generalizing acc with
  | nil => exact h0
  | cons x l ih => exact ih _ (hf _ _ h0)

theorem canon3_deepWordS (XI : ExecInst) (pts : Array VF.K3) (ops : List (ℕ × ℕ × VF.K3 × VF.K3)) (baseAt : ℕ → ℕ → G) (idx : ℕ) :
    canon3 (SF.deepWordS XI pts ops baseAt idx) := by
  rw [SF.deepWordS_eq]
  exact foldl_canon3 _ _ _ canon3_zero (fun a x ha => canon3_add _ _ ha (canon3_mul _ _))

theorem modify_get (a : Array VF.K3) (c p : ℕ) (f : VF.K3 → VF.K3) (hp : p < a.size) :
    (a.modify c f)[p]! = if c = p then f a[p]! else a[p]! := by
  have hp' : p < (a.modify c f).size := by simpa using hp
  rw [getElem!_pos _ p hp', getElem!_pos a p hp]
  by_cases hc : c = p
  · subst hc; simp [Array.modify, Array.modifyM, hp]
  · simp [Array.modify, Array.modifyM, hc]
    split <;> simp_all [Array.getElem_set]

theorem foldl_ext {α β : Type} (l : List β) (f g : α → β → α) (a : α) (h : ∀ x ∈ l, ∀ t, f t x = g t x) :
    l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp) a]
    exact ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- the verifier's `deepWord` (array accumulation by opening point) is the regrouped `deepWordS` of SoundFri -/
theorem deepWord_eq (XI : ExecInst) (pts : Array VF.K3) (ops : Array (ℕ × ℕ × VF.K3 × VF.K3)) (baseAt : ℕ → ℕ → G) (idx : ℕ) :
    deepWord XI pts ops baseAt idx = SF.deepWordS XI pts ops.toList baseAt idx := by
  rw [SF.deepWordS_eq]
  unfold deepWord
  have key : ∀ (l : List (ℕ × ℕ × VF.K3 × VF.K3)) (acc : Array VF.K3) (n : ℕ), acc.size = n →
      (l.foldl (fun (accs : Array VF.K3) (o : ℕ × ℕ × VF.K3 × VF.K3) =>
        accs.modify o.2.1 fun a => VF.K3.add a (VF.K3.mul o.2.2.1 (VF.K3.sub (VF.K3.ofG (baseAt o.1 idx)) o.2.2.2))) acc).size = n ∧
      ∀ p, p < n → (l.foldl (fun (accs : Array VF.K3) (o : ℕ × ℕ × VF.K3 × VF.K3) =>
        accs.modify o.2.1 fun a => VF.K3.add a (VF.K3.mul o.2.2.1 (VF.K3.sub (VF.K3.ofG (baseAt o.1 idx)) o.2.2.2))) acc)[p]! =
        l.foldl (fun (a : VF.K3) (o : ℕ × ℕ × VF.K3 × VF.K3) =>
          if o.2.1 = p then VF.K3.add a (VF.K3.mul o.2.2.1 (VF.K3.sub (VF.K3.ofG (baseAt o.1 idx)) o.2.2.2)) else a) acc[p]! := by
    intro l
    induction l with
    | nil => intro acc n h; exact ⟨h, fun p _ => rfl⟩
    | cons o l ih =>
      intro acc n h
      simp only [List.foldl_cons]
      have hs : (acc.modify o.2.1 fun a => VF.K3.add a (VF.K3.mul o.2.2.1 (VF.K3.sub (VF.K3.ofG (baseAt o.1 idx)) o.2.2.2))).size = n := by
        simpa using h
      obtain ⟨h1, h2⟩ := ih _ n hs
      refine ⟨h1, fun p hp => ?_⟩
      rw [h2 p hp, modify_get _ _ _ _ (by omega)]
  dsimp only
  rw [List.range_eq_range']
  refine foldl_ext _ _ _ _ ?_
  intro p hp t
  have hp' : p < XI.r + 2 := by simpa using (List.mem_range'_1.mp hp).2
  have hrep : (Array.replicate (XI.r + 2) VF.K3.zero)[p]! = VF.K3.zero := by
    rw [getElem!_pos _ p (by simpa using hp')]; simp
  have := (key ops.toList (Array.replicate (XI.r + 2) VF.K3.zero) _ (by simp)).2 p hp'
  rw [this, hrep]
  rfl

theorem canon3_deepWord (XI : ExecInst) (pts : Array VF.K3) (ops : Array (ℕ × ℕ × VF.K3 × VF.K3)) (baseAt : ℕ → ℕ → G) (idx : ℕ) :
    canon3 (deepWord XI pts ops baseAt idx) := by
  rw [deepWord_eq]; exact canon3_deepWordS _ _ _ _ _


end NockvmE2E.Exec.V

/-! ## Non-vacuity (kernel `decide` / instantiation; no `native_decide`) -/
namespace NockvmE2E.Exec.V

/-- the Merkle hypotheses are inhabited: a 2-leaf FRI-shaped tree with both leaves selected and an empty frontier -/
example : ∃ root, goRoot (fun l => l.take 5) (friSpec 2) 0 #[0, 1] (fun r => [r + 1, 0, 0, 0, 0]) #[] 1 0 2 0 =
    some (root, (#[] : Array Dg5).size) :=
  ⟨(fun l => l.take 5) ([tagNode, 0, 1] ++ [1, 0, 0, 0, 0] ++ [2, 0, 0, 0, 0]), by decide⟩

example : ∃ root, goRoot (fun l => l.take 5) (friSpec 2) 0 #[0, 1] (fun r => [r + 1, 0, 0, 0, 0]) #[] 1 0 2 0 =
    some (root, (#[] : Array Dg5).size) ∧ (#[0, 1] : Array Nat).toList.Pairwise (· < ·) ∧ 1 ≤ (friSpec 2).total :=
  ⟨(fun l => l.take 5) ([tagNode, 0, 1] ++ [1, 0, 0, 0, 0] ++ [2, 0, 0, 0, 0]), by decide, by decide, by decide⟩

/-- instantiation of `merkle_of_goRoot` on that tree -/
example : AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
      (fun a l r' => (fun i l r => (fun (l : List Nat) => l.take 5) ([tagNode, 0, i] ++ l ++ r)) (SM.heapIdx a 1) l r')
      (SM.mkOpening (fun i => (#[0, 1] : Array Nat)[lb #[0, 1] i]? == some i)
        (fun i => (fun r => [r + 1, 0, 0, 0, 0]) (lb #[0, 1] i)) (SM.skelOf (friSpec 2) (friSpec 2).total (friSpec 2).total)
        (#[] : Array Dg5).toList).values
      (SM.mkOpening (fun i => (#[0, 1] : Array Nat)[lb #[0, 1] i]? == some i)
        (fun i => (fun r => [r + 1, 0, 0, 0, 0]) (lb #[0, 1] i)) (SM.skelOf (friSpec 2) (friSpec 2).total (friSpec 2).total)
        (#[] : Array Dg5).toList).proof
      = (fun l => l.take 5) ([tagNode, 0, 1] ++ [1, 0, 0, 0, 0] ++ [2, 0, 0, 0, 0]) :=
  SM.merkle_of_goRoot (fun l => l.take 5) (friSpec 2) (SM.wf_friSpec 2) 0 #[0, 1] (by decide) (fun r => [r + 1, 0, 0, 0, 0])
    #[] _ (by decide) (by decide)

/-- the table-slice lemma and the canonical `Hom` laws are satisfiable on `K3.one` -/
example := deepTable VF.K3.one (VL.toKV VF.K3.one) rfl VF.K3.one 3 [VF.K3.one, VF.K3.zero] VF.K3.zero VL.canon3_zero
example : VL.toKV (VF.K3.add VF.K3.one VF.K3.one) = VL.toKV VF.K3.one + VL.toKV VF.K3.one :=
  VL.toKV_add _ _ VL.canon3_one VL.canon3_one
example : (VF.mul 0xFFFFFFFF00000000 3).toNat = (0xFFFFFFFF00000000 * 3) % NockvmE2E.Exec.p := VL.mul_toNat _ _

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.verifyFlatE_ok_iff
#print axioms NockvmE2E.Exec.V.verifyFlat_iff
#print axioms NockvmE2E.Exec.V.treeCheck_root
#print axioms NockvmE2E.Exec.V.deepCheck_of_flatK
#print axioms NockvmE2E.Exec.V.deepSlice
#print axioms NockvmE2E.Exec.V.zh_prod
#print axioms NockvmE2E.Exec.V.flatOk_merkle
#print axioms NockvmE2E.Exec.V.deepTable
#print axioms NockvmE2E.Exec.V.canon_evalDag
#print axioms NockvmE2E.Exec.V.flatOk_deep
#print axioms NockvmE2E.Exec.V.flatOk_pos
#print axioms NockvmE2E.Exec.V.flatOk_trees
#print axioms NockvmE2E.Exec.V.flatOk_offdom
#print axioms NockvmE2E.Exec.VL.homV
#print axioms NockvmE2E.Exec.V.friSteps_iff
#print axioms NockvmE2E.Exec.V.fri_query_iff_walkK
#print axioms NockvmE2E.Exec.V.walkK_sound_V
#print axioms NockvmE2E.Exec.V.selsOf_pw
#print axioms NockvmE2E.Exec.V.flatOk_merkle'
#print axioms NockvmE2E.Exec.V.tabCv_canon
#print axioms NockvmE2E.Exec.V.toKV_lhsOf
#print axioms NockvmE2E.Exec.V.toKV_multOf
#print axioms NockvmE2E.Exec.V.toKV_multOf_ne
#print axioms NockvmE2E.Exec.V.allCanon_of_flatOk
#print axioms NockvmE2E.Exec.V.tabs_fold
#print axioms NockvmE2E.Exec.V.deepCheck_of_flatKm
#print axioms NockvmE2E.Exec.V.flatOk_limbs
#print axioms NockvmE2E.Exec.V.hZ_of_H
#print axioms NockvmE2E.Exec.V.deepCheck_of_flatOk'
#print axioms NockvmE2E.Exec.V.deepWord_eq
#print axioms NockvmE2E.Exec.V.canon3_deepWord
#print axioms NockvmE2E.Exec.V.toy_allCanon
#print axioms NockvmE2E.Exec.SF.input_word_eq
#print axioms NockvmE2E.Exec.SF.walkK_sound
#print axioms NockvmE2E.Exec.SF.deepWordS_hom
