/-
the preg bridge.  `pregOkF` (the Bool gate on the ALU's loaded preprocessed columns `2..4`) gives nock's
`AcceptsJ9AL.PregOK` for `preL k = polyOfArr (pre[col0 + 2 + k])`, the prims decoded by `primsOfPub`.
* `pregVal_zv`: the loader's `pregVal` (UInt64 limbs) is `CheckJ9AL.pregCol` (field elements) of the decoded prims;
* `pregCol_of_pregOkF`: the pointwise evaluation of the loaded polynomials at the nodes `hGen^i`;
* `PregBridgeN`, `pregBridgeN` (proved by unfolding), and `pregOK_of_pregOkF`.
Not zero-knowledge.
-/
import NockvmE2E.J9AL.PbOfX9L
import NockvmE2E.Exec.MaskBridge
import NockvmE2E.Exec.SoundPub
import Nock.V1J9AL.CheckJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.PregJ9AL

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.MaskOkK NockvmE2E.Exec.MaskBridge
open NockvmE2E.J9A.RunGate9L NockvmE2E.Exec.MaskOk
open NockvmE2E.Exec.VF (G)
open NockvmE2E.Exec.J8Shape (tabs_all_mem)
open NockvmE2E.J9AL.PbOfX9L (primsOf)
open NockvmE2E.J8.InstJ8 (P)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (primCode)

/-! ## 1. `pregVal` is `pregCol` -/

theorem getD_cast (l : List ℕ) : ∀ i : ℕ, ((l.map (Nat.cast : ℕ → ZMod P)).getD i 0) = ((l.getD i 0 : ℕ) : ZMod P) := by
  induction l with
  | nil => intro i; simp only [List.map_nil, List.getD_nil, Nat.cast_zero]
  | cons a l ih =>
    intro i
    cases i with
    | zero => simp only [List.map_cons, List.getD_cons_zero]
    | succ i => simp only [List.map_cons, List.getD_cons_succ]; exact ih i

theorem getD_lt (l : List ℕ) (hl : ∀ x ∈ l, x < VF.PN) : ∀ i : ℕ, l.getD i 0 < VF.PN := by
  induction l with
  | nil => intro i; simp [VF.PN]
  | cons a l ih =>
    intro i
    cases i with
    | zero => simpa using hl a (by simp)
    | succ i => simpa using ih (fun x hx => hl x (by simp [hx])) i

theorem zv_ofNat_lt (n : ℕ) (h : n < VF.PN) : zv (UInt64.ofNat n) = (n : ZMod P) := by
  unfold zv
  rw [UInt64.toNat_ofNat_of_lt' (by unfold VF.PN at h; rw [UInt64.size]; omega)]
  rfl

/-- the decoded table `qs` re-encodes to the loader's `(id, code)` list -/
theorem roundtrip_data (ps : List PE.PrimRec) (h : primsRoundTrip ps = true) :
    ∃ qs, primsOfPub ps = some qs ∧ qs.map (fun q => (q.1, primCode q.2)) = ps.map (fun q => (q.id, q.code)) := by
  unfold primsRoundTrip at h
  cases hq : primsOfPub ps with
  | none => simp [hq] at h
  | some qs => exact ⟨qs, rfl, by simpa [hq] using h⟩

theorem primsOf_eq (XI : ExecInst) (qs : List (ℕ × Nock.Jet.Prim.PrimOp)) (h : primsOfPub XI.pubIn.prims = some qs) :
    primsOf XI = qs := by
  unfold primsOf; rw [h]; rfl

/-- **`pregVal_zv`**: the loader's preg column value `pregVal ps k i` (`k < 3`) is nock's `pregCol qs k i`, `qs` the decoded prims -/
theorem pregVal_zv (ps : List PE.PrimRec) (qs : List (ℕ × Nock.Jet.Prim.PrimOp))
    (hmap : qs.map (fun q => (q.1, primCode q.2)) = ps.map (fun q => (q.id, q.code)))
    (hb : ∀ q ∈ ps, q.id < VF.PN ∧ q.code < VF.PN) (k i : ℕ) (hk : k < 3) :
    zv (pregVal ps k i) = (Nock.V1J9AL.CheckJ9AL.pregCol qs k i : ZMod P) := by
  have hlen : qs.length = ps.length := by simpa using congrArg List.length hmap
  have hid : qs.map Prod.fst = ps.map PE.PrimRec.id := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hmap
  have hcode : qs.map (fun q => primCode q.2) = ps.map PE.PrimRec.code := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.snd) hmap
  unfold pregVal Nock.V1J9AL.CheckJ9AL.pregCol
  by_cases h0 : k = 0
  · subst h0
    simp only [beq_self_eq_true, ite_true, if_true, hlen]
    split_ifs
    · rfl
    · rfl
  · by_cases h1 : k = 1
    · subst h1
      simp only [beq_self_eq_true, ite_true, Nat.one_ne_zero, if_false, beq_iff_eq]
      have e : (qs.map fun q => ((q.1 : ℕ) : ZMod P)) = (qs.map Prod.fst).map (Nat.cast : ℕ → ZMod P) := by
        simp [List.map_map, Function.comp_def]
      rw [e, hid, getD_cast, zv_ofNat_lt]
      exact getD_lt _ (fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact (hb q hq).1) i
    · have h2 : k = 2 := by omega
      subst h2
      simp only [beq_iff_eq, show ((2 : ℕ) = 0) = False from by decide, show ((2 : ℕ) = 1) = False from by decide, ite_false]
      have e : (qs.map fun q => ((primCode q.2 : ℕ) : ZMod P)) = (qs.map fun q => primCode q.2).map (Nat.cast : ℕ → ZMod P) := by
        simp [List.map_map, Function.comp_def]
      rw [e, hcode, getD_cast, zv_ofNat_lt]
      exact getD_lt _ (fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact (hb q hq).2) i

/-! ## 2. evaluation of the loaded columns -/

/-- `eval_of_pat` without `canon hGen` (the generator is replaced by its canonical residue `gCan`, which has the same powers) -/
theorem eval_of_pat' (pa : Array G) (g : G) (hp : ∀ c ∈ pa.toList, canon c) (n : Nat) (f : ℕ → G)
    (h : evalNodes pa g n = (Array.range n).map f) : ∀ j < n, (polyOfArr pa).eval (zv g ^ j) = zv (f j) := by
  have e : evalNodes pa (gCan g) n = evalNodes pa g n := by
    unfold evalNodes; exact evalNodesAux_gCan _ _ _ _ _
  have := eval_of_pat pa (gCan g) (gCan_canon g) hp n f (e.trans h)
  intro j hj
  have h2 := this j hj
  rwa [gCan_zv] at h2

/-- **`pregCol_of_pregOkF`**: at the ALU table `t`, the loaded column `2 + k` evaluates, at the node `hGen^i` (`i < hN`), to `pregCol (primsOf XI) k i`;
and `|prims| ≤ hN` -/
theorem pregCol_of_pregOkF {F : Fam} (XI : ExecInst) (hsh : shapeOkF F XI = true) (hpreg : pregOkF XI = true)
    (hrt : primsRoundTrip XI.pubIn.prims = true) (tab : TabInst) (hmem : tab ∈ XI.tabs.toList) (hid : tab.chip.id = "aluChipJ9") :
    (primsOf XI).length ≤ tab.hN ∧
    ∀ (k : Fin 3) (i : ℕ), i < tab.hN →
      (polyOfArr XI.pre[tab.col0 + 2 + (k : ℕ)]!).eval (zv XI.hGen ^ i) =
        (Nock.V1J9AL.CheckJ9AL.pregCol (primsOf XI) (k : ℕ) i : ZMod P) := by
  obtain ⟨qs, hqs, hmap⟩ := roundtrip_data _ hrt
  have hpo := primsOf_eq XI qs hqs
  have hlen : qs.length = XI.pubIn.prims.length := by simpa using congrArg List.length hmap
  have hall := tabs_all_mem (f := fun t => if t.chip.id == "aluChipJ9" then _ else true) hpreg tab hmem
  simp only [hid, beq_self_eq_true, ite_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hall
  obtain ⟨⟨hl, hb⟩, hk⟩ := hall
  have hb' : ∀ q ∈ XI.pubIn.prims, q.id < VF.PN ∧ q.code < VF.PN := by
    intro q hq
    have := hb q hq
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  rw [hpo]
  refine ⟨by rw [hlen]; exact hl, fun k i hi => ?_⟩
  have hk' := hk k.1 (List.mem_range.mpr k.2)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk'
  obtain ⟨hsz, hev⟩ := hk'
  have hgd : XI.pre.getD (tab.col0 + 2 + k.1) #[] = XI.pre[tab.col0 + 2 + k.1]! := by
    by_cases hc : tab.col0 + 2 + k.1 < XI.pre.size
    · rw [getElem!_pos XI.pre _ hc, Array.getD, dif_pos hc]; rfl
    · rw [getElem!_neg XI.pre _ hc, Array.getD, dif_neg hc]; rfl
  rw [hgd] at hev
  rw [eval_of_pat' _ XI.hGen (hpreC_of_shapeF hsh _) tab.hN (pregVal XI.pubIn.prims k.1) hev i hi]
  exact pregVal_zv _ qs hmap hb' k.1 i k.2

/-- the loaded column `2 + k` of the ALU has at most `hN_t` entries -/
theorem preL_size_of_pregOkF (XI : ExecInst) (hpreg : pregOkF XI = true)
    (tab : TabInst) (hmem : tab ∈ XI.tabs.toList) (hid : tab.chip.id = "aluChipJ9") (k : Fin 3) :
    (XI.pre[tab.col0 + 2 + (k : ℕ)]!).size ≤ tab.hN := by
  have hall := tabs_all_mem (f := fun t => if t.chip.id == "aluChipJ9" then _ else true) hpreg tab hmem
  simp only [hid, beq_self_eq_true, ite_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hall
  obtain ⟨-, hk⟩ := hall
  have hk' := hk k.1 (List.mem_range.mpr k.2)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk'
  have hsz := hk'.1
  have hgd : XI.pre.getD (tab.col0 + 2 + k.1) #[] = XI.pre[tab.col0 + 2 + k.1]! := by
    by_cases hc : tab.col0 + 2 + k.1 < XI.pre.size
    · rw [getElem!_pos XI.pre _ hc, Array.getD, dif_pos hc]; rfl
    · rw [getElem!_neg XI.pre _ hc, Array.getD, dif_neg hc]; rfl
  rwa [hgd] at hsz

/-! ## 3. the bridge to nock's `PregOK` -/

/-- the shape we need from nockvm: the pointwise pre-column check implies `PregOK` -/
def PregBridgeN : Prop := ∀ {n : ℕ} (nodes : Fin n → ZMod P) (prims : List (ℕ × Nock.Jet.Prim.PrimOp)) (preL : Fin 3 → (ZMod P)[X]),
  prims.length ≤ n →
  (∀ (k : Fin 3) (i : Fin n), (preL k).eval (nodes i) = (Nock.V1J9AL.CheckJ9AL.pregCol prims (k : ℕ) (i : ℕ) : ZMod P)) →
  Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.PregOK nodes prims preL

theorem pregBridgeN : PregBridgeN := by
  intro n nodes prims preL hlen hv
  refine ⟨hlen, fun i => ⟨?_, ?_, ?_⟩⟩
  · simpa [Nock.V1J9AL.CheckJ9AL.pregCol] using hv 0 i
  · simpa [Nock.V1J9AL.CheckJ9AL.pregCol] using hv 1 i
  · simpa [Nock.V1J9AL.CheckJ9AL.pregCol] using hv 2 i

/-- **`pregOK_of_pregOkF`**: the `hALst` conjunct `PregOK` for a datum whose ALU nodes are the powers `hGen^i`, `nL = hN_t`, and whose `preL` is the loaded
column polynomials -/
theorem pregOK_of_pregOkF {F : Fam} (XI : ExecInst) (hsh : shapeOkF F XI = true) (hpreg : pregOkF XI = true)
    (hrt : primsRoundTrip XI.pubIn.prims = true) (tab : TabInst) (hmem : tab ∈ XI.tabs.toList) (hid : tab.chip.id = "aluChipJ9")
    {n : ℕ} (nodes : Fin n → ZMod P) (hn : n = tab.hN) (hnodes : ∀ i : Fin n, nodes i = zv XI.hGen ^ (i : ℕ))
    (preL : Fin 3 → (ZMod P)[X]) (hpre : ∀ k : Fin 3, preL k = polyOfArr XI.pre[tab.col0 + 2 + (k : ℕ)]!) :
    Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.PregOK nodes (primsOf XI) preL := by
  obtain ⟨hl, hv⟩ := pregCol_of_pregOkF XI hsh hpreg hrt tab hmem hid
  refine pregBridgeN nodes _ preL (hn ▸ hl) (fun k i => ?_)
  rw [hpre k, hnodes i]
  exact hv k i (hn ▸ i.2)

end NockvmE2E.J9AL.PregJ9AL

#print axioms NockvmE2E.J9AL.PregJ9AL.pregVal_zv
#print axioms NockvmE2E.J9AL.PregJ9AL.eval_of_pat'
#print axioms NockvmE2E.J9AL.PregJ9AL.pregCol_of_pregOkF
#print axioms NockvmE2E.J9AL.PregJ9AL.preL_size_of_pregOkF
#print axioms NockvmE2E.J9AL.PregJ9AL.pregBridgeN
#print axioms NockvmE2E.J9AL.PregJ9AL.pregOK_of_pregOkF
