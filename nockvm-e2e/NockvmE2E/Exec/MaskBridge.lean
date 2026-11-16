/-
  NockvmE2E/Exec/MaskBridge.lean   (the mask bridge `hLagr`; proof-only, Mathlib side)

  `hLagr_of`: from the EXECUTED `maskOk` and `numeralOk` (Exec/MaskOk.lean) plus the J-8 shape and datum numerals, the fixed columns of the final interface
  `(I.JJ npub tp hcap).pre (colJ I npub tp hcap t c)` are `some (monomial sum of the loaded coefficients)` for every preprocessed column of every NON-JET table.
  The jet's registry columns stay TCB (premise `hjet`).
  Route: `maskCol_sound` (MaskOkK, here without the `canon hGen` premise: `maskCol_sound'`) gives `polyOfArr pre = first/last/rootRowMaskW` over the nodes `zv hGen ^ i`;
  `preJ_s*` identify nock's `preprocessing j` / `preprocessingIndex j` of the five non-jet chips with those masks at the `preIdxJ8` positions;
  `pb_facts` / `hNof_tab` give `Pb.nodes* i = zv hGen ^ i`, `Pb.n* = t.hN`; node injectivity is `inj_pows` (hGen's exact order, `orbit_order_of_shape`).
-/
import NockvmE2E.Exec.E2EJ8P
import NockvmE2E.Exec.MaskOkK
import NockvmE2E.Exec.J8Chips

set_option autoImplicit false

namespace NockvmE2E.Exec.MaskBridge
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VF NockvmE2E.Exec.VL NockvmE2E.Exec.MaskOk NockvmE2E.Exec.MaskOkK
open NockvmE2E.J8 NockvmE2E.J8.TieJ8G NockvmE2E.Exec.J8Chips Polynomial
open Nock.Framework Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open NockvmE2E.J8.InstJ8 (Datum preJ preOf preOf_col ω0 hNof tabOf tabId)
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)

/-! ## 1. `polyOfArr` is the monomial sum -/

theorem polyOfList_sum (l : List G) :
    polyOfList l = ((List.range l.length).map fun m => monomial m (zv l[m]!)).sum := by
  induction l with
  | nil => simp [polyOfList]
  | cons c cs ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.sum_cons, List.map_map, polyOfList]
    rw [ih]
    have : ((List.range cs.length).map ((fun m => monomial m (zv (c :: cs)[m]!)) ∘ Nat.succ)).sum
        = Polynomial.X * ((List.range cs.length).map fun m => monomial m (zv cs[m]!)).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro m _
      simp [X_mul_monomial]
    rw [this]
    simp [monomial_zero_left]

theorem polyOfArr_sum (a : Array G) :
    polyOfArr a = ((List.range a.size).map fun m => monomial m (zv a[m]!)).sum := by
  unfold polyOfArr
  rw [polyOfList_sum]
  simp only [Array.length_toList]
  congr 1
  apply List.map_congr_left
  intro m hm
  have hm' : m < a.size := List.mem_range.mp hm
  rw [getElem!_pos a m hm', getElem!_pos a.toList m (by simpa using hm')]
  simp

/-! ## 2. `maskCol_sound` without the `canon hGen` premise -/

def gCan (g : UInt64) : UInt64 := UInt64.ofNat (g.toNat % NockvmE2E.Exec.p)

theorem gCan_toNat (g : UInt64) : (gCan g).toNat = g.toNat % NockvmE2E.Exec.p := by
  unfold gCan
  have h1 := Nat.mod_lt g.toNat Gold.p_pos
  have h2 : NockvmE2E.Exec.p < 2 ^ 64 := by unfold NockvmE2E.Exec.p; norm_num
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem gCan_canon (g : UInt64) : canon (gCan g) := by
  unfold canon; rw [gCan_toNat]; exact Nat.mod_lt _ Gold.p_pos

theorem gCan_zv (g : UInt64) : zv (gCan g) = zv g := by
  unfold zv; rw [gCan_toNat, ZMod.natCast_mod]

theorem mul_gCan (x g : UInt64) : VF.mul x (gCan g) = VF.mul x g := by
  apply UInt64.toNat_inj.mp
  rw [mul_toNat, mul_toNat, gCan_toNat, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem evalNodesAux_gCan (p : Array G) (g : UInt64) : ∀ (k : Nat) (x : G) (acc : Array G),
    evalNodesAux p (gCan g) k x acc = evalNodesAux p g k x acc
  | 0, x, acc => rfl
  | k + 1, x, acc => by simp only [evalNodesAux, mul_gCan, evalNodesAux_gCan p g k]

theorem maskCol_sound' (XI : ExecInst) (n pos : Nat) (hn : 0 < n)
    (hinj : Function.Injective (fun i : Fin n => zv XI.hGen ^ (i : ℕ)))
    (pre : Array G) (hp : ∀ c ∈ pre.toList, canon c) (k : Nat) (h : maskCol XI n pos pre = some k) :
    (pos = 0 → polyOfArr pre = Nock.Framework.firstRowMask (fun i : Fin n => zv XI.hGen ^ (i : ℕ))) ∧
    (pos = 1 → polyOfArr pre = Nock.Framework.lastRowMask hn (fun i : Fin n => zv XI.hGen ^ (i : ℕ))) ∧
    (2 ≤ pos → k ≤ n ∧ polyOfArr pre = Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.rootRowMaskW
        (fun i : Fin n => zv XI.hGen ^ (i : ℕ)) k) := by
  have hE : maskCol XI n pos pre = maskCol { XI with hGen := gCan XI.hGen } n pos pre := by
    have e : evalNodes pre XI.hGen n = evalNodes pre (gCan XI.hGen) n := (evalNodesAux_gCan _ _ _ _ _).symm
    unfold maskCol
    rw [e]
  rw [hE] at h
  have hz : zv ({ XI with hGen := gCan XI.hGen } : ExecInst).hGen = zv XI.hGen := gCan_zv _
  have := maskCol_sound { XI with hGen := gCan XI.hGen } n pos hn (gCan_canon _) (by simp only [hz]; exact hinj) pre hp k h
  simpa only [hz] using this

/-! ## 3. nock's fixed columns of the five non-jet chips -/

/-- the mask at position `pos` -/
noncomputable def Msk {n : ℕ} (pos : ℕ) (nodes : Fin n → ZMod InstJ8.P) (hn : 0 < n) (kr : ℕ) : (ZMod InstJ8.P)[X] :=
  if pos = 0 then firstRowMask nodes else if pos = 1 then lastRowMask hn nodes else rootRowMaskW nodes kr

theorem preOf_of_idx (R : FixedPreprocessingRAP (ZMod InstJ8.P)) (c : Fin R.rap.w) (j : Fin R.fixedCount)
    (h : (R.preprocessingIndex j).val = c.val) : preOf R c = some (R.preprocessing j) := by
  have e : R.preprocessingColumn j = c := Fin.ext h
  rw [← e]; exact preOf_col R j

theorem preJ_s0 (d : Datum) (c pos : ℕ) (h : (c, pos) ∈ (J8Shape.preIdxJ8 "computeChipVCLHX").toList.zipIdx) :
    preJ d (colI 0 c) = some (Msk pos d.Pb.nodes d.Pb.hn 0) := by
  simp [J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl


theorem preJ_s1 (d : Datum) (c pos : ℕ) (h : (c, pos) ∈ (J8Shape.preIdxJ8 "cellChipHQKW").toList.zipIdx) :
    preJ d (colI 1 c) = some (Msk pos d.Pb.nodesC d.Pb.hnC 0) := by
  simp [J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl

theorem preJ_s4 (d : Datum) (c pos : ℕ) (h : (c, pos) ∈ (J8Shape.preIdxJ8 "atomChipHQL").toList.zipIdx) :
    preJ d (colI 4 c) = some (Msk pos d.Pb.nodesA d.Pb.hnA 0) := by
  simp [J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl

theorem preJ_s2 (d : Datum) (c pos : ℕ) (h : (c, pos) ∈ (J8Shape.preIdxJ8 "walkChipJ8").toList.zipIdx) :
    preJ d (colI 2 c) = some (Msk pos d.Pb.nodesW d.Pb.hnW d.Pb.kroots) := by
  simp [J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨2, by show 2 < 3; omega⟩ rfl]; simp [Msk]; rfl

theorem preJ_s5 (d : Datum) (c pos : ℕ) (h : (c, pos) ∈ (J8Shape.preIdxJ8 "walkChipHQK").toList.zipIdx) :
    preJ d (colI 5 c) = some (Msk pos d.Pb.nodesV d.Pb.hnV d.Pb.krootsV) := by
  simp [J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨2, by show 2 < 3; omega⟩ rfl]; simp [Msk]; rfl



/-! ## 4. the fold of `tabMask` -/

/-- the fold step of `tabMask` -/
def stepF (mc : ℕ × ℕ → Option ℕ) (acc : Option ℕ) (x : ℕ × ℕ) : Option ℕ :=
  match acc, mc x with
  | some a, some k => some (max a k)
  | _, _ => none

theorem tabMask_eq (XI : ExecInst) (t : TabInst) (hj : (t.chip.id == "jetChipJ8") = false) :
    tabMask XI t = (J8Shape.preIdxJ8 t.chip.id).toList.zipIdx.foldl
      (stepF (fun x => maskCol XI t.hN x.2 (XI.pre.getD (t.col0 + x.1) #[]))) (some 0) := by
  unfold tabMask
  rw [hj]
  simp only [Bool.false_eq_true, ite_false]
  rfl

theorem fold_none (mc : ℕ × ℕ → Option ℕ) : ∀ l : List (ℕ × ℕ), l.foldl (stepF mc) none = none
  | [] => rfl
  | x :: l => by
    simp only [List.foldl_cons]
    have : stepF mc none x = none := by unfold stepF; split <;> simp_all
    rw [this]; exact fold_none mc l

theorem fold_some (mc : ℕ × ℕ → Option ℕ) : ∀ (l : List (ℕ × ℕ)) (a r : ℕ), l.foldl (stepF mc) (some a) = some r →
    ∀ x ∈ l, ∃ k, mc x = some k
  | [], a, r, _ => fun x hx => absurd hx (by simp)
  | y :: l, a, r, h => by
    simp only [List.foldl_cons] at h
    cases hy : mc y with
    | none =>
      have : stepF mc (some a) y = none := by unfold stepF; rw [hy]
      rw [this, fold_none] at h; cases h
    | some k =>
      have : stepF mc (some a) y = some (max a k) := by unfold stepF; rw [hy]
      rw [this] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨k, hy⟩
      · exact fold_some mc l _ r h x hx



theorem maskCol_lt2 (XI : ExecInst) (n pos : ℕ) (p : Array G) (hpos : pos < 2) (k : ℕ) (h : maskCol XI n pos p = some k) : k = 0 := by
  unfold maskCol at h
  by_cases hs : p.size > n
  · simp [hs] at h
  simp only [hs, ite_false] at h
  rcases (by omega : pos = 0 ∨ pos = 1) with rfl | rfl
  · by_cases hv : (evalNodes p XI.hGen n == rootPat n 1) = true
    · simp [hv] at h; exact h.symm
    · simp [hv] at h
  · by_cases hv : (evalNodes p XI.hGen n == lastPat n) = true
    · simp [hv] at h; exact h.symm
    · simp [hv] at h

/-- for a walk chip the root column's `kroots` is the table's `tabMask` -/
theorem tabMask_walk (XI : ExecInst) (t : TabInst) (hid : t.chip.id = "walkChipJ8" ∨ t.chip.id = "walkChipHQK") (r : ℕ)
    (h : tabMask XI t = some r) :
    maskCol XI t.hN 2 (XI.pre.getD (t.col0 + 2) #[]) = some r := by
  have hj : (t.chip.id == "jetChipJ8") = false := by rcases hid with h | h <;> rw [h] <;> decide
  rw [tabMask_eq XI t hj] at h
  have hl : (J8Shape.preIdxJ8 t.chip.id).toList.zipIdx = [(0, 0), (1, 1), (2, 2)] := by
    rcases hid with h | h <;> rw [h] <;> rfl
  rw [hl] at h
  simp only [List.foldl_cons, List.foldl_nil] at h
  cases h0 : maskCol XI t.hN 0 (XI.pre.getD (t.col0 + 0) #[]) with
  | none => simp only [stepF, h0, fold_none] at h; cases h
  | some k0 =>
  cases h1 : maskCol XI t.hN 1 (XI.pre.getD (t.col0 + 1) #[]) with
  | none => simp only [stepF, h0, h1, fold_none] at h; cases h
  | some k1 =>
  cases h2 : maskCol XI t.hN 2 (XI.pre.getD (t.col0 + 2) #[]) with
  | none => simp only [stepF, h0, h1, h2] at h; cases h
  | some k2 =>
    have e0 := maskCol_lt2 XI _ 0 _ (by omega) _ h0
    have e1 := maskCol_lt2 XI _ 1 _ (by omega) _ h1
    subst e0 e1
    simp only [stepF, h0, h1, h2, Nat.max_zero, Nat.zero_max, Option.some.injEq] at h
    rw [← h]


/-! ## 5. the core: a passing mask column is the mask over the instance's nodes -/

theorem polyOfArr_Msk (XI : ExecInst) (hsh : J8Shape.j8ShapeOk XI = true) (t : TabInst) (hle : t.hN ≤ XI.hN) (arr : Array G)
    (harr : ∀ c ∈ arr.toList, canon c) (pos n : ℕ) (nodes : Fin n → ZMod InstJ8.P) (hn0 : 0 < n)
    (hnodes : ∀ i, nodes i = ω0 XI ^ (i : ℕ)) (hnt : n = t.hN) (kr k : ℕ) (hm : maskCol XI t.hN pos arr = some k)
    (hk : 2 ≤ pos → kr = k) : polyOfArr arr = Msk pos nodes hn0 kr := by
  subst hnt
  have hnodes' : nodes = fun i : Fin t.hN => zv XI.hGen ^ (i : ℕ) := funext hnodes
  subst hnodes'
  have hinj : Function.Injective (fun i : Fin t.hN => zv XI.hGen ^ (i : ℕ)) := InstJ8.inj_pows hsh hle
  obtain ⟨h0, h1, h2⟩ := maskCol_sound' XI t.hN pos hn0 hinj arr harr k hm
  unfold Msk
  by_cases p0 : pos = 0
  · rw [if_pos p0]; exact h0 p0
  by_cases p1 : pos = 1
  · rw [if_neg p0, if_pos p1]; exact h1 p1
  rw [if_neg p0, if_neg p1, hk (by omega)]
  exact (h2 (by omega)).2

theorem pre_getD (a : Array (Array G)) (i : ℕ) : a[i]! = a.getD i #[] := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h]; simp [Array.getD, h]
  · rw [getElem!_neg a i h]; simp [Array.getD, h]; rfl

theorem exists_pos_of_contains (l : List ℕ) (c : ℕ) (h : l.contains c = true) : ∃ pos, (c, pos) ∈ l.zipIdx := by
  have := List.contains_iff_mem.mp h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem this
  exact ⟨i, by simp [List.mk_mem_zipIdx_iff_getElem?, hi]⟩

/-- `numeralOk`: the numeral of a walk table is its `tabMask` -/
theorem numeral_of_ok (XI : ExecInst) (hn : numeralOk XI = true) (t : TabInst) (ht : t ∈ XI.tabs.toList)
    (hid : t.chip.id = "walkChipJ8" ∨ t.chip.id = "walkChipHQK") :
    (chipNumeral t.chip).isSome = true ∧ chipNumeral t.chip = tabMask XI t := by
  unfold numeralOk at hn
  have := (Array.all_eq_true_iff_forall_mem.mp hn) t (Array.mem_def.mpr ht)
  have hw : (t.chip.id == "walkChipJ8" || t.chip.id == "walkChipHQK") = true := by
    rcases hid with h | h <;> rw [h] <;> decide
  simp only [hw, ite_true, Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-! ## 6. the bridge -/

/-- the conclusion of `hLagr` at one column (exactly the statement of `E2EJ8F.exec_e2e_J8F`'s `hLagr`) -/
def LagrAt (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub) (t : Fin I.XI.tabs.size) (c : ℕ) : Prop :=
  (I.JJ npub tp hcap).pre (colJ I npub tp hcap t c) = some
    (((List.range I.XI.pre[I.XI.tabs[t].col0 + c]!.size).map fun m =>
      Polynomial.monomial m (zv (I.XI.pre[I.XI.tabs[t].col0 + c]!)[m]!)).sum)

theorem finish (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub) (t : Fin I.XI.tabs.size) (c pos : ℕ) (n : ℕ)
    (nodes : Fin n → ZMod InstJ8.P) (hn0 : 0 < n) (kr k : ℕ) (hnodes : ∀ i, nodes i = ω0 I.XI ^ (i : ℕ))
    (hnt : n = I.XI.tabs[t].hN)
    (hmc : maskCol I.XI I.XI.tabs[t].hN pos (I.XI.pre.getD (I.XI.tabs[t].col0 + c) #[]) = some k) (hk : 2 ≤ pos → kr = k)
    (hpre : preJ I.d (colI (sigmaX I.XI t) c) = some (Msk pos nodes hn0 kr)) : LagrAt I npub tp hcap t c := by
  have hsh := I.hsh
  have hle : I.XI.tabs[t].hN ≤ I.XI.hN := J8Shape.hle_of_shape hsh _ (Array.getElem_mem_toList t.2)
  have h1 : (I.JJ npub tp hcap).pre (colJ I npub tp hcap t c) = preJ I.d (colI (sigmaX I.XI t) c) := rfl
  unfold LagrAt
  rw [h1, hpre, ← polyOfArr_sum]
  congr 1
  exact (polyOfArr_Msk I.XI hsh I.XI.tabs[t] hle _ (J8Shape.hpreC_of_shape hsh _) pos n nodes hn0 hnodes hnt kr k
    (by rw [pre_getD]; exact hmc) hk).symm

theorem hLagr_of (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)
    (hmask : maskOk I.XI = true) (hnum : numeralOk I.XI = true)
    (hnum0 : ∀ t : Fin I.XI.tabs.size, (chipNumeral I.XI.tabs[t].chip).getD 0 =
      (if sigmaX I.XI t = 2 then I.d.Pb.kroots else if sigmaX I.XI t = 5 then I.d.Pb.krootsV else 0))
    (hjet : ∀ t : Fin I.XI.tabs.size, I.XI.tabs[t].chip.id = "jetChipJ8" → ∀ c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub →
      I.XI.colKind[I.XI.tabs[t].col0 + c]! = 1 → LagrAt I npub tp hcap t c) :
    ∀ (t : Fin I.XI.tabs.size) c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub → I.XI.colKind[I.XI.tabs[t].col0 + c]! = 1 →
      LagrAt I npub tp hcap t c := by
  intro t c hc hk
  have hsh := I.hsh
  have hm : I.XI.tabs[t] ∈ I.XI.tabs.toList := Array.getElem_mem_toList t.2
  have hk1 : 1 ≤ I.XI.hN := by rw [J8Shape.hN_of_shape hsh]; exact Nat.one_le_two_pow
  obtain ⟨-, hmem⟩ := ids_of_shape hsh
  have hid6 := hmem _ hm
  by_cases hjt : I.XI.tabs[t].chip.id = "jetChipJ8"
  · exact hjet t hjt c hc hk
  -- the position of `c` among the mask columns
  have hpk := E2EJ8P.preKind_of_shape hsh _ hm c hc
  rw [hk] at hpk
  have hcont : (J8Shape.preIdxJ8 I.XI.tabs[t].chip.id).contains c = true := by simpa using hpk
  obtain ⟨pos, hpos⟩ := exists_pos_of_contains _ c
    (List.contains_iff_mem.mpr (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hcont)))
  -- the executed mask check at this table
  have hj' : (I.XI.tabs[t].chip.id == "jetChipJ8") = false := by simpa using hjt
  have hsome : (tabMask I.XI I.XI.tabs[t]).isSome = true := by
    unfold maskOk at hmask
    exact (Array.all_eq_true_iff_forall_mem.mp hmask) _ (Array.mem_def.mpr hm)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨k, hmc⟩ := fold_some _ _ 0 r (by rw [← tabMask_eq I.XI I.XI.tabs[t] hj']; exact hr) (c, pos) hpos
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, -, -, -⟩ := E2EJ8P.pb_facts I.XI hsh I.d.Pb I.hd hk1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hid6
  have hn_of : ∀ s : Fin 6, sigmaX I.XI t = s → hNof I.XI (tabId s) = I.XI.tabs[t].hN := fun s hs => by
    have := hNof_tab I.XI hsh t; rwa [hs] at this
  rcases hid6 with hid | hid | hid | hid | hid | hid
  · -- compute
    have hs : sigmaX I.XI t = 0 := by unfold sigmaX tabIdx; rw [hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by simp [J8Shape.preIdxJ8] at hpos; omega
    refine finish I npub tp hcap t c pos I.d.Pb.n I.d.Pb.nodes I.d.Pb.hn 0 k e1 ?_ hmc (fun h => absurd h (by omega)) ?_
    · rw [I.hd]; exact hn_of 0 hs
    · rw [hs]; exact preJ_s0 I.d c pos hpos
  · -- cell
    have hs : sigmaX I.XI t = 1 := by unfold sigmaX tabIdx; rw [hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by simp [J8Shape.preIdxJ8] at hpos; omega
    refine finish I npub tp hcap t c pos I.d.Pb.nC I.d.Pb.nodesC I.d.Pb.hnC 0 k e2 ?_ hmc (fun h => absurd h (by omega)) ?_
    · rw [I.hd]; exact hn_of 1 hs
    · rw [hs]; exact preJ_s1 I.d c pos hpos
  · -- walkJ8
    have hs : sigmaX I.XI t = 2 := by unfold sigmaX tabIdx; rw [hid]; rfl
    have hnumt := numeral_of_ok I.XI hnum _ hm (Or.inl hid)
    have hroot := tabMask_walk I.XI _ (Or.inl hid) r hr
    rw [hid] at hpos
    refine finish I npub tp hcap t c pos I.d.Pb.nW I.d.Pb.nodesW I.d.Pb.hnW I.d.Pb.kroots k e3 ?_ hmc ?_ ?_
    · rw [I.hd]; exact hn_of 2 hs
    · intro h2
      have hpc : c = 2 ∧ pos = 2 := by simp [J8Shape.preIdxJ8] at hpos; omega
      obtain ⟨rfl, rfl⟩ := hpc
      have hkr : k = r := Option.some.inj (hmc.symm.trans hroot)
      have h0 := hnum0 t
      rw [hs, hnumt.2.trans hr] at h0
      simp at h0
      omega
    · rw [hs]; exact preJ_s2 I.d c pos hpos
  · -- atom
    have hs : sigmaX I.XI t = 4 := by unfold sigmaX tabIdx; rw [hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by simp [J8Shape.preIdxJ8] at hpos; omega
    refine finish I npub tp hcap t c pos I.d.Pb.nA I.d.Pb.nodesA I.d.Pb.hnA 0 k e5 ?_ hmc (fun h => absurd h (by omega)) ?_
    · rw [I.hd]; exact hn_of 4 hs
    · rw [hs]; exact preJ_s4 I.d c pos hpos
  · -- walkHQK
    have hs : sigmaX I.XI t = 5 := by unfold sigmaX tabIdx; rw [hid]; rfl
    have hnumt := numeral_of_ok I.XI hnum _ hm (Or.inr hid)
    have hroot := tabMask_walk I.XI _ (Or.inr hid) r hr
    rw [hid] at hpos
    refine finish I npub tp hcap t c pos I.d.Pb.nV I.d.Pb.nodesV I.d.Pb.hnV I.d.Pb.krootsV k e6 ?_ hmc ?_ ?_
    · have hsomeV : (tabOf I.XI "walkChipHQK").isSome = true := by
        have := find_tab I.XI hsh t; rw [hid] at this; rw [this]; rfl
      rw [I.hd]; show (if (tabOf I.XI "walkChipHQK").isSome then hNof I.XI "walkChipHQK" else 1) = _
      rw [if_pos hsomeV]; exact hn_of 5 hs
    · intro h2
      have hpc : c = 2 ∧ pos = 2 := by simp [J8Shape.preIdxJ8] at hpos; omega
      obtain ⟨rfl, rfl⟩ := hpc
      have hkr : k = r := Option.some.inj (hmc.symm.trans hroot)
      have h0 := hnum0 t
      rw [hs, hnumt.2.trans hr] at h0
      simp at h0
      omega
    · rw [hs]; exact preJ_s5 I.d c pos hpos
  · exact absurd hid hjt

end NockvmE2E.Exec.MaskBridge

#print axioms NockvmE2E.Exec.MaskBridge.maskCol_sound'
#print axioms NockvmE2E.Exec.MaskBridge.polyOfArr_sum
#print axioms NockvmE2E.Exec.MaskBridge.preJ_s0
#print axioms NockvmE2E.Exec.MaskBridge.preJ_s1
#print axioms NockvmE2E.Exec.MaskBridge.preJ_s2
#print axioms NockvmE2E.Exec.MaskBridge.preJ_s4
#print axioms NockvmE2E.Exec.MaskBridge.preJ_s5
#print axioms NockvmE2E.Exec.MaskBridge.tabMask_walk
#print axioms NockvmE2E.Exec.MaskBridge.polyOfArr_Msk
#print axioms NockvmE2E.Exec.MaskBridge.hLagr_of
