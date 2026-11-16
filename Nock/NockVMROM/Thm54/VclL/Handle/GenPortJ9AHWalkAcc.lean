/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHWalkAcc.lean

The exec walk table (`Nock.V1J8.Gen.walkGenRows`) computes `q` from `scanN fos`, the children sums from
  `childSums α kr fos curs` and `ln cnt acc` from `walkLCA`.  Over the honest BFS rows `W := walkRows cells reads`
  (generically `W = bfsForest l`, `kr = l.length`) and `curs` with `toK curs[i] = curCol nodeVal W (i+1)`:

  * `scanN_getD`, `q_eq`            : `q = qH kr (foCol W) (j+1)`;
  * `bfs_child_pos`                 : the `c`-th child of row `j` sits at row `kr + Sf (foCol W) j + c`;
  * `childSums_eq`                  : `toK cc_j = Σ_{l ∈ Icc 1 fo} α^l · chldCol (j+1) l`;
  * `walkLCA_eq`                    : `ln = α^(j+1)`, `cnt = countH`, `acc = accH`
    (by induction on the `foldl`, with the `walkSatInGate_explicit` / `honest_walk_acc_zero` fields as recursion).
-/
import Nock.V1J8.GenMem
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkAcc

open Nock Nock.Walk Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.GenWalk

variable {LT : Type*}

/-- The exec walk row of a trie node (design C2 §1.2). -/
def wrowOf (t : NTree WN) : Nock.V1J8.Gen.WRow :=
  ⟨t.label.node, t.label.root, VclL.axisFold t.label.bits, t.label.bits.length, t.label.cL, t.label.cR,
    t.label.mL, t.label.mR⟩

/-! ## 0. Generic list helpers -/

theorem sum_map_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem toK_foldl_add (L : List K3) : ∀ a : K3,
    K3.toK (L.foldl (· + ·) a) = K3.toK a + (L.map K3.toK).sum := by
  induction L with
  | nil => intro a; simp
  | cons x L ih => intro a; rw [List.foldl_cons, ih, K3.toK_add]; simp [List.sum_cons]; ring

theorem arr_getD (curs : List K3) (i : ℕ) : curs.toArray.getD i 0 = curs.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## 1. `scanN` -/

theorem scanN_aux (l : List ℕ) : ∀ (out : List ℕ) (s : ℕ),
    (l.foldl (fun (st : List ℕ × ℕ) x => (st.1 ++ [st.2 + x], st.2 + x)) (out, s)).1
      = out ++ (List.range l.length).map (fun j => s + ∑ i ∈ Finset.range (j + 1), l.getD i 0) := by
  induction l with
  | nil => intro out s; simp
  | cons x l ih =>
    intro out s
    simp only [List.foldl_cons]
    rw [ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.append_assoc]
    congr 1
    simp only [List.singleton_append]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    rw [Finset.sum_range_succ' _ (j + 1)]
    simp
    omega

theorem scanN_getD_gen (fos : List ℕ) (j : ℕ) (hj : j < fos.length) :
    (scanN fos).getD j 0 = ∑ i ∈ Finset.range (j + 1), fos.getD i 0 := by
  unfold scanN
  rw [scanN_aux fos [] 0]
  simp [List.getD_eq_getElem?_getD, hj]

/-! ## 2. The honest columns in terms of the fan-out list -/

theorem foCol_succ (W : List (NTree LT)) (j : ℕ) :
    foCol W (j + 1) = (W.map (fun t => t.children.length)).getD j 0 := by
  simp [foCol, List.getD_eq_getElem?_getD, List.getElem?_map]

theorem Sf_eq_range (W : List (NTree LT)) (j : ℕ) :
    Sf (foCol W) j = ∑ i ∈ Finset.range j, (W.map (fun t => t.children.length)).getD i 0 := by
  unfold Sf
  rw [sum_Icc_one_eq_range]
  exact Finset.sum_congr rfl (fun i _ => foCol_succ W i)

/-- `q_eq` at a generic BFS forest. -/
theorem q_eq_gen (l : List (NTree LT)) (fos : List ℕ)
    (hfos : fos = (bfsForest l).map (fun t => t.children.length)) (j : ℕ)
    (hj : j < (bfsForest l).length) :
    (scanN fos).getD j 0 = Sf (foCol (bfsForest l)) (j + 1) ∧
      l.length + (scanN fos).getD j 0 - (j + 1) = GenWalk.qH l.length (foCol (bfsForest l)) (j + 1) := by
  have hlen : fos.length = (bfsForest l).length := by simp [hfos]
  have h1 : (scanN fos).getD j 0 = Sf (foCol (bfsForest l)) (j + 1) := by
    rw [scanN_getD_gen fos j (by omega), Sf_eq_range, hfos]
  exact ⟨h1, by rw [h1]; rfl⟩

/-! ## 3. BFS child position -/

theorem length_take_flatMap (W : List (NTree LT)) (j : ℕ) (hj : j ≤ W.length) :
    ((W.take j).flatMap NTree.children).length
      = ∑ i ∈ Finset.range j, (W.map (fun t => t.children.length)).getD i 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < W.length := hj
    rw [List.take_succ, List.getElem?_eq_getElem hj', Option.toList_some, List.flatMap_append,
      List.length_append, ih (by omega), Finset.sum_range_succ]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']

theorem flatMap_index (L : List (NTree LT)) (j c : ℕ) (hj : j < L.length)
    (hc : c < (L[j]).children.length) :
    (L.flatMap NTree.children)[((L.take j).flatMap NTree.children).length + c]? = (L[j]).children[c]? := by
  have hL : L = L.take j ++ (L[j] :: L.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have h1 : L.flatMap NTree.children
      = (L.take j).flatMap NTree.children ++ ((L[j]).children ++ (L.drop (j + 1)).flatMap NTree.children) := by
    conv_lhs => rw [hL]
    rw [List.flatMap_append, List.flatMap_cons]
  rw [h1, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hc]

/-- **`bfs_child_pos`**: the `c`-th child of row `j` of `bfsForest l` is at row `l.length + Sf (foCol W) j + c`. -/
theorem bfs_child_pos_gen (l : List (NTree LT)) (hl : l ≠ []) (j c : ℕ)
    (hj : j < (bfsForest l).length) (hc : c < ((bfsForest l)[j]).children.length) :
    (bfsForest l)[l.length + Sf (foCol (bfsForest l)) j + c]? = ((bfsForest l)[j]).children[c]? := by
  have hW := bfsForest_eq_append_flatMap l hl
  have h2 : ∀ i, (bfsForest l)[l.length + i]? = ((bfsForest l).flatMap NTree.children)[i]? := by
    intro i
    have := congrArg (fun L => L[l.length + i]?) hW
    rw [this, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  rw [Sf_eq_range, ← length_take_flatMap _ j (by omega), add_assoc, h2]
  exact flatMap_index _ j c hj hc

/-! ## 4. `childSums` -/

/-- One children sum `cc` starting at queue position `p` with fan-out `f`. -/
def ccAt (α : K3) (curs : Array K3) (p f : ℕ) : K3 :=
  ((List.range f).map fun l => CompX.powK α (l + 1) * curs.getD (p + l) 0).foldl (· + ·) 0

theorem childSums_eq_fold (α : K3) (kr : ℕ) (fos : List ℕ) (curs : Array K3) :
    childSums α kr fos curs
      = (fos.foldl (fun (st : List K3 × ℕ) f => (st.1 ++ [ccAt α curs st.2 f], st.2 + f)) ([], kr)).1 := rfl

theorem childSums_aux (α : K3) (curs : Array K3) (fos : List ℕ) : ∀ (out : List K3) (p : ℕ),
    (fos.foldl (fun (st : List K3 × ℕ) f => (st.1 ++ [ccAt α curs st.2 f], st.2 + f)) (out, p)).1
      = out ++ (List.range fos.length).map (fun j =>
          ccAt α curs (p + ∑ i ∈ Finset.range j, fos.getD i 0) (fos.getD j 0)) := by
  induction fos with
  | nil => intro out p; simp
  | cons x fos ih =>
    intro out p
    simp only [List.foldl_cons]
    rw [ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.append_assoc,
      List.singleton_append]
    have hh : ccAt α curs p x
        = ccAt α curs (p + ∑ i ∈ Finset.range 0, (x :: fos).getD i 0) ((x :: fos).getD 0 0) := by
      rw [Finset.sum_range_zero]; rfl
    have ht : List.map (fun j => ccAt α curs (p + x + ∑ i ∈ Finset.range j, fos.getD i 0) (fos.getD j 0))
          (List.range fos.length)
        = List.map ((fun j => ccAt α curs (p + ∑ i ∈ Finset.range j, (x :: fos).getD i 0)
            ((x :: fos).getD j 0)) ∘ Nat.succ) (List.range fos.length) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      have : p + ∑ i ∈ Finset.range (j + 1), (x :: fos).getD i 0
          = p + x + ∑ i ∈ Finset.range j, fos.getD i 0 := by
        rw [Finset.sum_range_succ' _ j]; simp; omega
      rw [this]; rfl
    exact congrArg (out ++ ·) (congrArg₂ List.cons hh ht)

theorem childSums_length (α : K3) (kr : ℕ) (fos : List ℕ) (curs : Array K3) :
    (childSums α kr fos curs).length = fos.length := by
  rw [childSums_eq_fold, childSums_aux]
  simp

theorem childSums_getD (α : K3) (kr : ℕ) (fos : List ℕ) (curs : Array K3) (j : ℕ) (hj : j < fos.length) :
    (childSums α kr fos curs).getD j 0
      = ((List.range (fos.getD j 0)).map fun l =>
          CompX.powK α (l + 1) * curs.getD (kr + ∑ i ∈ Finset.range j, fos.getD i 0 + l) 0).foldl (· + ·) 0 := by
  rw [childSums_eq_fold, childSums_aux]
  simp [List.getD_eq_getElem?_getD, hj, ccAt]

/-- **`childSums_eq`** at a generic BFS forest. -/
theorem childSums_eq_gen (l : List (NTree LT)) (hl : l ≠ []) (nodeVal : NTree LT → KC) (α : K3)
    (curs : List K3)
    (hcur : curs.length = (bfsForest l).length ∧
      ∀ i < (bfsForest l).length, K3.toK (curs.getD i 0) = curCol nodeVal (bfsForest l) (i + 1))
    (fos : List ℕ) (hfos : fos = (bfsForest l).map (fun t => t.children.length))
    (j : ℕ) (hj : j < (bfsForest l).length) :
    K3.toK ((childSums α l.length fos curs.toArray).getD j 0)
      = ∑ c ∈ Finset.Icc 1 (foCol (bfsForest l) (j + 1)),
          (K3.toK α) ^ c * chldCol nodeVal (bfsForest l) (j + 1) c := by
  have hlen : fos.length = (bfsForest l).length := by simp [hfos]
  rw [childSums_getD α l.length fos curs.toArray j (by omega), toK_foldl_add, K3.toK_zero, zero_add,
    List.map_map, sum_map_range, foCol_succ, ← hfos, sum_Icc_one_eq_range]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mem_range] at hc
  have hfj : fos.getD j 0 = ((bfsForest l)[j]).children.length := by
    rw [hfos]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [hfj] at hc
  have hpos := bfs_child_pos_gen l hl j c hj hc
  have hS : ∑ i ∈ Finset.range j, fos.getD i 0 = Sf (foCol (bfsForest l)) j := by
    rw [Sf_eq_range, hfos]
  have hcc : ((bfsForest l)[j]).children[c]? = some (((bfsForest l)[j]).children[c]) :=
    List.getElem?_eq_getElem hc
  rw [hcc] at hpos
  have hidx : l.length + Sf (foCol (bfsForest l)) j + c < (bfsForest l).length :=
    (List.getElem?_eq_some_iff.mp hpos).1
  simp only [Function.comp, K3.toK_mul, CompX.toK_powK, arr_getD]
  rw [hS, hcur.2 _ hidx]
  simp [curCol, chldCol, hpos, List.getElem?_eq_getElem hj, hcc]

/-! ## 5. `walkLCA` -/

abbrev LSt := List (K3 × K3 × K3) × K3 × K3 × K3

/-- The step of `walkLCA`'s fold, as a named function. -/
def lcaStep (α : K3) (kr : ℕ) (curs : List K3) : LSt → (ℕ × K3) × ℕ → LSt :=
  fun st (fc, i) =>
    match st with
    | (out, lnP, cntP, accP) =>
      let ln := if i = 0 then α else α * lnP
      let cnt := if i = 0 then CompX.powK α kr * CompX.powK α fc.1 else cntP * CompX.powK α fc.1
      let acc := if i = 0 then CompX.powK α kr * fc.2
        else accP + cntP * fc.2 - (if i < kr then 0 else ln * curs.getD i 0)
      (out ++ [(ln, cnt, acc)], ln, cnt, acc)

theorem walkLCA_eq_fold (α : K3) (kr : ℕ) (fos : List ℕ) (ccs curs : List K3) :
    walkLCA α kr fos ccs curs
      = (((fos.zip ccs).zipIdx 0).foldl (lcaStep α kr curs) ([], 0, 0, 0)).1 := rfl

theorem lcaStep_spec (α : K3) (kr : ℕ) (curs : List K3) (out : List (K3 × K3 × K3)) (lnP cntP accP : K3)
    (f : ℕ) (c : K3) (i : ℕ) :
    ∃ L C A : K3, lcaStep α kr curs (out, lnP, cntP, accP) ((f, c), i) = (out ++ [(L, C, A)], L, C, A) ∧
      L = (if i = 0 then α else α * lnP) ∧
      C = (if i = 0 then CompX.powK α kr * CompX.powK α f else cntP * CompX.powK α f) ∧
      A = (if i = 0 then CompX.powK α kr * c
        else accP + cntP * c - (if i < kr then 0 else L * curs.getD i 0)) :=
  ⟨_, _, _, rfl, rfl, rfl, rfl⟩

theorem getD_append_last (out : List (K3 × K3 × K3)) (x : K3 × K3 × K3) (j : ℕ) (hj : j < out.length) :
    (out ++ [x]).getD j (0, 0, 0) = out.getD j (0, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem getD_append_new (out : List (K3 × K3 × K3)) (x : K3 × K3 × K3) :
    (out ++ [x]).getD out.length (0, 0, 0) = x := by
  simp [List.getD_eq_getElem?_getD]

theorem zipIdx_zip_getElem? (fos : List ℕ) (ccs : List K3) (n : ℕ) (hn : n < fos.length)
    (hc : n < ccs.length) :
    ((fos.zip ccs).zipIdx 0)[n]? = some ((fos.getD n 0, ccs.getD n 0), n) := by
  simp [List.getElem?_zipIdx, List.getElem?_zip_eq_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hc]

/-- **The `walkLCA` invariant**, by induction on the number of processed rows. -/
theorem lca_inv (l : List (NTree LT)) (hl : l ≠ []) (nodeVal : NTree LT → KC) (α : K3) (curs : List K3)
    (hcur : curs.length = (bfsForest l).length ∧
      ∀ i < (bfsForest l).length, K3.toK (curs.getD i 0) = curCol nodeVal (bfsForest l) (i + 1))
    (fos : List ℕ) (hfos : fos = (bfsForest l).map (fun t => t.children.length))
    (ccs : List K3) (hccl : ccs.length = (bfsForest l).length)
    (hcc : ∀ j < (bfsForest l).length, K3.toK (ccs.getD j 0)
      = ∑ c ∈ Finset.Icc 1 (foCol (bfsForest l) (j + 1)),
          (K3.toK α) ^ c * chldCol nodeVal (bfsForest l) (j + 1) c) :
    ∀ n ≤ (bfsForest l).length, ∃ (out : List (K3 × K3 × K3)) (lnP cntP accP : K3),
      (((fos.zip ccs).zipIdx 0).take n).foldl (lcaStep α l.length curs) ([], 0, 0, 0)
        = (out, lnP, cntP, accP) ∧
      out.length = n ∧
      (∀ j < n, K3.toK (out.getD j (0, 0, 0)).1 = (K3.toK α) ^ (j + 1) ∧
        K3.toK (out.getD j (0, 0, 0)).2.1
          = GenWalk.countH (foCol (bfsForest l)) (K3.toK α) l.length (j + 1) ∧
        K3.toK (out.getD j (0, 0, 0)).2.2
          = GenWalk.accH (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l))
              (foCol (bfsForest l)) (K3.toK α) l.length (j + 1)) ∧
      (∀ m, n = m + 1 → (lnP, cntP, accP) = out.getD m (0, 0, 0)) := by
  have hlen : fos.length = (bfsForest l).length := by simp [hfos]
  have hw := (GenWalk.honest_walk_acc_zero nodeVal l hl (K3.toK α)).1
  have hfoc : ∀ j, foCol (bfsForest l) (j + 1) = fos.getD j 0 := fun j => by rw [foCol_succ, hfos]
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨[], 0, 0, 0, rfl, rfl, fun j hj => absurd hj (by omega), fun m hm => absurd hm (by omega)⟩
  | succ n ih =>
    intro hn
    obtain ⟨out, lnP, cntP, accP, hst, hol, hout, hlast⟩ := ih (by omega)
    obtain ⟨L, C, A, hstep, hL, hC, hA⟩ :=
      lcaStep_spec α l.length curs out lnP cntP accP (fos.getD n 0) (ccs.getD n 0) n
    have hget := zipIdx_zip_getElem? fos ccs n (by omega) (by omega)
    have htake : ((fos.zip ccs).zipIdx 0).take (n + 1)
        = ((fos.zip ccs).zipIdx 0).take n ++ [((fos.getD n 0, ccs.getD n 0), n)] := by
      rw [List.take_succ, hget]; rfl
    have hnew : K3.toK L = (K3.toK α) ^ (n + 1) ∧
          K3.toK C = GenWalk.countH (foCol (bfsForest l)) (K3.toK α) l.length (n + 1) ∧
          K3.toK A = GenWalk.accH (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l))
            (foCol (bfsForest l)) (K3.toK α) l.length (n + 1) := by
        have hcurn := hcur.2 n (by omega)
        have hccn := hcc n (by omega)
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp only [if_true] at hL hC hA
          have hL' : K3.toK L = (K3.toK α) ^ (0 + 1) := by rw [hL]; simp
          refine ⟨hL', ?_, ?_⟩
          · rw [hC, K3.toK_mul, CompX.toK_powK, CompX.toK_powK]
            simp only [GenWalk.countH, hfoc]
            rw [Sf_one, hfoc]
          · rw [hA, K3.toK_mul, CompX.toK_powK, hccn]
            have := hw.accInit
            simp only [GenWalk.accH] at this ⊢
            rw [this, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _; ring
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          have hprev := hout m (by omega)
          have hlp := hlast m rfl
          have hl1 : lnP = (out.getD m (0, 0, 0)).1 := congrArg Prod.fst hlp
          have hl2 : cntP = (out.getD m (0, 0, 0)).2.1 := congrArg (fun x => x.2.1) hlp
          have hl3 : accP = (out.getD m (0, 0, 0)).2.2 := congrArg (fun x => x.2.2) hlp
          have hn0 : (m + 1 = 0) = False := by simp
          simp only [hn0, if_false] at hL hC hA
          have hLk : K3.toK L = (K3.toK α) ^ (m + 1 + 1) := by
            rw [hL, K3.toK_mul, hl1, hprev.1, pow_succ]; ring
          refine ⟨hLk, ?_, ?_⟩
          · rw [hC, K3.toK_mul, CompX.toK_powK, hl2, hprev.2.1, ← hfoc (m + 1)]
            simp only [GenWalk.countH]
            rw [Sf_succ (foCol (bfsForest l)) (m + 1), pow_add]; ring
          · have hstp := hw.accStep (m + 1) (by omega) (by omega)
            have hacc_prev := hprev.2.2
            rw [← hl3] at hacc_prev
            have hcnt_prev : K3.toK cntP
                = GenWalk.countH (foCol (bfsForest l)) (K3.toK α) l.length (m + 1) := by
              rw [hl2]; exact hprev.2.1
            have hlnk : K3.toK α ^ (m + 1 + 1) = GenWalk.lnH (K3.toK α) (m + 1 + 1) := rfl
            have hs : ∑ c ∈ Finset.Icc 1 (foCol (bfsForest l) (m + 1 + 1)),
                (K3.toK α) ^ c * GenWalk.countH (foCol (bfsForest l)) (K3.toK α) l.length (m + 1)
                  * chldCol nodeVal (bfsForest l) (m + 1 + 1) c
                = GenWalk.countH (foCol (bfsForest l)) (K3.toK α) l.length (m + 1) *
                  ∑ c ∈ Finset.Icc 1 (foCol (bfsForest l) (m + 1 + 1)),
                    (K3.toK α) ^ c * chldCol nodeVal (bfsForest l) (m + 1 + 1) c := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
            rw [← hlnk] at hstp
            by_cases hq : m + 1 < l.length
            · have hdeq : deqCoeff (K := KC) l.length (m + 1 + 1) = 0 :=
                deqCoeff_of_le (K := KC) (by omega)
              rw [hdeq] at hstp
              rw [hA, if_pos hq, K3.toK_sub, K3.toK_add, K3.toK_mul, K3.toK_zero, hccn, hacc_prev, hcnt_prev]
              linear_combination (-1 : KC) * hstp - hs
            · have hdeq : deqCoeff (K := KC) l.length (m + 1 + 1) = 1 :=
                deqCoeff_of_gt (K := KC) (by omega)
              rw [hdeq] at hstp
              rw [hA, if_neg hq, K3.toK_sub, K3.toK_add, K3.toK_mul, K3.toK_mul, hccn, hacc_prev,
                hcnt_prev, hLk, hcurn]
              linear_combination (-1 : KC) * hstp - hs
    refine ⟨out ++ [(L, C, A)], L, C, A, ?_, by simp [hol], ?_, ?_⟩
    · rw [htake, List.foldl_append, hst]; simpa using hstep
    · intro j hj
      by_cases hjn : j < n
      · rw [getD_append_last out _ j (by omega)]; exact hout j hjn
      · have hj' : j = n := by omega
        subst hj'
        have h := getD_append_new out (L, C, A)
        rw [hol] at h
        rw [h]; exact hnew
    · intro m hm
      have hm' : m = n := by omega
      subst hm'
      have h := getD_append_new out (L, C, A)
      rw [hol] at h
      rw [h]

/-- **`walkLCA_eq`** at a generic BFS forest. -/
theorem walkLCA_eq_gen (l : List (NTree LT)) (hl : l ≠ []) (nodeVal : NTree LT → KC) (α : K3)
    (curs : List K3)
    (hcur : curs.length = (bfsForest l).length ∧
      ∀ i < (bfsForest l).length, K3.toK (curs.getD i 0) = curCol nodeVal (bfsForest l) (i + 1))
    (fos : List ℕ) (hfos : fos = (bfsForest l).map (fun t => t.children.length))
    (j : ℕ) (hj : j < (bfsForest l).length) :
    ∀ v, v = (walkLCA α l.length fos (childSums α l.length fos curs.toArray) curs).getD j (0, 0, 0) →
      K3.toK v.1 = (K3.toK α) ^ (j + 1) ∧
      K3.toK v.2.1 = GenWalk.countH (foCol (bfsForest l)) (K3.toK α) l.length (j + 1) ∧
      K3.toK v.2.2 = GenWalk.accH (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l))
        (foCol (bfsForest l)) (K3.toK α) l.length (j + 1) := by
  intro v hv
  have hlen : fos.length = (bfsForest l).length := by simp [hfos]
  have hccl : (childSums α l.length fos curs.toArray).length = (bfsForest l).length := by
    rw [childSums_length]; exact hlen
  have hcc : ∀ j < (bfsForest l).length,
      K3.toK ((childSums α l.length fos curs.toArray).getD j 0)
        = ∑ c ∈ Finset.Icc 1 (foCol (bfsForest l) (j + 1)),
            (K3.toK α) ^ c * chldCol nodeVal (bfsForest l) (j + 1) c :=
    fun j hj => childSums_eq_gen l hl nodeVal α curs hcur fos hfos j hj
  obtain ⟨out, lnP, cntP, accP, hst, hol, hout, -⟩ :=
    lca_inv l hl nodeVal α curs hcur fos hfos _ hccl hcc (bfsForest l).length le_rfl
  have hz : ((fos.zip (childSums α l.length fos curs.toArray)).zipIdx 0).length
      = (bfsForest l).length := by simp [hlen, hccl]
  rw [List.take_of_length_le hz.le] at hst
  have hw : walkLCA α l.length fos (childSums α l.length fos curs.toArray) curs = out := by
    rw [walkLCA_eq_fold, hst]
  rw [hw] at hv
  subst hv
  exact hout j hj

/-! ## 6. The card statements at `W := walkRows cells reads` -/

/-- The executable fan-out list. -/
abbrev fosOf (cells : List Noun) (reads : List (Noun × ℕ)) : List ℕ :=
  ((walkRows cells reads).map wrowOf).map foW

theorem foW_wrowOf (cells : List Noun) (reads : List (Noun × ℕ)) (t : NTree WN)
    (ht : t ∈ walkRows cells reads) : foW (wrowOf t) = t.children.length := by
  obtain ⟨c, hc, hct⟩ := (mem_bfsForest _ t).mp ht
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩
  · obtain ⟨n', bs', T', rfl, -⟩ := inTree_trie_inv _ (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
      hct _ _ _ rfl trivial
    rw [trie_fanout]; rfl
  · obtain ⟨n', bs', T', rfl, -⟩ := inTree_trie_inv _ (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
      hct _ _ _ rfl trivial
    rw [trie_fanout]; rfl

theorem fosOf_eq (cells : List Noun) (reads : List (Noun × ℕ)) :
    fosOf cells reads = (walkRows cells reads).map (fun t => t.children.length) := by
  show ((walkRows cells reads).map wrowOf).map foW = _
  rw [List.map_map]
  exact List.map_congr_left (fun t ht => foW_wrowOf cells reads t ht)

theorem scanN_getD (cells : List Noun) (reads : List (Noun × ℕ)) (j : ℕ)
    (hj : j < (walkRows cells reads).length) :
    (scanN (fosOf cells reads)).getD j 0 = Sf (foCol (walkRows cells reads)) (j + 1) :=
  (q_eq_gen (walkForest cells reads) _ (fosOf_eq cells reads) j hj).1

theorem q_eq (cells : List Noun) (reads : List (Noun × ℕ)) (j : ℕ)
    (hj : j < (walkRows cells reads).length) :
    krW cells reads + (scanN (fosOf cells reads)).getD j 0 - (j + 1)
      = GenWalk.qH (krW cells reads) (foCol (walkRows cells reads)) (j + 1) :=
  (q_eq_gen (walkForest cells reads) _ (fosOf_eq cells reads) j hj).2

theorem bfs_child_pos (cells : List Noun) (reads : List (Noun × ℕ)) (j c : ℕ)
    (hj : j < (walkRows cells reads).length)
    (hc : c < ((walkRows cells reads)[j]).children.length) :
    (walkRows cells reads)[krW cells reads + Sf (foCol (walkRows cells reads)) j + c]?
      = ((walkRows cells reads)[j]).children[c]? :=
  bfs_child_pos_gen (walkForest cells reads) (walkForest_ne_nil cells reads) j c hj hc

theorem childSums_eq (cells : List Noun) (reads : List (Noun × ℕ)) (nodeVal : NTree WN → KC) (α : K3)
    (curs : List K3)
    (hcur : curs.length = (walkRows cells reads).length ∧
      ∀ i < (walkRows cells reads).length,
        K3.toK (curs.getD i 0) = curCol nodeVal (walkRows cells reads) (i + 1))
    (j : ℕ) (hj : j < (walkRows cells reads).length) :
    K3.toK ((childSums α (krW cells reads) (fosOf cells reads) curs.toArray).getD j 0)
      = ∑ l ∈ Finset.Icc 1 (foCol (walkRows cells reads) (j + 1)),
          (K3.toK α) ^ l * chldCol nodeVal (walkRows cells reads) (j + 1) l :=
  childSums_eq_gen (walkForest cells reads) (walkForest_ne_nil cells reads) nodeVal α curs hcur _
    (fosOf_eq cells reads) j hj

theorem walkLCA_eq (cells : List Noun) (reads : List (Noun × ℕ)) (nodeVal : NTree WN → KC) (α : K3)
    (curs : List K3)
    (hcur : curs.length = (walkRows cells reads).length ∧
      ∀ i < (walkRows cells reads).length,
        K3.toK (curs.getD i 0) = curCol nodeVal (walkRows cells reads) (i + 1))
    (j : ℕ) (hj : j < (walkRows cells reads).length) :
    ∀ v, v = (walkLCA α (krW cells reads) (fosOf cells reads)
        (childSums α (krW cells reads) (fosOf cells reads) curs.toArray) curs).getD j (0, 0, 0) →
      K3.toK v.1 = (K3.toK α) ^ (j + 1) ∧
      K3.toK v.2.1 = GenWalk.countH (foCol (walkRows cells reads)) (K3.toK α) (krW cells reads) (j + 1) ∧
      K3.toK v.2.2 = GenWalk.accH (curCol nodeVal (walkRows cells reads))
        (chldCol nodeVal (walkRows cells reads)) (foCol (walkRows cells reads)) (K3.toK α)
        (krW cells reads) (j + 1) :=
  walkLCA_eq_gen (walkForest cells reads) (walkForest_ne_nil cells reads) nodeVal α curs hcur _
    (fosOf_eq cells reads) j hj

#print axioms scanN_getD
#print axioms q_eq
#print axioms bfs_child_pos
#print axioms childSums_eq
#print axioms walkLCA_eq
#print axioms foW_wrowOf
#print axioms fosOf_eq

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkAcc
