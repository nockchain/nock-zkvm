/-
  Nock/NockVMROM/Thm54/VclL/Walk/GenWalkRows.lean

  **The honest walk rows — the read trie per root
  in BFS order, fed by the path chip's own read collection.**

  * §1 `WN` (the Noun-level walk label: node, side bits from the root, root, states `cL cR`,
    record multiplicities `mL mR`), `trie root n bs T` (structural on the noun: the node `n` at
    side bits `bs` with the remaining target suffixes `T`; child `b` exists iff some target goes
    strictly deeper through side `b`; `mL / mR` count the targets that END at the left / right
    child — reads are emitted by the target's parent, WALK-F §9).
  * §2 the read collection: `walkRoots` / `targetsOf` read `TraceGen.pathReads`' filter of the
    `Demand`'s `preads` (the same per-`(root, axis)` collection `HonestMemGenPath.pathTable` chains
    over; multiplicity = occurrences, as `pathTable`'s `preads.count r`), `walkForest` (one trie
    per distinct read root; a one-node dummy at `cells.headD` when there is no path read),
    `walkRows := bfsForest walkForest` (trunk `Walk.bfsForest`), `krW := #roots`.
  * §3 structure: every row is a trie node (`inTree_trie_inv`), its children are the trie's
    (`trie_children`), fanout `= cL + cR` (`trie_fanout`), and the depth guard `len ≤ 61`
    (`walkRows_len_le`) from `depthOf ≤ 62` of every path read (the path chip's `h62`).
  * §4 **honest walk gates from trunk**: at the explicit columns `ln i = α^i`,
    `count i = α^kr · α^{Sf fo i}`, `acc = accInGate …` (`WalkInGate.accInGate`), the BFS forest
    satisfies `WalkSatInGate` at `initial_count = α^kr` (`walkSatInGate_explicit`, the explicit
    form of trunk `walkSatInGate_exists`) and the terminal is ZERO (`honest_walk_acc_zero`, from
    trunk `bfsForest_isForestFullBFT` + `forestQueueP_eval` + `walkSatInGate_completeness`), for
    every `nodeVal` and every coin `α` — no coin event on the walk itself.
-/
import Nock.WalkInGate
import Nock.WalkForest
import Nock.NockVMROM.Thm54.TraceGen.GenPathRows
import Nock.NockVMROM.Thm54.P8Core.VclL.Chain

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.GenWalk

open Nock Nock.Walk Nock.NockVMROM.Thm54.VclL
open Polynomial

/-! ## 1. The trie -/

/-- **The Noun-level walk label**: the node, its side bits from the root (root first; prefix
`= axisFold`, `len = bits.length`), the root, the states `cL cR` (continue left / right) and the
path-record multiplicities `mL mR`. -/
structure WN where
  node : Noun
  bits : List Bool
  root : Noun
  cL : Bool
  cR : Bool
  mL : ℕ
  mR : ℕ

/-- The suffixes of the targets that leave through side `b`. -/
def sideTails (b : Bool) (T : List (List Bool)) : List (List Bool) :=
  T.filterMap fun t => match t with
    | c :: s => if c = b then some s else none
    | [] => none

/-- The targets strictly below the side-`b` child (non-empty suffixes). -/
def contT (b : Bool) (T : List (List Bool)) : List (List Bool) :=
  (sideTails b T).filter fun s => !s.isEmpty

/-- The side-`b` child is a walk node iff some target goes strictly deeper through it. -/
def cont (b : Bool) (T : List (List Bool)) : Bool := !(contT b T).isEmpty

/-- The number of targets that END at the side-`b` child (the record multiplicity). -/
def multT (b : Bool) (T : List (List Bool)) : ℕ := (sideTails b T).count []

/-- **The read trie** at node `n`, side bits `bs`, remaining target suffixes `T`. -/
def trie (root : Noun) : Noun → List Bool → List (List Bool) → NTree WN
  | .atom a, bs, T => .node ⟨.atom a, bs, root, false, false, multT false T, multT true T⟩ []
  | .cell l r, bs, T => .node ⟨.cell l r, bs, root, cont false T, cont true T, multT false T, multT true T⟩
      ((if cont false T then [trie root l (bs ++ [false]) (contT false T)] else []) ++
       (if cont true T then [trie root r (bs ++ [true]) (contT true T)] else []))

theorem trie_label (root n : Noun) (bs : List Bool) (T : List (List Bool)) :
    (trie root n bs T).label.node = n ∧ (trie root n bs T).label.bits = bs ∧
      (trie root n bs T).label.root = root := by
  cases n <;> exact ⟨rfl, rfl, rfl⟩

theorem trie_children_cell (root l r : Noun) (bs : List Bool) (T : List (List Bool)) :
    (trie root (.cell l r) bs T).children =
      (if cont false T then [trie root l (bs ++ [false]) (contT false T)] else []) ++
        (if cont true T then [trie root r (bs ++ [true]) (contT true T)] else []) := rfl

theorem trie_states_cell (root l r : Noun) (bs : List Bool) (T : List (List Bool)) :
    (trie root (.cell l r) bs T).label.cL = cont false T ∧
      (trie root (.cell l r) bs T).label.cR = cont true T := ⟨rfl, rfl⟩

/-- `fanout = cL + cR` (`WalkInstance.fanout`'s count) at every trie node. -/
theorem trie_fanout (root n : Noun) (bs : List Bool) (T : List (List Bool)) :
    (trie root n bs T).children.length =
      (if (trie root n bs T).label.cL then 1 else 0) + (if (trie root n bs T).label.cR then 1 else 0) := by
  cases n with
  | atom a => rfl
  | cell l r =>
    rw [trie_children_cell, (trie_states_cell root l r bs T).1, (trie_states_cell root l r bs T).2]
    cases cont false T <;> cases cont true T <;> rfl

/-- **Every subtree of a trie is a trie** whose arguments keep any invariant `Q` closed under the
children step. -/
theorem inTree_trie_inv (root : Noun) (Q : Noun → List Bool → List (List Bool) → Prop)
    (hQ : ∀ l r bs T (b : Bool), Q (.cell l r) bs T → cont b T = true →
      Q (if b then r else l) (bs ++ [b]) (contT b T)) :
    ∀ {c t : NTree WN}, InTree c t → ∀ n bs T, c = trie root n bs T → Q n bs T →
      ∃ n' bs' T', t = trie root n' bs' T' ∧ Q n' bs' T' := by
  intro c t h
  induction h with
  | here c => intro n bs T hc hq; exact ⟨n, bs, T, hc, hq⟩
  | @sub c s t hs _ ih =>
    intro n bs T hc hq
    subst hc
    cases n with
    | atom a => simp [trie, NTree.children] at hs
    | cell l r =>
      rw [trie_children_cell] at hs
      rcases List.mem_append.mp hs with h1 | h1
      · by_cases hb : cont false T = true
        · rw [if_pos hb, List.mem_singleton] at h1
          exact ih _ _ _ h1 (by simpa using hQ l r bs T false hq hb)
        · rw [if_neg hb] at h1; simp at h1
      · by_cases hb : cont true T = true
        · rw [if_pos hb, List.mem_singleton] at h1
          exact ih _ _ _ h1 (by simpa using hQ l r bs T true hq hb)
        · rw [if_neg hb] at h1; simp at h1

/-! ## 2. The read collection and the forest -/

/-- The path-kind reads with multiplicity (`pathReads` before its dedup). -/
def pathKind (preads : List (Noun × ℕ)) : List (Noun × ℕ) := preads.filter fun r => isPathAx r.2

/-- The distinct read roots (first-occurrence order). -/
def walkRoots (preads : List (Noun × ℕ)) : List Noun := ((pathKind preads).map Prod.fst).dedup

/-- The side bits of every path read of root `r`, with multiplicity. -/
def targetsOf (preads : List (Noun × ℕ)) (r : Noun) : List (List Bool) :=
  ((pathKind preads).filter fun x => decide (x.1 = r)).map fun x => axisBits x.2

/-- **The walk forest**: one trie per distinct read root; a one-node dummy at the first cell when
there is no path read (the walk table is never empty). -/
def walkForest (cells : List Noun) (preads : List (Noun × ℕ)) : List (NTree WN) :=
  if walkRoots preads = [] then [trie (cells.headD (.atom 0)) (cells.headD (.atom 0)) [] []]
  else (walkRoots preads).map fun r => trie r r [] (targetsOf preads r)

/-- **The walk rows**: the forest in BFS order (trunk `bfsForest`). -/
def walkRows (cells : List Noun) (preads : List (Noun × ℕ)) : List (NTree WN) :=
  bfsForest (walkForest cells preads)

/-- **`kr`**: the number of read roots (the forest's root count; the dummy counts as one). -/
def krW (cells : List Noun) (preads : List (Noun × ℕ)) : ℕ := (walkForest cells preads).length

theorem walkForest_ne_nil (cells : List Noun) (preads : List (Noun × ℕ)) : walkForest cells preads ≠ [] := by
  unfold walkForest
  split_ifs with h
  · simp
  · simpa using h

theorem one_le_krW (cells : List Noun) (preads : List (Noun × ℕ)) : 1 ≤ krW cells preads := by
  unfold krW
  have := walkForest_ne_nil cells preads
  cases h : walkForest cells preads with
  | nil => exact absurd h this
  | cons _ _ => simp

theorem krW_le_rows (cells : List Noun) (preads : List (Noun × ℕ)) :
    krW cells preads ≤ (walkRows cells preads).length := by
  unfold krW walkRows
  rw [bfsForest_eq_append_flatMap _ (walkForest_ne_nil cells preads), List.length_append]
  omega

theorem mem_walkForest {cells : List Noun} {preads : List (Noun × ℕ)} {c : NTree WN}
    (hc : c ∈ walkForest cells preads) :
    (walkRoots preads = [] ∧ c = trie (cells.headD (.atom 0)) (cells.headD (.atom 0)) [] []) ∨
      ∃ r ∈ walkRoots preads, c = trie r r [] (targetsOf preads r) := by
  unfold walkForest at hc
  split_ifs at hc with h
  · exact Or.inl ⟨h, List.mem_singleton.mp hc⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
    exact Or.inr ⟨r, hr, rfl⟩

/-! ## 3. The depth guard -/

/-- The depth invariant: the node is at depth `≤ 61` and every remaining target is a non-empty
suffix ending at depth `≤ 62`. -/
def DepthInv (_n : Noun) (bs : List Bool) (T : List (List Bool)) : Prop :=
  bs.length ≤ 61 ∧ ∀ s ∈ T, s ≠ [] ∧ bs.length + s.length ≤ 62

theorem mem_sideTails {b : Bool} {T : List (List Bool)} {s : List Bool} (h : s ∈ sideTails b T) :
    b :: s ∈ T := by
  unfold sideTails at h
  obtain ⟨t, ht, he⟩ := List.mem_filterMap.mp h
  match t, he with
  | c :: s', he =>
    simp only at he
    split_ifs at he with hc
    · cases he; rw [← hc]; exact ht

theorem mem_contT {b : Bool} {T : List (List Bool)} {s : List Bool} (h : s ∈ contT b T) :
    b :: s ∈ T ∧ s ≠ [] := by
  unfold contT at h
  obtain ⟨h1, h2⟩ := List.mem_filter.mp h
  refine ⟨mem_sideTails h1, ?_⟩
  rintro rfl; simp at h2

theorem depthInv_step : ∀ l r bs T (b : Bool), DepthInv (.cell l r) bs T → cont b T = true →
    DepthInv (if b then r else l) (bs ++ [b]) (contT b T) := by
  intro l r bs T b hI hc
  obtain ⟨-, hT⟩ := hI
  have hne : contT b T ≠ [] := by
    intro h; simp [cont, h] at hc
  obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hm0, hn0⟩ := mem_contT hs0
  have h0 := (hT _ hm0).2
  have hl0 : 1 ≤ s0.length := List.length_pos_iff.mpr hn0
  simp only [List.length_cons] at h0
  refine ⟨by simp; omega, fun s hs => ?_⟩
  obtain ⟨hm, hn⟩ := mem_contT hs
  have := (hT _ hm).2
  simp only [List.length_cons] at this
  exact ⟨hn, by simp; omega⟩

theorem targetsOf_depth {preads : List (Noun × ℕ)} (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62)
    (r : Noun) : DepthInv r [] (targetsOf preads r) := by
  refine ⟨by simp, fun s hs => ?_⟩
  unfold targetsOf at hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  have hx1 := (List.mem_filter.mp hx).1
  have hpk : isPathAx x.2 = true := (List.mem_filter.mp hx1).2
  have hpr : x ∈ pathReads preads := by unfold pathReads; exact List.mem_dedup.mpr hx1
  have hd := h62 x hpr
  have h1 : 1 ≤ depthOf x.2 := by simpa [isPathAx] using hpk
  refine ⟨fun h => ?_, by simpa using hd⟩
  have : depthOf x.2 = 0 := by simp [depthOf, h]
  omega

theorem walkRows_len_le {cells : List Noun} {preads : List (Noun × ℕ)}
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {t : NTree WN} (ht : t ∈ walkRows cells preads) :
    t.label.bits.length ≤ 61 := by
  obtain ⟨c, hc, hct⟩ := (mem_bfsForest _ t).mp ht
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩
  · obtain ⟨n', bs', T', rfl, hI⟩ := inTree_trie_inv _ DepthInv depthInv_step hct _ _ _ rfl
      ⟨by simp, by simp⟩
    rw [(trie_label _ n' bs' T').2.1]; exact hI.1
  · obtain ⟨n', bs', T', rfl, hI⟩ := inTree_trie_inv _ DepthInv depthInv_step hct _ _ _ rfl
      (targetsOf_depth h62 r)
    rw [(trie_label _ n' bs' T').2.1]; exact hI.1

/-! ## 4. The honest walk gates, from trunk -/

section Gates
variable {K : Type*} [Field K]

/-- The honest `ln` column: `ln i = α^i`. -/
def lnH (α : K) : ℕ → K := fun i => α ^ i
/-- The honest `count` column: `count i = α^kr · α^{Sf fo i}`. -/
def countH (fo : ℕ → ℕ) (α : K) (kr : ℕ) : ℕ → K := fun i => α ^ kr * α ^ Sf fo i
/-- The honest `acc` column: trunk's closed form `accInGate`. -/
noncomputable def accH (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K) (kr : ℕ) : ℕ → K :=
  fun i => accInGate cur chld' fo α (α ^ kr) kr i

/-- **The explicit honest in-gate walk** (the explicit form of trunk `walkSatInGate_exists`): the
columns `lnH`, `countH`, `accH` satisfy every `WalkSatInGate` field at `initial_count = α^kr`. -/
theorem walkSatInGate_explicit (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K) {kr h : ℕ}
    (hh : 1 ≤ h) (hk : 1 ≤ kr) (hle : kr ≤ h) :
    WalkSatInGate cur chld' fo (lnH α) (countH fo α kr) (accH cur chld' fo α kr) α (α ^ kr) kr h := by
  refine
    { hpos := hh
      kpos := hk
      kle := hle
      ln1 := by simp [lnH]
      lnInc := fun i _ _ => by simp only [lnH]; rw [pow_succ]; ring
      count1 := by simp only [countH]; rw [Sf_one]
      countInc := fun i _ _ => by simp only [countH]; rw [Sf_succ, pow_add]; ring
      accInit := ?_
      accStep := ?_ }
  · have hmin : (1 : ℕ) ⊓ kr = 1 := min_eq_left hk
    have hnl : (nodeListP cur 1).eval α = cur 1 * α := by rw [nodeListP_eval]; simp
    have hsum : (∑ i ∈ Finset.Icc 1 1, childSum chld' fo α i) = childSum chld' fo α 1 := by simp
    simp only [accH, accInGate, hmin, hnl, hsum, sub_self, zero_add]
    exact (childSum_scale_init chld' fo α (α ^ kr)).symm
  · intro i hi hih
    have hnl : (nodeListP cur (i + 1)).eval α
        = (nodeListP cur i).eval α + cur (i + 1) * α ^ (i + 1) := by
      rw [nodeListP_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    have hsum : (∑ j ∈ Finset.Icc 1 (i + 1), childSum chld' fo α j)
        = (∑ j ∈ Finset.Icc 1 i, childSum chld' fo α j) + childSum chld' fo α (i + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ i + 1)]
    have hkey : α ^ kr * childSum chld' fo α (i + 1)
        = ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * (α ^ kr * α ^ Sf fo i) * chld' (i + 1) l :=
      (childSum_scale_step chld' fo α (α ^ kr) i).symm
    simp only [lnH, countH, accH]
    by_cases hroot : i + 1 ≤ kr
    · have hdeq : deqCoeff (K := K) kr (i + 1) = 0 := deqCoeff_of_le (K := K) hroot
      have hminN : (i + 1) ⊓ kr = i + 1 := min_eq_left hroot
      have hminC : i ⊓ kr = i := min_eq_left (Nat.le_of_succ_le hroot)
      simp only [accInGate, hminN, hminC, hnl, hsum, hdeq, zero_mul, zero_add]
      linear_combination hkey
    · have hgt : kr < i + 1 := Nat.lt_of_not_ge hroot
      have hdeq : deqCoeff (K := K) kr (i + 1) = 1 := deqCoeff_of_gt (K := K) hgt
      have hminN : (i + 1) ⊓ kr = kr := min_eq_right (Nat.le_of_lt hgt)
      have hminC : i ⊓ kr = kr := min_eq_right (by omega)
      simp only [accInGate, hminN, hminC, hnl, hsum, hdeq, one_mul]
      linear_combination hkey

variable {LT : Type*}

/-- **Honest walk completeness on a BFS forest**: for every
node valuation and every coin `α`, the BFS forest's columns satisfy the in-gate walk at
`initial_count = α^{#roots}` and the terminal accumulator is zero.  Trunk
`bfsForest_isForestFullBFT` → `ForestAccepts` (`forestQueueP_eval`) →
`walkSatInGate_completeness`. -/
theorem honest_walk_acc_zero (nodeVal : NTree LT → K) (l : List (NTree LT)) (hne : l ≠ []) (α : K) :
    WalkSatInGate (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l)) (foCol (bfsForest l))
        (lnH α) (countH (foCol (bfsForest l)) α l.length)
        (accH (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l)) (foCol (bfsForest l)) α
          l.length)
        α (α ^ l.length) l.length (bfsForest l).length ∧
      accH (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l)) (foCol (bfsForest l)) α
        l.length (bfsForest l).length = 0 := by
  have hk : 1 ≤ l.length := List.length_pos_iff.mpr hne
  have hle : l.length ≤ (bfsForest l).length := by
    rw [bfsForest_eq_append_flatMap l hne, List.length_append]; omega
  have hw := walkSatInGate_explicit (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l))
    (foCol (bfsForest l)) α (le_trans hk hle) hk hle
  refine ⟨hw, walkSatInGate_completeness hw ?_⟩
  have hb := congrArg (Polynomial.eval α) (bfsForest_isForestFullBFT nodeVal l hne)
  unfold ForestAccepts
  rw [hb, forestQueueP_eval]

end Gates

/-- **The honest walk table's terminal is zero** at every coin, for every node valuation
(`honest_walk_acc_zero` at `walkForest`). -/
theorem walkRows_acc_zero {K : Type*} [Field K] (cells : List Noun) (preads : List (Noun × ℕ))
    (nodeVal : NTree WN → K) (α : K) :
    accH (curCol nodeVal (walkRows cells preads)) (chldCol nodeVal (walkRows cells preads))
      (foCol (walkRows cells preads)) α (krW cells preads) (walkRows cells preads).length = 0 :=
  (honest_walk_acc_zero nodeVal _ (walkForest_ne_nil cells preads) α).2

/-! ## 5. -/

def qH (kr : ℕ) (fo : ℕ → ℕ) (i : ℕ) : ℕ := kr + Sf fo i - i

theorem walkRows_queue (cells : List Noun) (preads : List (Noun × ℕ)) :
    (∀ i, 1 ≤ i → i < (walkRows cells preads).length →
      1 ≤ qH (krW cells preads) (foCol (walkRows cells preads)) i ∧
        i + qH (krW cells preads) (foCol (walkRows cells preads)) i =
          krW cells preads + Sf (foCol (walkRows cells preads)) i) ∧
      qH (krW cells preads) (foCol (walkRows cells preads)) (walkRows cells preads).length = 0 ∧
      krW cells preads + Sf (foCol (walkRows cells preads)) (walkRows cells preads).length =
        (walkRows cells preads).length ∧
      (∀ i, i ≤ (walkRows cells preads).length →
        krW cells preads + Sf (foCol (walkRows cells preads)) i ≤ (walkRows cells preads).length) := by
  have hne := walkForest_ne_nil cells preads
  have hv : BFSValidF (krW cells preads) (foCol (walkRows cells preads)) (walkRows cells preads).length :=
    foCol_BFSValidF (walkForest cells preads) hne
  have ht : krW cells preads + Sf (foCol (walkRows cells preads)) (walkRows cells preads).length =
      (walkRows cells preads).length := foCol_Sf_tilingF (walkForest cells preads) hne
  have hmono : ∀ i, i ≤ (walkRows cells preads).length →
      Sf (foCol (walkRows cells preads)) i ≤ Sf (foCol (walkRows cells preads)) (walkRows cells preads).length := by
    intro i hi
    unfold Sf
    exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl hi)
  refine ⟨fun i hi hih => ?_, ?_, ht, fun i hi => ?_⟩
  · have := hv (i + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at this
    unfold qH; constructor <;> omega
  · unfold qH; omega
  · have := hmono i hi; omega

/-! ## 6. Reach and root rows -/

/-- Every honest row's node is the subtree of its root at its side bits (`Chain.chainWalk`), and
its prefix is `axisFold` of the bits (`axisFold_append`: child prefix `2p + b`). -/
theorem walkRows_reach {cells : List Noun} {preads : List (Noun × ℕ)} {t : NTree WN}
    (ht : t ∈ walkRows cells preads) :
    chainWalk t.label.root t.label.bits = some t.label.node := by
  obtain ⟨c, hc, hct⟩ := (mem_bfsForest _ t).mp ht
  have step : ∀ (root : Noun) l r bs (T : List (List Bool)) (b : Bool),
      chainWalk root bs = some (Noun.cell l r) → cont b T = true →
      chainWalk root (bs ++ [b]) = some (if b then r else l) := by
    intro root l r bs T b h _
    rw [chainWalk_append, h]
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩
  · obtain ⟨n', bs', T', rfl, hI⟩ := inTree_trie_inv _ (fun n bs _ => chainWalk (cells.headD (.atom 0)) bs = some n)
      (fun l r bs T b h hc => step _ l r bs T b h hc) hct _ _ _ rfl (by simp [chainWalk])
    obtain ⟨h1, h2, h3⟩ := trie_label (cells.headD (.atom 0)) n' bs' T'
    rw [h1, h2, h3]; exact hI
  · obtain ⟨n', bs', T', rfl, hI⟩ := inTree_trie_inv _ (fun n bs _ => chainWalk r bs = some n)
      (fun l r' bs T b h hc => step _ l r' bs T b h hc) hct _ _ _ rfl (by simp [chainWalk])
    obtain ⟨h1, h2, h3⟩ := trie_label r n' bs' T'
    rw [h1, h2, h3]; exact hI

theorem walkRows_root (cells : List Noun) (preads : List (Noun × ℕ)) (i : ℕ)
    (hi : i < krW cells preads) :
    ∃ t, (walkRows cells preads)[i]? = some t ∧ t.label.bits = [] ∧ t.label.node = t.label.root := by
  have hsplit := bfsForest_eq_append_flatMap _ (walkForest_ne_nil cells preads)
  have hil : i < (walkForest cells preads).length := hi
  refine ⟨(walkForest cells preads)[i], ?_, ?_⟩
  · show (bfsForest (walkForest cells preads))[i]? = _
    rw [hsplit, List.getElem?_append_left hil, List.getElem?_eq_getElem hil]
  · rcases mem_walkForest (List.getElem_mem hil) with ⟨-, h⟩ | ⟨r, -, h⟩ <;> rw [h] <;>
      exact ⟨(trie_label _ _ _ _).2.1, (trie_label _ _ _ _).1.trans (trie_label _ _ _ _).2.2.symm⟩

end Nock.NockVMROM.Thm54.VclL.GenWalk
