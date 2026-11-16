import Nock.NockVMROM.Thm54.VclL.Compute.KeysQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1171Thm54C2InductionPositional

/-!
# V4T4 : the tree-node → row lemma, the serial, and `RowFacts.ax0` / `ax9` at `axB0Q7`

.

* **`inTree_buildT_label`** / **`inTree_mapNTree`** — every node of `buildT fo lbl h i` carries a
  label `lbl j`; every node of a `mapNTree f t` is the image of a node of `t`.
* **`treeV_node_row`** — every node of the hCF tree `treeV` (stride-2 carrier) is the label of some
  compute row `r`: `u.label = (rowLabel (envsV r), 2 · rowCarrier (envsV r))` (`at1` always picks a
  row, so no range premise).
* **`serial_eq_row`** — on a trace accepted by the side chip `computeChipVCLQ7S` (adjacent, injective
  nodes) the serial column `220` of row `r` is `r` (`serialInitGate` / `serialStepGate` + the masks);
  **`rowCarrier_eq_row`**: with `V.N ≤ ringChar K` (the verifier's `Checks.hrowsC` gives it) the
  node carrier of row `r` is `r`, so the node label is exactly `2 r`.
* **`rowFacts_ax0_Q7`** / **`rowFacts_ax9_Q7`** — `Batch1171.RowFacts.ax0` / `ax9` at every node of
  `treeV`, at the B0 axis oracle `axB0Q7 V (b0 Q)` and `q = ringChar K`: through `axB0Q7_s0` /
  `axB0Q7_s9` (address `2r+2` / `2r+3` reads row `r`'s `axCol`) and AxGate's `axGates_s0` / `_s9`
  (the gate pins the decoded `f_t.leaf` / `f_th.leaf` to `algebraMap axCol`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module Nock.Walk
open Nock.ComputeTable (State DTcomp fanoutComp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.RecordCarrier
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Nodes of `buildT` and of a `mapNTree` image -/

section nodes

/-- Every node of `buildT fo lbl h i` carries the label of some BFS position. -/
theorem inTree_buildT_label {LT : Type} (fo : ℕ → ℕ) (lbl : ℕ → LT) (h i : ℕ) (u : NTree LT)
    (hu : InTree (buildT fo lbl h i) u) : ∃ j, u.label = lbl j := by
  suffices key : ∀ (c t : NTree LT), InTree c t → ∀ i, c = buildT fo lbl h i → ∃ j, t.label = lbl j from
    key _ _ hu i rfl
  intro c t hct
  induction hct with
  | here c => intro i hc; exact ⟨i, by rw [hc, buildT_label]⟩
  | sub hs _ ih =>
      intro i hc
      rw [hc, buildT] at hs
      simp only [NTree.children_node, List.mem_map] at hs
      obtain ⟨j, -, rfl⟩ := hs
      exact ih j.1 rfl

/-- Every node of `mapNTree f t` is the image of a node of `t`. -/
theorem inTree_mapNTree {A B : Type} (f : A → B) (t : NTree A) (u : NTree B)
    (hu : InTree (mapNTree f t) u) : ∃ v, InTree t v ∧ u.label = f v.label := by
  revert u
  let P := fun t : NTree A => ∀ u, InTree (mapNTree f t) u → ∃ v, InTree t v ∧ u.label = f v.label
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih u hu
    simp only [mapNTree] at hu
    cases hu with
    | here => exact ⟨_, InTree.here _, rfl⟩
    | sub hc hrec =>
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
        obtain ⟨v, hv, hl⟩ := ih c0 hc0 u hrec
        exact ⟨v, InTree.sub hc0 hv, hl⟩
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

end nodes

/-! ## 2. The tree-node → row lemma -/

section tree
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}

/-- **The tree-node → row lemma**: every node of `treeV` is the (stride-2) label of a compute row. -/
theorem treeV_node_row (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (u : NTree ((State × DTcomp K) × ℕ)) (hu : InTree (treeV V chalV pubVal Q) u) :
    ∃ r : Fin V.N, u.label =
      (rowLabel (envsP V chalV pubVal Q r), 2 * rowCarrier (envsP V chalV pubVal Q r)) := by
  obtain ⟨v, hv, hl⟩ := inTree_mapNTree _ _ u hu
  unfold treeV1 computeTree treeOfRows reconTree at hv
  obtain ⟨j, hj⟩ := inTree_buildT_label _ _ _ _ v hv
  refine ⟨if h : j - 1 < V.N then ⟨j - 1, h⟩ else ⟨0, V.hN⟩, ?_⟩
  rw [hl, hj]
  unfold at1
  split_ifs <;> rfl

/-- The patched row's state is the row's (base selectors untouched). -/
theorem rowLabel_envsP_fst (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (r : Fin V.N) : (rowLabel (envsP V chalV pubVal Q r)).1 = (rowLabel (envsV V chalV pubVal Q r)).1 := by
  rw [rowLabel_fst, rowLabel_fst]; rfl

/-- The patched row's `Dec` is the row's (`decodeDec_lnPatch`). -/
theorem rowLabel_envsP_dec (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (r : Fin V.N) :
    (rowLabel (envsP V chalV pubVal Q r)).2.2.2 = (rowLabel (envsV V chalV pubVal Q r)).2.2.2 :=
  decodeDec_lnPatch _

theorem rowCarrier_envsP (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (r : Fin V.N) : rowCarrier (envsP V chalV pubVal Q r) = rowCarrier (envsV V chalV pubVal Q r) := rfl

end tree

/-! ## 3. The serial and the node carrier -/

section serial
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hC : ℕ} {S : MemShape}

/-- **The serial of an accepted side-chip trace**: column `220` of row `r` is `r`. -/
theorem serial_eq_row (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (Q : Fin 232 → F[X]) (hadj : V.AdjacentC) (hinj : Function.Injective V.computeNodes)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (r : Fin V.N) : (rawEnvQ7 V chalV pubVal Q r).trace serialCol = (r : F) := by
  have hs := (computeChipVCLQ7S_sat_iff V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC Q).1 hsat
  have hmem : ∀ i : Fin V.N, V.computeNodes i ∈ rowNodeSet V.computeNodes := fun i => by
    simp [rowNodeSet]
  have hgate : ∀ i : Fin V.N, ∀ g ∈ serialGates (F := F), g.eval (rawEnvQ7 V chalV pubVal Q i) = 0 :=
    fun i g hg => hs.2 _ (hmem i) g (by
      simp only [vclGatesQ7S, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hg)))))
  have h11 : (11 : ℕ) < 232 := by norm_num
  have h12 : (12 : ℕ) < 232 := by norm_num
  have m0 : Q ⟨11, h11⟩ = firstRowMask V.computeNodes := hs.1 ⟨0, by change 0 < 2; norm_num⟩
  have m1 : Q ⟨12, h12⟩ = lastRowMask V.hN V.computeNodes := hs.1 ⟨1, by change 1 < 2; norm_num⟩
  have mask0 : ∀ i : Fin V.N, (rawEnvQ7 V chalV pubVal Q i).trace 11 = if (i : ℕ) = 0 then 1 else 0 := by
    intro i
    simp only [rawEnvQ7, envOfTrace, dif_pos h11]
    rw [m0, Nock.Framework.firstRowMask_eval _ hinj]
  have mask1 : ∀ i : Fin V.N, (rawEnvQ7 V chalV pubVal Q i).trace 12 =
      if (i : ℕ) = V.N - 1 then 1 else 0 := by
    intro i
    simp only [rawEnvQ7, envOfTrace, dif_pos h12]
    rw [m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]
  have hnext : ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
      (rawEnvQ7 V chalV pubVal Q i).traceNext serialCol =
        (rawEnvQ7 V chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace serialCol := by
    intro i hi
    have ha := hadj i hi
    simp only [rawEnvQ7, envOfTrace]
    split_ifs
    · rw [ha]
    · rfl
  obtain ⟨r, hr⟩ := r
  induction r with
  | zero =>
      have := (serialInitGate_eval _).1 (hgate ⟨0, hr⟩ _ (by simp [serialGates]))
      rw [mask0] at this
      simpa using this
  | succ k ih =>
      have hk : k < V.N := by omega
      have hstep := (serialStepGate_eval _).1 (hgate ⟨k, hk⟩ _ (by simp [serialGates]))
      rw [mask1] at hstep
      have hne : ¬ (k = V.N - 1) := by omega
      simp only [hne, if_false] at hstep
      rcases hstep with h | h
      · exact absurd h zero_ne_one
      · rw [hnext ⟨k, hk⟩ hr] at h
        rw [h, ih hk]; push_cast; ring

/-- **The node carrier of row `r` is `r`** (below the characteristic). -/
theorem rowCarrier_eq_row [DecidableEq F] (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (Q : Fin 232 → F[X]) (hadj : V.AdjacentC) (hinj : Function.Injective V.computeNodes)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (hNp : V.N ≤ ringChar K) (r : Fin V.N) :
    rowCarrier (envsV V chalV pubVal Q r) = r := by
  unfold rowCarrier
  rw [envsV_expCol]
  have h := serial_eq_row V γc ρc chalV pubVal Q hadj hinj hsat r
  have he : (Q ⟨220, by norm_num⟩).eval (V.computeNodes r) = (r : F) := by
    rw [← h]; simp [rawEnvQ7, envOfTrace, serialCol]
  rw [he, map_natCast]
  exact natLift_natCast (by omega)

end serial

/-! ## 4. `RowFacts.ax0` / `ax9` at `axB0Q7` -/

section ax
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq F] [DecidableEq K] [CharP K (ringChar K)] {hC : ℕ} {S : MemShape}

/-- At a row with `SelAt envF st`, the decoded state of its gathered pull-back is `st`. -/
theorem stateOfBase_selAt (envF : Env F) (st : State) (hs : SelAt envF st) :
    stateOfBase (fun k => if h : k < 13 then envF.trace k else 0) = st := by
  have hv : ∀ i (hi : i < 11), envF.trace i = _ := fun i hi => hs i hi
  cases st <;>
    simp [stateOfBase, hv 1 (by norm_num), hv 2 (by norm_num), hv 3 (by norm_num), hv 4 (by norm_num),
      hv 5 (by norm_num), hv 6 (by norm_num), hv 7 (by norm_num), hv 8 (by norm_num),
      hv 9 (by norm_num), hv 10 (by norm_num)]

/-- The row facts the two axis clauses need, per row of an accepted side-chip trace. -/
theorem row_ax_facts (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (r : Fin V.N) :
    ∃ st, SelAt (rawEnvQ7 V chalV pubVal Q r) st ∧
      (rowLabel (envsV V chalV pubVal Q r)).1 = st ∧
      ∀ g ∈ axGates V.basis, g.eval (rawEnvQ7 V chalV pubVal Q r) = 0 := by
  have hs := (computeChipVCLQ7S_sat_iff V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC Q).1 hsat
  have hg : ∀ g ∈ vclGatesQ7S V.N V.basis γc ρc, g.eval (rawEnvQ7 V chalV pubVal Q r) = 0 :=
    hs.2 _ (by simp [rowNodeSet])
  obtain ⟨st, hst⟩ := selAt_of_gatesQ7S V.N V.basis γc ρc _ hg hchar
  refine ⟨st, hst, ?_, fun g hgm => hg g (by
    simp only [vclGatesQ7S, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hgm))))⟩
  rw [rowLabel_fst, ← stateOfBase_selAt _ st hst]
  congr 1; funext k
  split_ifs with hk
  · rw [envsV_base V chalV pubVal Q r k hk]; simp [rawEnvQ7, envOfTrace, show k < 232 by omega]
  · rfl

/-- The decoded `f_t.leaf` / `f_th.leaf` of a row's gathered pull-back read the raw row (limbs
`136..138` / `145..147` are below `202`). -/
theorem envsV_ft_leaf (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (r : Fin V.N) :
    (StrategyOfTracesLift.decodeDec (envsV V chalV pubVal Q r)).f_t.leaf =
      (gatherCorrectedFinalTypedEnv V.basis (rawEnvQ7 V chalV pubVal Q r)).extTrace ⟨41, by omega⟩ := by
  rw [decodeDec_ft_leaf]; unfold envsV; rw [gather_ext41, gather_ext41]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pullEnv_trace_lt _ _ (by fin_cases k <;> decide)]; rfl

theorem envsV_fth_leaf (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (r : Fin V.N) :
    (StrategyOfTracesLift.decodeDec (envsV V chalV pubVal Q r)).f_th.leaf =
      (gatherCorrectedFinalTypedEnv V.basis (rawEnvQ7 V chalV pubVal Q r)).extTrace ⟨44, by omega⟩ := by
  rw [decodeDec_fth_leaf]; unfold envsV; rw [gather_ext44, gather_ext44]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pullEnv_trace_lt _ _ (by fin_cases k <;> decide)]; rfl

variable (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
  (hadj : V.AdjacentC) (hinj : Function.Injective V.computeNodes)
  (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
  (hsat : RAP.SatisfiesWithPreprocessing
    (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
  (hNp : V.N ≤ ringChar K)

include hadj hinj hchar hsat hNp in
/-- **`RowFacts.ax0` at `axB0Q7`**, every node of `treeV` (`q = ringChar K`). -/
theorem rowFacts_ax0_Q7 (u : NTree ((State × DTcomp K) × ℕ)) (hu : InTree (treeV V chalV pubVal Q) u) :
    u.label.1.1 = .s0 →
      (∀ n : ℕ, n < ringChar K → u.label.1.2.2.2.f_t.leaf = (n : K) →
          axB0Q7 V (b0 (T := tableVCLE hC) Q) (u.label.2 + 2) = n) ∧
        axB0Q7 V (b0 (T := tableVCLE hC) Q) (u.label.2 + 2) < ringChar K := by
  intro hs0
  obtain ⟨r, hr⟩ := treeV_node_row V chalV pubVal Q u hu
  obtain ⟨st, hsel, hst, hax⟩ := row_ax_facts V γc ρc chalV pubVal Q hchar hsat r
  have hcar := rowCarrier_eq_row V γc ρc chalV pubVal Q hadj hinj hsat hNp r
  rw [hr] at hs0 ⊢
  simp only at hs0 ⊢
  rw [rowLabel_envsP_fst] at hs0
  rw [rowCarrier_envsP, hcar, axB0Q7_s0, b0NatAt_row (T := tableVCLE hC) V chalV pubVal Q r]
  have hst0 : st = .s0 := hst ▸ hs0
  subst hst0
  have h0 : (rawEnvQ7 V chalV pubVal Q r).trace 0 = 1 := by simpa using hsel 0 (by norm_num)
  have h9 : (rawEnvQ7 V chalV pubVal Q r).trace 9 = 0 := by simpa using hsel 9 (by norm_num)
  have hK := axGates_s0 V.basis _ hax h0 h9
  refine ⟨fun n hn hleaf => ?_, natLift_lt (CharP.ringChar_ne_zero_of_finite K |>.bot_lt) _⟩
  have hleaf' : (rowLabel (envsV V chalV pubVal Q r)).2.2.2.f_t.leaf = (n : K) := by
    rw [← rowLabel_envsP_dec]; exact hleaf
  change (StrategyOfTracesLift.decodeDec (envsV V chalV pubVal Q r)).f_t.leaf = (n : K) at hleaf'
  rw [envsV_ft_leaf, hK] at hleaf'
  exact (congrArg natLift hleaf').trans (natLift_natCast hn)

include hadj hinj hchar hsat hNp in
/-- **`RowFacts.ax9` at `axB0Q7`**, every node of `treeV`. -/
theorem rowFacts_ax9_Q7 (u : NTree ((State × DTcomp K) × ℕ)) (hu : InTree (treeV V chalV pubVal Q) u) :
    u.label.1.1 = .s9 →
      (∀ n : ℕ, n < ringChar K → u.label.1.2.2.2.f_th.leaf = (n : K) →
          axB0Q7 V (b0 (T := tableVCLE hC) Q) (u.label.2 + 3) = n) ∧
        axB0Q7 V (b0 (T := tableVCLE hC) Q) (u.label.2 + 3) < ringChar K := by
  intro hs9
  obtain ⟨r, hr⟩ := treeV_node_row V chalV pubVal Q u hu
  obtain ⟨st, hsel, hst, hax⟩ := row_ax_facts V γc ρc chalV pubVal Q hchar hsat r
  have hcar := rowCarrier_eq_row V γc ρc chalV pubVal Q hadj hinj hsat hNp r
  rw [hr] at hs9 ⊢
  simp only at hs9 ⊢
  rw [rowLabel_envsP_fst] at hs9
  rw [rowCarrier_envsP, hcar, axB0Q7_s9, b0NatAt_row (T := tableVCLE hC) V chalV pubVal Q r]
  have hst9 : st = .s9 := hst ▸ hs9
  subst hst9
  have h0 : (rawEnvQ7 V chalV pubVal Q r).trace 0 = 0 := by simpa using hsel 0 (by norm_num)
  have h9 : (rawEnvQ7 V chalV pubVal Q r).trace 9 = 1 := by simpa using hsel 9 (by norm_num)
  have hK := axGates_s9 V.basis _ hax h0 h9
  refine ⟨fun n hn hleaf => ?_, natLift_lt (CharP.ringChar_ne_zero_of_finite K |>.bot_lt) _⟩
  have hleaf' : (rowLabel (envsV V chalV pubVal Q r)).2.2.2.f_th.leaf = (n : K) := by
    rw [← rowLabel_envsP_dec]; exact hleaf
  change (StrategyOfTracesLift.decodeDec (envsV V chalV pubVal Q r)).f_th.leaf = (n : K) at hleaf'
  rw [envsV_fth_leaf, hK] at hleaf'
  exact (congrArg natLift hleaf').trans (natLift_natCast hn)

include hadj hinj hchar hsat hNp in
/-- **Every node label of `treeV` is `2 r` for the row it decodes** (the carrier is the doubled row
index; `stride2_disjoint` then separates the oracle addresses of any two nodes). -/
theorem treeV_label_row (u : NTree ((State × DTcomp K) × ℕ)) (hu : InTree (treeV V chalV pubVal Q) u) :
    ∃ r : Fin V.N, u.label.1 = rowLabel (envsP V chalV pubVal Q r) ∧ u.label.2 = 2 * (r : ℕ) := by
  obtain ⟨r, hr⟩ := treeV_node_row V chalV pubVal Q u hu
  refine ⟨r, by rw [hr], ?_⟩
  rw [hr, rowCarrier_envsP, rowCarrier_eq_row V γc ρc chalV pubVal Q hadj hinj hsat hNp r]

include hadj hinj hchar hsat hNp in
/-- **`RowFacts` at `ax := axB0Q7`** (the frame's `rowFactsAt` shape at one node), from the five
carrier-free core facts (`Batch1111.rowFacts_core_ev`'s conclusion shape; NOT proved here for VCL):
the two axis clauses are `rowFacts_ax0_Q7` / `rowFacts_ax9_Q7`. -/
theorem rowFacts_Q7_of_core (z : K) (u : NTree ((State × DTcomp K) × ℕ))
    (hu : InTree (treeV V chalV pubVal Q) u)
    (hcore : u.label.1.2.2.1.state = u.label.1.1 ∧ u.label.1.2.1.z = z ∧
      Nock.ComputeTable.Vcomp u.label.1.2.1 u.label.1.2.2.1 u.label.1.2.2.2 ∧
      u.children.length = fanoutComp u.label.1.1 ∧
      ∀ (k : Fin 3) (c : NTree ((State × DTcomp K) × ℕ)), u.children[(k : ℕ)]? = some c →
        (c.label.1.2.2.1.s, c.label.1.2.2.1.f, c.label.1.2.2.1.e) =
          Nock.ComputeTable.sfTriple u.label.1.2.2.1 k) :
    Nock.RedTeam.Batch1171.RowFacts (ax := axB0Q7 V (b0 (T := tableVCLE hC) Q)) z (ringChar K) u :=
  ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2,
    rowFacts_ax0_Q7 V γc ρc chalV pubVal Q hadj hinj hchar hsat hNp u hu,
    rowFacts_ax9_Q7 V γc ρc chalV pubVal Q hadj hinj hchar hsat hNp u hu⟩

end ax

end

end VclL.Compute
end Nock.NockVMROM.Thm54
