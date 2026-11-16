/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemHonest.lean

Part 1: `poleSummand` — a bad summand whose event is "the IO coins `(γ′, ρ′)` hit a pole of one of a list of
  honest records" (`compress ⟨γ′, ρ′⟩ v = 0`), priced `|recs| · |𝕂′|` over `|𝕂′|` pairs; its membership
  characterisation `poleSummand_mem`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundVCL
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemAccept
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemGenPath
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JointSummands

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.PathModel
open Module
open scoped Polynomial

noncomputable section

section Pole
variable {Φ : CoinFrame} {K Kio : Type} [Field K] [Fintype K] [DecidableEq K] [Field Kio] [Fintype Kio]
  [DecidableEq Kio]

open Classical in
/-- The `(γ, ρ)` pairs at which some record of `recs` has a zero denominator. -/
def poleBad {m : ℕ} (recs : List (Fin m → Kio)) : Finset (Kio × Kio) :=
  Finset.univ.filter fun q => ∃ v ∈ recs, FiniteIO.compress (m := m) ⟨q.1, q.2⟩ v = 0

theorem poleBad_card_le {m : ℕ} (recs : List (Fin m → Kio)) :
    (poleBad recs).card ≤ recs.length * Fintype.card Kio := by
  classical
  have hsub : poleBad recs ⊆ recs.toFinset.biUnion fun v =>
      (Finset.univ : Finset Kio).image fun γ => (γ, -(FiniteIO.compress (m := m) ⟨γ, 0⟩ v)) := by
    intro q hq
    simp only [poleBad, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨v, hv, h0⟩ := hq
    simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨v, hv, q.1, ?_⟩
    have : q.2 = -(FiniteIO.compress (m := m) ⟨q.1, 0⟩ v) := by
      have h1 : FiniteIO.compress (m := m) ⟨q.1, q.2⟩ v = q.2 + FiniteIO.compress (m := m) ⟨q.1, 0⟩ v := by
        simp [FiniteIO.compress]
      rw [h1] at h0
      exact eq_neg_of_add_eq_zero_left h0
    exact Prod.ext rfl this.symm
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ v ∈ recs.toFinset, ((Finset.univ : Finset Kio).image
        fun γ => (γ, -(FiniteIO.compress (m := m) ⟨γ, 0⟩ v))).card
      ≤ ∑ _v ∈ recs.toFinset, Fintype.card Kio :=
        Finset.sum_le_sum fun v _ => (Finset.card_image_le).trans (by simp)
    _ = recs.toFinset.card * Fintype.card Kio := by simp
    _ ≤ recs.length * Fintype.card Kio := Nat.mul_le_mul_right _ (List.toFinset_card_le _)

variable {F : Type} [Field F] {C : TableSpec} {S : MemShape}

open Classical in
/-- **A pole summand**: the IO coins hit a pole of one of the records `recs χ`, which read only the coins
`dep` (disjoint from the IO coins). -/
def poleSummand (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hd : Disjoint I.dep dep) {m : ℕ}
    (len : ℕ) (recs : Coins Φ K → List (Fin m → Kio)) (hlen : ∀ χ, (recs χ).length ≤ len)
    (hreads : ReadsOnC Φ dep recs) :
    BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) where
  coins := I.dep
  dep := dep
  disj := hd
  badSet _ χ := Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs χ)
  weight := len * Fintype.card Kio
  card_le _ χ := by
    refine le_trans (Finset.card_le_card_of_injOn (fun v => I.pair (extIO I v)) ?_ ?_)
      ((poleBad_card_le (recs χ)).trans (Nat.mul_le_mul_right _ (hlen χ)))
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj I h
  readsOn _ _ χ χ' hdep := by
    show (Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs χ)) =
      Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs χ')
    rw [hreads χ χ' hdep]

theorem poleSummand_mem (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hd : Disjoint I.dep dep)
    {m : ℕ} (len : ℕ) (recs : Coins Φ K → List (Fin m → Kio)) (hlen : ∀ χ, (recs χ).length ≤ len)
    (hreads : ReadsOnC Φ dep recs) (tr : Traces F C S) (χ : Coins Φ K) :
    (poleSummand (F := F) (C := C) (S := S) I dep hd len recs hlen hreads).mem tr χ ↔
      I.pair χ ∈ poleBad (recs χ) := by
  classical
  unfold BadSummand.mem
  show (fun i : I.dep => χ i) ∈
      (Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs χ)) ↔ _
  rw [Finset.mem_filter, pair_extIO]
  simp

end Pole

/-! ## 2. The honest datum -/

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP : ℕ) (hC : ℕ)

/-- **The honest datum of the VCL-L memory family**: a verifier datum `V` whose memory tables are exactly
the generator's (`d.cells` rows, the chains of the distinct deep reads of `d`), with the public numeric facts
`GoodM` reads (Goldilocks-type: `2^63 < p`, `rows + 1 < p`, prime-field elements) and the adjacency /
injectivity of the nodes (`V.Checks.hadjM`, `memNodes_injective`). -/
structure HonestVCL where
  V : VerifierData F K hC (shapeV hT hP)
  d : Demand
  hF : GeneratedField.PrimeFieldElems F
  hq : 2 ^ 63 < ringChar F
  hrows : ∀ t, V.memRows t + 1 < ringChar F
  hadj : ∀ t, V.AdjacentM t
  hinj : ∀ t, Function.Injective (V.memNodes t)
  hrank : ∀ n ∈ d.cells, rankOf n < 2 ^ 110
  h62 : ∀ r ∈ pathReads d.preads, depthOf r.2 ≤ 62
  hC0 : V.memRows (tC hT hP) = d.cells.length
  hP0 : V.memRows (tP hT hP) = (pathTableP δF (0 : Quad (algebraMap F K δF)) d.cells d.preads).length

variable {δF hT hP hC}

/-- The seed `z′ = χ₂ + χ₃√δ` of the coins. -/
def zC (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  Quad.mk _ (χ ⟨2, by decide⟩) (χ ⟨3, by decide⟩)
/-- `γ′ = χ₄ + χ₆√δ`. -/
def γC (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  Quad.mk _ (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩)
/-- `ρ′ = χ₅ + χ₇√δ`. -/
def ρC (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  Quad.mk _ (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)

namespace HonestVCL
variable (H : HonestVCL (K := K) δF hT hP hC)

/-- The generated cell rows at the seed `z` (before the fill). -/
def cellRows (z : Quad (algebraMap F K δF)) : ℕ → CellVals F (Quad (algebraMap F K δF)) :=
  cellRows0 δF z H.d.cells (vcsOf H.d.cells []) (xs0P H.d.cells H.d.preads H.d.reads) (xs1P H.d.cells H.d.preads H.d.reads)

/-- The generated path rows at the seed `z` (before the fill). -/
def pathRows (z : Quad (algebraMap F K δF)) : ℕ → PathVals F (Quad (algebraMap F K δF)) :=
  fun j => (pathTableP δF z H.d.cells H.d.preads).getD j (chainRow δF z H.d.cells (.atom 0) 0 [] 0)

/-- The accumulator terminals: validity `Σ vTerm`, export `Σ xTerm`, path-consume `Σ xConsInv`, path-provide
`Σ m·pProvInv`. -/
def vTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tC hT hP)),
    vTermOf δF (cellFillInv δF (γC χ) (ρC χ) (H.cellRows (zC χ) k))
def xTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tC hT hP)),
    xTermOf δF (cellFillInv δF (γC χ) (ρC χ) (H.cellRows (zC χ) k))
def yTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tP hT hP)),
    (pathFillInv δF (γC χ) (ρC χ) (H.pathRows (zC χ) k)).xConsInv
def pTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tP hT hP)),
    liftQ δF (H.pathRows (zC χ) k).m * (pathFillInv δF (γC χ) (ρC χ) (H.pathRows (zC χ) k)).pProvInv

/-- **`honestReq`**: the three request sums the chips' publics fix. -/
def req (χ : Coins frameVCL K) : Fin 3 → Quad (algebraMap F K δF)
  | 0 => H.vTot χ
  | 1 => H.xTot χ - H.yTot χ
  | 2 => H.pTot χ

/-- **`honestMsg2`**: the path chip's export-consume total `y`. -/
def msg2 (χ : Coins frameVCL K) : Quad (algebraMap F K δF) := H.yTot χ

/-- The honest column function of table `t`. -/
def col (χ : Coins frameVCL K) (t : Fin (shapeV hT hP).k) :
    ℕ → Fin (H.V.memRows t) → F :=
  fun j i =>
    if (t : ℕ) = 0 then
      cellCol δF H.V.basis (fun i' : Fin (H.V.memRows t) =>
        cellFill δF (γC χ) (ρC χ) (H.cellRows (zC χ)) i') j i
    else
      pathCol δF H.V.basis (fun i' : Fin (H.V.memRows t) =>
        pathFill δF (γC χ) (ρC χ) (H.pathRows (zC χ)) i') j i

/-- **`honestQ`**: the interpolated honest trace. -/
def trace (χ : Coins frameVCL K) (t : Fin (shapeV hT hP).k) :
    Fin ((shapeV hT hP).table t).width → F[X] :=
  honestQ (H.V.hM t) (H.V.memNodes t) (H.col χ t) ((shapeV hT hP).table t).width

end HonestVCL

end Honest

/-! ## 3. Stagedness -/

section Staged
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP hC : ℕ}

theorem sampledAfter_seed (i : Fin frameVCL.n) (hi : (i : ℕ) = 2 ∨ (i : ℕ) = 3) :
    frameVCL.sampledAfter i = 0 := by
  rcases i with ⟨i, hi'⟩
  simp only at hi
  rcases hi with rfl | rfl <;> rfl

theorem sampledAfter_io (i : Fin frameVCL.n) (hi : (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) :
    frameVCL.sampledAfter i = 1 := by
  rcases i with ⟨i, hi'⟩
  simp only at hi
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem zC_congr (χ χ' : Coins frameVCL K) {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < r → χ i = χ' i) :
    zC (δF := δF) χ = zC χ' := by
  unfold zC
  rw [h ⟨2, by decide⟩ (by rw [sampledAfter_seed ⟨2, by decide⟩ (Or.inl rfl)]; omega),
    h ⟨3, by decide⟩ (by rw [sampledAfter_seed ⟨3, by decide⟩ (Or.inr rfl)]; omega)]

theorem γC_congr (χ χ' : Coins frameVCL K) {r : ℕ} (hr : 2 ≤ r)
    (h : ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < r → χ i = χ' i) :
    γC (δF := δF) χ = γC χ' := by
  unfold γC
  rw [h ⟨4, by decide⟩ (by rw [sampledAfter_io ⟨4, by decide⟩ (Or.inl rfl)]; omega),
    h ⟨6, by decide⟩ (by rw [sampledAfter_io ⟨6, by decide⟩ (by simp)]; omega)]

theorem ρC_congr (χ χ' : Coins frameVCL K) {r : ℕ} (hr : 2 ≤ r)
    (h : ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < r → χ i = χ' i) :
    ρC (δF := δF) χ = ρC χ' := by
  unfold ρC
  rw [h ⟨5, by decide⟩ (by rw [sampledAfter_io ⟨5, by decide⟩ (by simp)]; omega),
    h ⟨7, by decide⟩ (by rw [sampledAfter_io ⟨7, by decide⟩ (by simp)]; omega)]

theorem table_zero_round (t : Fin (shapeV hT hP).k) (ht : (t : ℕ) = 0)
    (j : Fin ((shapeV hT hP).table t).width) :
    ∃ hj : (j : ℕ) < 225, ((shapeV hT hP).table t).colRound j = Chips.Cell.colRoundT ⟨j, hj⟩ := by
  obtain rfl : t = tC hT hP := Fin.ext ht
  exact ⟨j.2, rfl⟩

theorem table_one_round (t : Fin (shapeV hT hP).k) (ht : (t : ℕ) ≠ 0)
    (j : Fin ((shapeV hT hP).table t).width) :
    ∃ hj : (j : ℕ) < 112, ((shapeV hT hP).table t).colRound j = Chips.Path.colRoundT ⟨j, hj⟩ := by
  have h2 : (t : ℕ) < 2 := t.2
  obtain rfl : t = tP hT hP := Fin.ext (show (t : ℕ) = 1 by omega)
  exact ⟨j.2, rfl⟩

end Staged

section ColIndep
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

theorem cellRows0_base_indep (z z' : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun) (j k : ℕ) :
    (cellRows0 δF z cells vcs xs0 xs1 j).base k = (cellRows0 δF z' cells vcs xs0 xs1 j).base k := by
  rfl

theorem cellFill_base_indep (γ ρ γ' ρ' : Quad (algebraMap F K δF))
    (rows rows' : ℕ → CellVals F (Quad (algebraMap F K δF)))
    (hb : ∀ i k, (rows i).base k = (rows' i).base k) (i k : ℕ) :
    (cellFill δF γ ρ rows i).base k = (cellFill δF γ' ρ' rows' i).base k := by
  have := hb i k
  unfold CellVals.base at this ⊢
  exact this

theorem cellFill_qslot_lt9 (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → CellVals F (Quad (algebraMap F K δF)))
    (i s : ℕ) (hs : s < 9) : (cellFill δF γ ρ rows i).qslot s = (rows i).qslot s := by
  interval_cases s <;> rfl

theorem cellCol_round1 (γ ρ γ' ρ' : Quad (algebraMap F K δF))
    (rows rows' : ℕ → CellVals F (Quad (algebraMap F K δF)))
    (j : ℕ) (hb : ∀ i k, (rows i).base k = (rows' i).base k)
    (hq : 129 ≤ j → ∀ i s, s < 9 → (rows i).qslot s = (rows' i).qslot s) {n : ℕ} (i : Fin n) (hj : j < 183) :
    cellCol δF b (fun i' : Fin n => cellFill δF γ ρ rows i') j i =
      cellCol δF b (fun i' : Fin n => cellFill δF γ' ρ' rows' i') j i := by
  unfold cellCol
  by_cases h : j < 129
  · simp only [h, if_true]; exact cellFill_base_indep γ ρ γ' ρ' rows rows' hb i j
  · simp only [h, if_false]
    congr 1
    unfold roleVal
    have hs : ((j - 129) / 3) / 2 < 9 := by omega
    rw [cellFill_qslot_lt9 γ ρ rows i _ hs, cellFill_qslot_lt9 γ' ρ' rows' i _ hs, hq (by omega) i _ hs]

theorem chainRow_base_indep (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (root : Noun) (mult : ℕ)
    (steps : List (Noun × Bool)) (k j : ℕ) :
    (chainRow δF z cells root mult steps k).base j = (chainRow δF z' cells root mult steps k).base j := rfl

theorem pathTable_map_base (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (reads : List (Noun × ℕ))
    (k : ℕ) :
    (pathTable δF z cells reads).map (fun x => x.base k) = (pathTable δF z' cells reads).map (fun x => x.base k) := by
  unfold pathTable
  rw [List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun r _ => ?_
  unfold chainRows
  simp only [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact chainRow_base_indep z z' _ _ _ _ i k

theorem pathRows_base_indep (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (reads : List (Noun × ℕ))
    (j k : ℕ) :
    ((pathTable δF z cells reads).getD j (chainRow δF z cells (.atom 0) 0 [] 0)).base k =
      ((pathTable δF z' cells reads).getD j (chainRow δF z' cells (.atom 0) 0 [] 0)).base k := by
  have hm := pathTable_map_base z z' cells reads k
  have hlen : (pathTable δF z cells reads).length = (pathTable δF z' cells reads).length := by
    simpa using congrArg List.length hm
  by_cases hj : j < (pathTable δF z cells reads).length
  · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (hlen ▸ hj)]
    have := congrArg (fun l => l[j]?) hm
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (hlen ▸ hj)] at this
    simpa using this
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rfl

theorem chainRows_map_base (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (root : Noun) (mult : ℕ)
    (steps : List (Noun × Bool)) (k : ℕ) :
    (chainRows δF z cells root mult steps).map (fun x => x.base k) =
      (chainRows δF z' cells root mult steps).map (fun x => x.base k) := by
  unfold chainRows
  simp only [List.map_map]
  exact List.map_congr_left fun i _ => chainRow_base_indep z z' _ _ _ _ i k

theorem pathTableP_map_base (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (reads : List (Noun × ℕ))
    (k : ℕ) :
    (pathTableP δF z cells reads).map (fun x => x.base k) = (pathTableP δF z' cells reads).map (fun x => x.base k) := by
  unfold pathTableP
  rw [List.map_append, List.map_append, pathTable_map_base z z' cells reads k,
    chainRows_map_base z z' cells _ _ _ k]

theorem pathRowsP_base_indep (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (reads : List (Noun × ℕ))
    (j k : ℕ) :
    ((pathTableP δF z cells reads).getD j (chainRow δF z cells (.atom 0) 0 [] 0)).base k =
      ((pathTableP δF z' cells reads).getD j (chainRow δF z' cells (.atom 0) 0 [] 0)).base k := by
  have hm := pathTableP_map_base z z' cells reads k
  have hlen : (pathTableP δF z cells reads).length = (pathTableP δF z' cells reads).length := by
    simpa using congrArg List.length hm
  by_cases hj : j < (pathTableP δF z cells reads).length
  · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (hlen ▸ hj)]
    have := congrArg (fun l => l[j]?) hm
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (hlen ▸ hj)] at this
    simpa using this
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rfl

end ColIndep

section PathColIndep
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

theorem pathFill_base_indep (γ ρ γ' ρ' : Quad (algebraMap F K δF))
    (rows rows' : ℕ → PathVals F (Quad (algebraMap F K δF)))
    (hb : ∀ i k, (rows i).base k = (rows' i).base k) (i k : ℕ) :
    (pathFill δF γ ρ rows i).base k = (pathFill δF γ' ρ' rows' i).base k := by
  have := hb i k
  unfold PathVals.base at this ⊢
  exact this

theorem pathFill_qslot_lt12 (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → PathVals F (Quad (algebraMap F K δF)))
    (i s : ℕ) (hs : s < 12) : (pathFill δF γ ρ rows i).qslot s = (rows i).qslot s := by
  interval_cases s <;> rfl

theorem pathCol_round1 (γ ρ γ' ρ' : Quad (algebraMap F K δF))
    (rows rows' : ℕ → PathVals F (Quad (algebraMap F K δF)))
    (j : ℕ) (hb : ∀ i k, (rows i).base k = (rows' i).base k)
    (hq : 16 ≤ j → ∀ i s, s < 12 → (rows i).qslot s = (rows' i).qslot s) {n : ℕ} (i : Fin n)
    (hj : j < 88) :
    pathCol δF b (fun i' : Fin n => pathFill δF γ ρ rows i') j i =
      pathCol δF b (fun i' : Fin n => pathFill δF γ' ρ' rows' i') j i := by
  unfold pathCol
  by_cases h : j < 16
  · simp only [h, if_true]; exact pathFill_base_indep γ ρ γ' ρ' rows rows' hb i j
  · simp only [h, if_false]
    congr 1
    unfold proleVal
    have hs : ((j - 16) / 3) / 2 < 12 := by omega
    rw [pathFill_qslot_lt12 γ ρ rows i _ hs, pathFill_qslot_lt12 γ' ρ' rows' i _ hs, hq (by omega) i _ hs]

end PathColIndep

section StagedMain
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP hC : ℕ} (H : HonestVCL (K := K) δF hT hP hC)

theorem cell_round_lower (j : Fin Chips.Cell.widthT) :
    (129 ≤ (j : ℕ) → 1 ≤ Chips.Cell.colRoundT j) ∧ (183 ≤ (j : ℕ) → 2 ≤ Chips.Cell.colRoundT j) := by
  simp only [Chips.Cell.colRoundT, show Chips.Cell.b0CountS = 129 from rfl,
    show Chips.Cell.b1Count = 54 from rfl]
  split_ifs <;> omega

theorem path_round_lower (j : Fin Chips.Path.widthT) :
    (16 ≤ (j : ℕ) → 1 ≤ Chips.Path.colRoundT j) ∧ (88 ≤ (j : ℕ) → 2 ≤ Chips.Path.colRoundT j) := by
  simp only [Chips.Path.colRoundT, show Chips.Path.b0Count = 16 from rfl,
    show Chips.Path.b1Count = 72 from rfl]
  split_ifs <;> omega

/-- **`honest_staged`.** -/
theorem trace_staged (t : Fin (shapeV hT hP).k) :
    StagedCols frameVCL ((shapeV hT hP).table t).colRound (fun χ => H.trace χ t) := by
  intro j χ χ' h
  unfold HonestVCL.trace
  refine honestQ_congr (H.V.hM t) (H.V.memNodes t) (H.col χ t) (H.col χ' t) _ j ?_
  funext i
  have hb := H.V.basis
  by_cases ht : (t : ℕ) = 0
  · obtain ⟨hj, hr⟩ := table_zero_round t ht j
    have hlow := cell_round_lower ⟨j, hj⟩
    rw [← hr] at hlow
    simp only [HonestVCL.col, ht, if_true]
    by_cases h2 : 183 ≤ (j : ℕ)
    · have hr2 := hlow.2 h2
      have hz := zC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j) (by omega) h
      have hγ := γC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j) (by omega) h
      have hρ := ρC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j) (by omega) h
      rw [hz, hγ, hρ]
    · refine cellCol_round1 H.V.basis _ _ _ _ _ _ j (fun i k => cellRows0_base_indep _ _ _ _ _ _ i k)
        (fun h1 i s _ => ?_) i (by omega)
      have hz := zC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j)
        (hlow.1 h1) h
      show (H.cellRows (zC χ) i).qslot s = (H.cellRows (zC χ') i).qslot s
      rw [hz]
  · obtain ⟨hj, hr⟩ := table_one_round t ht j
    have hlow := path_round_lower ⟨j, hj⟩
    rw [← hr] at hlow
    simp only [HonestVCL.col, ht, if_false]
    by_cases h2 : 88 ≤ (j : ℕ)
    · have hr2 := hlow.2 h2
      have hz := zC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j) (by omega) h
      have hγ := γC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j) (by omega) h
      have hρ := ρC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j) (by omega) h
      rw [hz, hγ, hρ]
    · refine pathCol_round1 H.V.basis _ _ _ _ _ _ j (fun i k => pathRowsP_base_indep _ _ _ _ i k)
        (fun h1 i s _ => ?_) i (by omega)
      have hz := zC_congr (δF := δF) χ χ' (r := ((shapeV hT hP).table t).colRound j)
        (hlow.1 h1) h
      show (H.pathRows (zC χ) i).qslot s = (H.pathRows (zC χ') i).qslot s
      rw [hz]

end StagedMain

/-! ## 4. The honest bad summands -/

section Bad
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP hC : ℕ} {C : TableSpec}
  (H : HonestVCL (K := K) δF hT hP hC)

namespace HonestVCL

/-- The validity-accumulator denominators of the honest records: `vKey`, `lKey`, `rKey` of every row. -/
def keys0 (χ : Coins frameVCL K) : List (Fin 5 → Quad (algebraMap F K δF)) :=
  (List.range (H.V.memRows (tC hT hP))).map (fun j => vKeyOf δF (H.cellRows (zC χ) j)) ++
  (List.range (H.V.memRows (tC hT hP))).map (fun j => lKeyOf δF (H.cellRows (zC χ) j)) ++
  (List.range (H.V.memRows (tC hT hP))).map (fun j => rKeyOf δF (H.cellRows (zC χ) j))

/-- The export-accumulator denominators: both sides of every cell row and every path edge's consume key. -/
def keys1 (χ : Coins frameVCL K) : List (Fin 11 → Quad (algebraMap F K δF)) :=
  (List.range (H.V.memRows (tC hT hP))).map (fun j => xKeyOf δF (H.cellRows (zC χ) j) 0) ++
  (List.range (H.V.memRows (tC hT hP))).map (fun j => xKeyOf δF (H.cellRows (zC χ) j) 1) ++
  (List.range (H.V.memRows (tP hT hP))).map (fun j => pxKeyOf δF (H.pathRows (zC χ) j))

/-- The path-accumulator denominators: the provided record of every path row. -/
def keys2 (χ : Coins frameVCL K) : List (Fin 8 → Quad (algebraMap F K δF)) :=
  (List.range (H.V.memRows (tP hT hP))).map (fun j => pRecOf δF (H.pathRows (zC χ) j))

theorem zC_eq_seed (χ : Coins frameVCL K) : zC (δF := δF) χ = (seedSpecVCL (algebraMap F K δF)).seed χ := rfl

theorem reads_seed {α : Type} (f : Quad (algebraMap F K δF) → α) :
    ReadsOnC frameVCL (seedSpecVCL (algebraMap F K δF)).dep (fun χ => f (zC χ)) :=
  fun χ χ' h => congrArg f ((seedSpecVCL (algebraMap F K δF)).readsOn χ χ' h)

theorem disj_io_seed :
    Disjoint (ioSpecVCLQuad (algebraMap F K δF)).dep (seedSpecVCL (algebraMap F K δF)).dep := by
  show Disjoint ({ioγVCL.1, ioγVCL.2, ioρVCL.1, ioρVCL.2} : Finset (Fin frameVCL.n)) {c2, c3}
  decide

/-- The zero-seed summand. -/
def zeroS : BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP)) :=
  seedSummand (seedSpecVCL (algebraMap F K δF)) (fun _ => ({0} : Finset (Quad (algebraMap F K δF)))) 1
    (fun _ => by simp)

def poleS0 : BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP)) :=
  poleSummand (ioSpecVCLQuad (algebraMap F K δF)) _ disj_io_seed (3 * H.V.memRows (tC hT hP))
    (fun χ => H.keys0 χ) (fun χ => by simp [keys0]; omega)
    (reads_seed (fun z => (List.range (H.V.memRows (tC hT hP))).map (fun j => vKeyOf δF (H.cellRows z j)) ++
      (List.range (H.V.memRows (tC hT hP))).map (fun j => lKeyOf δF (H.cellRows z j)) ++
      (List.range (H.V.memRows (tC hT hP))).map (fun j => rKeyOf δF (H.cellRows z j))))

def poleS1 : BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP)) :=
  poleSummand (ioSpecVCLQuad (algebraMap F K δF)) _ disj_io_seed
    (2 * H.V.memRows (tC hT hP) + H.V.memRows (tP hT hP))
    (fun χ => H.keys1 χ) (fun χ => by simp [keys1]; omega)
    (reads_seed (fun z => (List.range (H.V.memRows (tC hT hP))).map (fun j => xKeyOf δF (H.cellRows z j) 0) ++
      (List.range (H.V.memRows (tC hT hP))).map (fun j => xKeyOf δF (H.cellRows z j) 1) ++
      (List.range (H.V.memRows (tP hT hP))).map (fun j => pxKeyOf δF (H.pathRows z j))))

def poleS2 : BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP)) :=
  poleSummand (ioSpecVCLQuad (algebraMap F K δF)) _ disj_io_seed (H.V.memRows (tP hT hP))
    (fun χ => H.keys2 χ) (fun χ => by simp [keys2])
    (reads_seed (fun z => (List.range (H.V.memRows (tP hT hP))).map (fun j => pRecOf δF (H.pathRows z j))))

/-- **`honestBad`**: the zero seed and the three pole events of the honest records. -/
def bad : List (BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP))) :=
  [zeroS (δF := δF), H.poleS0, H.poleS1, H.poleS2]

end HonestVCL

end Bad

/-! ## 5. Acceptance -/

section Accepted
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP hC : ℕ} {C : TableSpec}
  (H : HonestVCL (K := K) δF hT hP hC)

theorem sat_transportW {ch ch' : FixedPreprocessingRAP F} (h : ch = ch') (Q : Fin ch.rap.w → F[X])
    (Q' : Fin ch'.rap.w → F[X]) (hQ : ∀ j (hj : j < ch.rap.w) (hj' : j < ch'.rap.w), Q ⟨j, hj⟩ = Q' ⟨j, hj'⟩) :
    RAP.SatisfiesWithPreprocessing ch Q → RAP.SatisfiesWithPreprocessing ch' Q' := by
  subst h
  have : Q = Q' := funext fun j => hQ j j.2 j.2
  rw [← this]; exact id

theorem pathTableP_length_indep (z z' : Quad (algebraMap F K δF)) (cells : List Noun)
    (reads : List (Noun × ℕ)) :
    (pathTableP δF z cells reads).length = (pathTableP δF z' cells reads).length := by
  simpa using congrArg List.length (pathTableP_map_base z z' cells reads 0)

theorem pathTable_length_indep (z z' : Quad (algebraMap F K δF)) (cells : List Noun)
    (reads : List (Noun × ℕ)) :
    (pathTable δF z cells reads).length = (pathTable δF z' cells reads).length := by
  simpa using congrArg List.length (pathTable_map_base z z' cells reads 0)

theorem pole_ne {m : ℕ} (recs : List (Fin m → Quad (algebraMap F K δF))) (χ : Coins frameVCL K)
    (h : (ioSpecVCLQuad (algebraMap F K δF)).pair χ ∉ poleBad recs) :
    ∀ v ∈ recs, FiniteIO.compress (m := m) ⟨γC (δF := δF) χ, ρC χ⟩ v ≠ 0 := by
  intro v hv h0
  apply h
  simp only [poleBad, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, hv, h0⟩

/-- **The honest bad set, decoded**: no zero seed and no pole at any honest record. -/
theorem bad_decode (χ : Coins frameVCL K) (Qc : Fin C.width → F[X])
    (hbad : ∀ s ∈ H.bad (C := C), ¬ s.mem (Qc, fun t => H.trace χ t) χ) :
    zC (δF := δF) χ ≠ 0 ∧
    (∀ v ∈ H.keys0 χ, FiniteIO.compress (m := 5) ⟨γC χ, ρC χ⟩ v ≠ 0) ∧
    (∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0) ∧
    (∀ v ∈ H.keys2 χ, FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ v ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hbad (HonestVCL.zeroS (K := K) (δF := δF) (hT := hT) (hP := hP) (C := C)) (by simp [HonestVCL.bad])
    intro hz
    apply h
    unfold HonestVCL.zeroS
    rw [seedSummand_mem]
    simp [HonestVCL.zC_eq_seed] at hz ⊢
    exact hz
  · have h := hbad H.poleS0 (by simp [HonestVCL.bad])
    unfold HonestVCL.poleS0 at h
    erw [poleSummand_mem] at h
    exact pole_ne _ χ h
  · have h := hbad H.poleS1 (by simp [HonestVCL.bad])
    unfold HonestVCL.poleS1 at h
    erw [poleSummand_mem] at h
    exact pole_ne _ χ h
  · have h := hbad H.poleS2 (by simp [HonestVCL.bad])
    unfold HonestVCL.poleS2 at h
    erw [poleSummand_mem] at h
    exact pole_ne _ χ h

end Accepted

section AcceptedMain
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP hC : ℕ} {C : TableSpec}
  (H : HonestVCL (K := K) δF hT hP hC)

theorem cell_accepted (χ : Coins frameVCL K)
    (hz : zC (δF := δF) χ ≠ 0)
    (h0 : ∀ v ∈ H.keys0 χ, FiniteIO.compress (m := 5) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (h1 : ∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hρ0 : ρ 0 = H.vTot χ) (hρ1 : ρ 1 + y = H.xTot χ) :
    RAP.SatisfiesWithPreprocessing
      (cellChipOk δF H.V.basis (H.V.hM (tC hT hP)) (H.V.memNodes (tC hT hP)) (H.V.orbitM (tC hT hP))
        (chalsVCL δF χ) (pubsC δF ρ y) true)
      (fun j => honestQ (H.V.hM (tC hT hP)) (H.V.memNodes (tC hT hP))
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tC hT hP)) =>
          cellFill δF (γC χ) (ρC χ) (H.cellRows (zC χ)) i')) 225
        (Fin.cast (cellChipOk_w δF H.V.basis (H.V.hM (tC hT hP)) (H.V.memNodes (tC hT hP))
          (H.V.orbitM (tC hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) true) j)) := by
  have hN : H.V.memRows (tC hT hP) = H.d.cells.length := H.hC0
  have hnd := closureOf_nodup H.d.roots
  have hcell : ∀ n ∈ H.d.cells, n.isCell = true := fun n hn => closureOf_isCell hn
  refine cellOk_sat δF H.V.basis (H.V.hM (tC hT hP)) (H.V.memNodes (tC hT hP)) (H.V.orbitM (tC hT hP))
    (chalsVCL δF χ) (pubsC δF ρ y) _ (H.hinj _) (H.hadj _) (γC χ) (ρC χ) (zC χ)
    (chalsVCL_ok δF χ 11) rfl (fun i => ?_) (fun i => ?_)
  · exact cellBaseFacts_fill δF _ _ (H.cellRows (zC χ)) i
      (cellRows0_baseFacts (δF := δF) (zC χ) H.d.cells (vcsOf H.d.cells []) (xs0P H.d.cells H.d.preads H.d.reads)
        (xs1P H.d.cells H.d.preads H.d.reads) hcell hnd H.hrank hN i)
  · have hlt : ∀ j < H.V.memRows (tC hT hP), j < H.d.cells.length := fun j hj => hN ▸ hj
    refine cellFill_facts (γC χ) (ρC χ) (H.cellRows (zC χ)) (zC χ) (pubsC δF ρ y) i hz
      (fun j hj => cellRows0_cons (δF := δF) (zC χ) H.d.cells _ _ _ hcell hz (hlt j hj))
      (fun j hj => cellRows0_atomL (δF := δF) (zC χ) H.d.cells _ _ _ hcell (hlt j hj))
      (fun j hj => cellRows0_atomR (δF := δF) (zC χ) H.d.cells _ _ _ hcell (hlt j hj))
      (fun j hj => h0 _ ?_) (fun j hj _ => h0 _ ?_) (fun j hj _ => h0 _ ?_)
      (fun j hj => h1 _ ?_) (fun j hj => h1 _ ?_) ?_ ?_
    · simp only [HonestVCL.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
    · simp only [HonestVCL.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    · simp only [HonestVCL.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · simp only [HonestVCL.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
    · simp only [HonestVCL.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    · rw [pubsC_01, hρ0]; rfl
    · rw [pubsC_23, hρ1]; rfl

theorem path_accepted (χ : Coins frameVCL K)
    (h1 : ∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (h2 : ∀ v ∈ H.keys2 χ, FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hy : y = H.yTot χ) (hρ2 : ρ 2 = H.pTot χ) :
    RAP.SatisfiesWithPreprocessing
      (pathChipOk δF H.V.basis (H.V.hM (tP hT hP)) (H.V.memNodes (tP hT hP)) (H.V.orbitM (tP hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) true)
      (fun j => honestQ (H.V.hM (tP hT hP)) (H.V.memNodes (tP hT hP))
        (pathCol δF H.V.basis (fun i' : Fin (H.V.memRows (tP hT hP)) =>
          pathFill δF (γC χ) (ρC χ) (H.pathRows (zC χ)) i')) 112
        (Fin.cast (pathChipOk_w δF H.V.basis (H.V.hM (tP hT hP)) (H.V.memNodes (tP hT hP))
          (H.V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) true) j)) := by
  have hN : H.V.memRows (tP hT hP) = (pathTableP δF (zC χ) H.d.cells H.d.preads).length :=
    H.hP0.trans (pathTableP_length_indep _ _ _ _)
  have hgood := pathTableP_good (δF := δF) (zC χ) H.d.cells H.d.preads H.h62
  refine pathOk_sat δF H.V.basis (H.V.hM (tP hT hP)) (H.V.memNodes (tP hT hP)) (H.V.orbitM (tP hT hP))
    (chalsVCL δF χ) (pubsP δF ρ y) _ (H.hinj _) (H.hadj _) (γC χ) (ρC χ)
    (chalsVCL_ok δF χ 11) (fun i => ?_) (fun i => ?_)
  · exact pathBaseFacts_fill δF _ _ (H.pathRows (zC χ)) i
      (pathBaseFacts_of_good _ hgood (chainRow δF (zC χ) H.d.cells (.atom 0) 0 [] 0) hN i)
  · obtain ⟨hrf, hrs, hps⟩ := pathMixedRows_of_good _ hgood (chainRow δF (zC χ) H.d.cells (.atom 0) 0 [] 0)
    refine pathFill_facts (γC χ) (ρC χ) (H.pathRows (zC χ)) (pubsP δF ρ y) i
      (fun j hj => hrf j (hN ▸ hj)) (fun j hj => hrs j (hN ▸ hj)) (fun j hj => hps j (hN ▸ hj))
      (fun j hj => h1 _ ?_) (fun j hj _ => h2 _ ?_) ?_ ?_
    · simp only [HonestVCL.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · simp only [HonestVCL.keys2, List.mem_map, List.mem_range]
      exact ⟨j, hj, rfl⟩
    · rw [pubsP_01, hy]; rfl
    · rw [pubsP_23, hρ2]; rfl

/-- **`honest_accepted`**: outside the honest bad set the `ok`-gated chip of table `t` accepts the honest trace
at the honest requests / message. -/
theorem accepted (χ : Coins frameVCL K) (Qc : Fin C.width → F[X])
    (hbad : ∀ s ∈ H.bad (C := C), ¬ s.mem (Qc, fun t => H.trace χ t) χ) (t : Fin (shapeV hT hP).k) :
    RAP.SatisfiesWithPreprocessing (vclChip δF hT hP (H.req χ) (H.msg2 χ) H.V χ t)
      (fun j => H.trace χ t (Fin.cast (vclChip_width δF hT hP (H.req χ) (H.msg2 χ) H.V χ t) j)) := by
  obtain ⟨hz, h0, h1, h2⟩ := bad_decode H χ Qc hbad
  have hok : ∀ t, okOf H.V t = true := fun t =>
    ok_of_goodM ⟨H.hadj t, H.hinj t, H.hF, H.hq, H.hrows t⟩
  by_cases ht : (t : ℕ) = 0
  · obtain rfl : t = tC hT hP := Fin.ext ht
    have hch : vclChip δF hT hP (H.req χ) (H.msg2 χ) H.V χ (tC hT hP) =
        cellChipOk δF H.V.basis (H.V.hM (tC hT hP)) (H.V.memNodes (tC hT hP)) (H.V.orbitM (tC hT hP))
          (chalsVCL δF χ) (pubsC δF (H.req χ) (H.msg2 χ)) true := by
      unfold vclChip
      rw [if_pos (by rfl), hok]
    have hcol : H.col χ (tC hT hP) = cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tC hT hP)) =>
        cellFill δF (γC χ) (ρC χ) (H.cellRows (zC χ)) i') := by
      funext j i; unfold HonestVCL.col; rw [if_pos ht]
    refine sat_transportW hch.symm _ _ ?_
      (cell_accepted H χ hz h0 h1 (H.req χ) (H.msg2 χ) rfl (sub_add_cancel _ _))
    intro j hj hj'
    simp only [HonestVCL.trace, hcol]
    rfl
  · have ht1 : t = tP hT hP := Fin.ext (by have h2 : (t : ℕ) < 2 := t.2; show (t : ℕ) = 1; omega)
    subst ht1
    have hch : vclChip δF hT hP (H.req χ) (H.msg2 χ) H.V χ (tP hT hP) =
        pathChipOk δF H.V.basis (H.V.hM (tP hT hP)) (H.V.memNodes (tP hT hP)) (H.V.orbitM (tP hT hP))
          (chalsVCL δF χ) (pubsP δF (H.req χ) (H.msg2 χ)) true := by
      unfold vclChip
      rw [if_neg (by show (1 : ℕ) ≠ 0; exact one_ne_zero), hok]
    have hcol : H.col χ (tP hT hP) = pathCol δF H.V.basis (fun i' : Fin (H.V.memRows (tP hT hP)) =>
        pathFill δF (γC χ) (ρC χ) (H.pathRows (zC χ)) i') := by
      funext j i; unfold HonestVCL.col; rw [if_neg (by show (1 : ℕ) ≠ 0; exact one_ne_zero)]
    refine sat_transportW hch.symm _ _ ?_
      (path_accepted H χ h1 h2 (H.req χ) (H.msg2 χ) rfl rfl)
    intro j hj hj'
    simp only [HonestVCL.trace, hcol]
    rfl

/-- **The honest bad set's mass**: `Pr[¬ accepted] ≤ ε` with `ε = (1 + 5·nC + 2·nP) / |𝕂|²` (the zero seed plus the
pole events of the `3nC + (2nC + nP) + nP` honest denominators over the `|𝕂|²` IO-coin pairs). -/
theorem epsilon_bad :
    epsilonOf (H.bad (C := C)) =
      (1 + 5 * (H.V.memRows (tC hT hP) : ℚ) + 2 * (H.V.memRows (tP hT hP) : ℚ)) / (Fintype.card K : ℚ) ^ 2 := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  have hdep : (seedSpecVCL (algebraMap F K δF)).dep.card = 2 := by
    show ({c2, c3} : Finset (Fin frameVCL.n)).card = 2
    decide
  have hio : (ioSpecVCLQuad (algebraMap F K δF)).dep.card = 4 := ioSpecVCLQuad_dep_card _
  have hq : Fintype.card (Quad (algebraMap F K δF)) = Fintype.card K ^ 2 := ioSpecVCLQuad_card _
  unfold epsilonOf HonestVCL.bad
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e0 : ((HonestVCL.zeroS (K := K) (δF := δF) (hT := hT) (hP := hP) (C := C)).weight : ℚ) /
      (Fintype.card K : ℚ) ^ (HonestVCL.zeroS (K := K) (δF := δF) (hT := hT) (hP := hP) (C := C)).coins.card
      = 1 / (Fintype.card K : ℚ) ^ 2 := by
    show ((1 : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ (seedSpecVCL (algebraMap F K δF)).dep.card = _
    rw [hdep]; simp
  have ep : ∀ (len : ℕ), ((len * Fintype.card (Quad (algebraMap F K δF)) : ℕ) : ℚ) /
      (Fintype.card K : ℚ) ^ (ioSpecVCLQuad (algebraMap F K δF)).dep.card = len / (Fintype.card K : ℚ) ^ 2 := by
    intro len
    rw [hio, hq]; push_cast; field_simp
  have p0 : ((H.poleS0 (C := C)).weight : ℚ) / (Fintype.card K : ℚ) ^ (H.poleS0 (C := C)).coins.card =
      ((3 * H.V.memRows (tC hT hP) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := ep _
  have p1 : ((H.poleS1 (C := C)).weight : ℚ) / (Fintype.card K : ℚ) ^ (H.poleS1 (C := C)).coins.card =
      ((2 * H.V.memRows (tC hT hP) + H.V.memRows (tP hT hP) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := ep _
  have p2 : ((H.poleS2 (C := C)).weight : ℚ) / (Fintype.card K : ℚ) ^ (H.poleS2 (C := C)).coins.card =
      ((H.V.memRows (tP hT hP) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := ep _
  rw [e0, p0, p1, p2]
  push_cast
  field_simp
  ring

end AcceptedMain

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
