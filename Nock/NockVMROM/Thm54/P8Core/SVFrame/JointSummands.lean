/-
  Nock/NockVMROM/Thm54/P8Core/SVFrame/JointSummands.lean

  **The joint summands `jointSummands CF MF`.**
  Every summand is a `BadSummand` whose `card_le` and `readsOn` are proved
  from the families' fields and `TracesStaged` only.

  * `ioSummand_mass_ext`: at `|I.dep| = 4`, `|Kio| = |𝕂|²` (VCL-L,
    `𝕂′` coins) the mass is `ioFailureUnionBound (m a) k₁ k₂ 1 / |𝕂|²` (DESIGN §3, `ioFUB_sq`).
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.FibreBound
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JoinUtil

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVFrame

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable Nock.FieldEmbedding
open Nock.NockVMROM.Thm54
open scoped Polynomial

noncomputable section

/-! ## 1. Seed cylinders -/

section Seed

variable {Φ : CoinFrame} {K Kfp : Type} [Field K]

/-- Extend values on the seed coins by `0`. -/
def extDep (Z : SeedSpec Φ K Kfp) (v : Z.dep → K) : Coins Φ K :=
  fun i => if h : i ∈ Z.dep then v ⟨i, h⟩ else 0

theorem seed_extDep (Z : SeedSpec Φ K Kfp) (χ : Coins Φ K) :
    Z.seed (extDep Z fun i : Z.dep => χ i) = Z.seed χ :=
  Z.readsOn _ _ (fun j hj => by simp [extDep, hj])

theorem extDep_inj (Z : SeedSpec Φ K Kfp) {v v' : Z.dep → K}
    (h : Z.seed (extDep Z v) = Z.seed (extDep Z v')) : v = v' := by
  funext ⟨i, hi⟩
  have := Z.inj _ _ h i hi
  simpa [extDep, hi] using this

end Seed

section B0

variable {F K : Type} [Field F] {Φ : CoinFrame} {C : TableSpec} {S : MemShape}

/-- The B0 columns of both sides. -/
abbrev B0Pair (F : Type) [Field F] (C : TableSpec) (S : MemShape) :=
  B0Cols F C × (∀ t, B0Cols F (S.table t))

/-- The B0 projection of a trace pair. -/
def b0Tr (tr : Traces F C S) : B0Pair F C S := (b0 tr.1, fun t => b0 (tr.2 t))

/-- Along a staged strategy the B0 columns are coin-free. -/
theorem b0Tr_staged {Q : Coins Φ K → Traces F C S} (hQ : TracesStaged Φ C S Q) (χ χ' : Coins Φ K) :
    b0Tr (Q χ) = b0Tr (Q χ') := by
  have h0 : ∀ (r : ℕ), r = 0 → ∀ i : Fin Φ.n, Φ.sampledAfter i < r → χ i = χ' i := by
    intro r hr i hi; omega
  simp only [b0Tr]
  congr 1
  · funext j; exact hQ.1 j.1 χ χ' (h0 _ j.2)
  · funext t j; exact hQ.2 t j.1 χ χ' (h0 _ j.2)

end B0

section SeedSummand

variable {F K Kfp : Type} [Field F] [Field K] [Fintype K] [DecidableEq K] [DecidableEq Kfp]
  {Φ : CoinFrame} {C : TableSpec} {S : MemShape}

open Classical in
/-- **A seed cylinder**: the bad set is the preimage, on the seed coins, of a B0-determined set of
bad seeds. -/
def seedSummand (Z : SeedSpec Φ K Kfp) (B : B0Pair F C S → Finset Kfp) (w : ℕ)
    (hB : ∀ b, (B b).card ≤ w) : BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) where
  coins := Z.dep
  dep := ∅
  disj := Finset.disjoint_empty_right _
  badSet tr _ := Finset.univ.filter fun v : Z.dep → K => Z.seed (extDep Z v) ∈ B (b0Tr tr)
  weight := w
  card_le tr _ := by
    refine le_trans (Finset.card_le_card_of_injOn (fun v => Z.seed (extDep Z v)) ?_ ?_) (hB (b0Tr tr))
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h
      exact extDep_inj Z h
  readsOn Q hQ χ χ' _ := by
    simp only [b0Tr_staged hQ χ χ']

theorem seedSummand_mem (Z : SeedSpec Φ K Kfp) (B : B0Pair F C S → Finset Kfp) (w : ℕ)
    (hB : ∀ b, (B b).card ≤ w) (tr : Traces F C S) (χ : Coins Φ K) :
    (seedSummand Z B w hB).mem tr χ ↔ Z.seed χ ∈ B (b0Tr tr) := by
  classical
  unfold BadSummand.mem
  show (fun i : Z.dep => χ i) ∈
      (Finset.univ.filter fun v : Z.dep → K => Z.seed (extDep Z v) ∈ B (b0Tr tr)) ↔ _
  rw [Finset.mem_filter, seed_extDep]
  simp

end SeedSummand

/-! ## 2. The families' B0 join and the census lists -/

section Families

variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp]
  [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {Φ : CoinFrame} {hC : ℕ} {S : MemShape} {C : TableSpec} {nAcc : ℕ} {m : Fin nAcc → ℕ}
  {R : RecordView F K Kio Kfp Key C S hC m} {Z : SeedSpec Φ K Kfp} {I : IOCoinSpec Φ K Kio}
  (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
  (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)

/-- The window the generic proof runs at: `windowAt`'s body, a function of `(V, y)`. -/
def windowW (V : VerifierData F K hC S) (y : MF.Msg0) : ℕ :=
  max (leafBoundF (ringChar Kfp) V.N V.claim) (MF.windowBound V y)

/-- The served-noun oracle at B0. -/
def svB0 (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (b : B0Pair F C S) :
    MState → ℕ → Noun :=
  fun st k => MF.served V y b.2 (CF.keyOf V x b.1 st k)

/-- **The field C2 join at B0**: the shape, the served nouns, the B0 axis oracle, the claim. -/
def joinB0 (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (b : B0Pair F C S) :
    NTree SemanticStrategy.ComputeRowSkeleton :=
  SVJoinF.c2JoinFuelF (ringChar Kfp) Prod.fst Prod.snd (svB0 CF MF V x y b) (CF.axB0 V x b.1 b.2)
    (CF.shape V x b.1).size (CF.shape V x b.1) V.claim.subject V.claim.formula

theorem joinB0_size_le (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (b : B0Pair F C S) :
    (joinB0 CF MF V x y b).size ≤ V.N :=
  (c2JoinFuelF_size_le _ _ _ _ _ _ _ _ _).trans (CF.shape_size V x b.1)

/-- The NPR census list: every comparison of every node of the B0 join. -/
def censusPairs (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (b : B0Pair F C S) :
    List (Noun × Noun) :=
  (bfsForest [joinB0 CF MF V x y b]).flatMap fun w =>
    (P8Census.skeletonComparisons (K := Kfp) w.label).map SemanticTrace.ComparisonUse.pair

theorem length_flatMap_le {α γ : Type*} (l : List α) (f : α → List γ) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := h a (List.mem_cons_self ..)
      have h2 := ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
      rw [Nat.mul_succ]
      omega

theorem censusPairs_length_le (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0)
    (b : B0Pair F C S) : (censusPairs CF MF V x y b).length ≤ 10 * V.N := by
  refine (length_flatMap_le _ _ 10 (fun w _ => ?_)).trans ?_
  · rw [List.length_map]; exact P8Census.skeletonComparisons_length_le Kfp w.label
  · rw [bfsForest_length]
    have : totalSize [joinB0 CF MF V x y b] = (joinB0 CF MF V x y b).size := by
      simp [totalSize]
    rw [this]
    exact Nat.mul_le_mul_left _ (joinB0_size_le CF MF V x y b)

/-- The root of record `j` of a join row (a dummy atom past the row's record count). -/
def recRootOf (v : SemanticStrategy.ComputeRowSkeleton) (j : Fin 3) : Noun :=
  if h : (j : ℕ) < Nock.Framework.recordCount v.state then (v.memoryRecord j h).root else .atom 0

/-- The record-pair census list: for every node of the shape paired with its join row, every
record `j`, the pair (structural record root, served root at the record's key). -/
def recPairs (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (b : B0Pair F C S) :
    List (Noun × Noun) :=
  (zipLabels (CF.shape V x b.1) (joinB0 CF MF V x y b)).flatMap fun p =>
    (List.finRange 3).map fun j =>
      (recRootOf p.2 j, MF.servedRoot V y b.2 (CF.recKey V x b.1 p.1.1 p.1.2 j))

theorem recPairs_length_le (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0)
    (b : B0Pair F C S) : (recPairs CF MF V x y b).length ≤ 3 * V.N := by
  refine (length_flatMap_le _ _ 3 (fun p _ => by simp)).trans ?_
  exact Nat.mul_le_mul_left _ ((zipLabels_length_le _ _).trans (CF.shape_size V x b.1))

/-- The inline-record census list: for every inline record of every node of the shape
paired with its join row, the instance's `inlinePairs` at the record's structural root. -/
def inlinePairsList (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (b : B0Pair F C S) :
    List (Noun × Noun) :=
  (zipLabels (CF.shape V x b.1) (joinB0 CF MF V x y b)).flatMap fun p =>
    (List.finRange 3).flatMap fun j : Fin 3 =>
      if (j : ℕ) < CF.inlineRecords p.1.1 then CF.inlinePairs p.1.1 (j : ℕ) (recRootOf p.2 j) else []

theorem inlinePairsList_length_le (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0)
    (b : B0Pair F C S) : (inlinePairsList CF MF V x y b).length ≤ 3 * CF.inlinePairCount * V.N := by
  refine (length_flatMap_le _ _ (3 * CF.inlinePairCount) (fun p _ => ?_)).trans ?_
  · refine (length_flatMap_le _ _ CF.inlinePairCount (fun j _ => ?_)).trans ?_
    · split_ifs
      · exact CF.inlinePairs_length _ _ _
      · simp
    · simp [Nat.mul_comm]
  · exact Nat.mul_le_mul_left _ ((zipLabels_length_le _ _).trans (CF.shape_size V x b.1))

/-- The root-result pair. -/
def rootPairs (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (b : B0Pair F C S) :
    List (Noun × Noun) :=
  [((joinB0 CF MF V x y b).label.evaluation, V.claim.result)]

/-! ## 3. The IO summand -/

/-- The coins sampled after blocks `< r`. -/
def coinsBelow (Φ : CoinFrame) (r : ℕ) : Finset (Fin Φ.n) :=
  Finset.univ.filter fun i => Φ.sampledAfter i < r

/-- Extend values on the IO coins by `0`. -/
def extIO (I : IOCoinSpec Φ K Kio) (v : I.dep → K) : Coins Φ K :=
  fun i => if h : i ∈ I.dep then v ⟨i, h⟩ else 0

theorem pair_extIO (I : IOCoinSpec Φ K Kio) (χ : Coins Φ K) :
    I.pair (extIO I fun i : I.dep => χ i) = I.pair χ := by
  unfold IOCoinSpec.pair
  rw [I.readsOn (extIO I fun i : I.dep => χ i) χ (fun j hj => by simp [extIO, hj])]

theorem extIO_inj (I : IOCoinSpec Φ K Kio) {v v' : I.dep → K}
    (h : I.pair (extIO I v) = I.pair (extIO I v')) : v = v' := by
  have h' : I.ioCoins (extIO I v) = I.ioCoins (extIO I v') := by
    unfold IOCoinSpec.pair at h
    cases hc : I.ioCoins (extIO I v)
    cases hc' : I.ioCoins (extIO I v')
    rw [hc, hc'] at h
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]
  funext ⟨i, hi⟩
  have := I.inj _ _ h' i hi
  simpa [extIO, hi] using this

open Classical in
/-- The IO failure event of accumulator `a` at the traces' record lists (empty past the bounds). -/
def ioEventAt (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc)
    (tr : Traces F C S) (χ : Coins Φ K) : Finset (Kio × Kio) :=
  if (CF.reqRecords V x tr.1 χ a ++ MF.internal V y tr.2 χ a).length ≤
        CF.reqBound V a + MF.internalBound V a ∧
      (MF.respRecords V y tr.2 χ a).length ≤ MF.respBound V a
  then FiniteIO.IOFailureEventW (CF.reqRecords V x tr.1 χ a ++ MF.internal V y tr.2 χ a)
    (liftWts (MF.respRecords V y tr.2 χ a))
  else ∅

theorem ioFailureUnionBound_mono {m k₁ k₂ K₁ K₂ c : ℕ} (h₁ : k₁ ≤ K₁) (h₂ : k₂ ≤ K₂) :
    FiniteIO.ioFailureUnionBound m k₁ k₂ c ≤ FiniteIO.ioFailureUnionBound m K₁ K₂ c := by
  unfold FiniteIO.ioFailureUnionBound
  have h : k₁ + k₂ ≤ K₁ + K₂ := Nat.add_le_add h₁ h₂
  gcongr

theorem ioEventAt_card_le (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc)
    (tr : Traces F C S) (χ : Coins Φ K) :
    (ioEventAt CF MF V x y a tr χ).card ≤
      FiniteIO.ioFailureUnionBound (m a) (CF.reqBound V a + MF.internalBound V a) (MF.respBound V a)
        (Fintype.card Kio) := by
  unfold ioEventAt
  split_ifs with h
  · refine (FiniteIO.IOFailureEventW_card_le _ _).trans (ioFailureUnionBound_mono h.1 ?_)
    rw [liftWts_length]; exact h.2
  · simp

open Classical in
def ioSummand (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc) :
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
  badSet tr χ := Finset.univ.filter fun v => I.pair (extIO I v) ∈ ioEventAt CF MF V x y a tr χ
  weight := FiniteIO.ioFailureUnionBound (m a) (CF.reqBound V a + MF.internalBound V a)
    (MF.respBound V a) (Fintype.card Kio)
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn (fun v => I.pair (extIO I v)) ?_ ?_)
      (ioEventAt_card_le CF MF V x y a tr χ)
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
    show (Finset.univ.filter fun v => I.pair (extIO I v) ∈ ioEventAt CF MF V x y a (Q χ) χ) =
      Finset.univ.filter fun v => I.pair (extIO I v) ∈ ioEventAt CF MF V x y a (Q χ') χ'
    have hint : MF.internal V y (Q χ).2 χ = MF.internal V y (Q χ').2 χ' :=
      MF.internal_round V y _ _ χ χ' (fun t j hj => hQ.2 t j χ χ' (fun i hi => hin i (by omega)))
        (fun i hi => hin i (by omega))
    unfold ioEventAt
    rw [hreq, hresp, hint]

theorem ioSummand_mem (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc)
    (tr : Traces F C S) (χ : Coins Φ K) :
    (ioSummand CF MF V x y a).mem tr χ ↔ I.pair χ ∈ ioEventAt CF MF V x y a tr χ := by
  classical
  unfold BadSummand.mem
  show (fun i : I.dep => χ i) ∈
      (Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ ioEventAt CF MF V x y a tr χ) ↔ _
  rw [Finset.mem_filter, pair_extIO]
  simp

/-- **The IO summand's mass at `𝕂′` coins** (DESIGN §3): with four IO frame coins and
`|Kio| = |𝕂|²`, `weight / |𝕂|^4 = ioFailureUnionBound (m a) k₁ k₂ 1 / |𝕂|²` — the `1`-form over
`|𝕂|²` that V3's `ioWorkKp` sums. -/
theorem ioSummand_mass_ext (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (a : Fin nAcc)
    (hdep : I.dep.card = 4) (hcard : Fintype.card Kio = Fintype.card K ^ 2) :
    ((ioSummand CF MF V x y a).weight : ℚ) /
        (Fintype.card K : ℚ) ^ (ioSummand CF MF V x y a).coins.card =
      (FiniteIO.ioFailureUnionBound (m a) (CF.reqBound V a + MF.internalBound V a)
        (MF.respBound V a) 1 : ℚ) / (Fintype.card K : ℚ) ^ 2 := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  show ((FiniteIO.ioFailureUnionBound (m a) (CF.reqBound V a + MF.internalBound V a)
      (MF.respBound V a) (Fintype.card Kio) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ I.dep.card = _
  rw [hdep, hcard, FiniteIO.ioFUB_mul]
  push_cast
  field_simp

/-- No bound on the multiplicities. -/
theorem serves_of_weighted_lookup {p : ℕ} [CharP Kio p] (χ : Coins Φ K) (a : Fin nAcc)
    (reqs internal : List (Fin (m a) → Kio)) (ρ : Kio)
    (M : IOFacts F (FiniteIO.compress (m := m a) (I.ioCoins χ))
      (ρ + (internal.map fun r => (FiniteIO.compress (m := m a) (I.ioCoins χ) r)⁻¹).sum))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := m a) (I.ioCoins χ) r)⁻¹).sum = ρ)
    (hne : ∀ r ∈ reqs, FiniteIO.compress (m := m a) (I.ioCoins χ) r ≠ 0)
    (hine : ∀ r ∈ internal, FiniteIO.compress (m := m a) (I.ioCoins χ) r ≠ 0)
    (hio : I.pair χ ∉ FiniteIO.IOFailureEventW (reqs ++ internal) (liftWts M.records))
    (hcount : (reqs ++ internal).length < p) :
    ∀ r ∈ reqs, r ∈ M.records.map Prod.fst := by
  have hγ : (I.ioCoins χ).gamma ∉
      FiniteIO.IORLCCollisionEvent (FiniteIO.recordsW (reqs ++ internal) (liftWts M.records)) :=
    fun h => hio (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inl h))
  have hpole : (I.ioCoins χ).pole ∉
      FiniteIO.IOLogDerivEventW (reqs ++ internal) (liftWts M.records) (I.ioCoins χ).gamma :=
    fun h => hio (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr h)))
  have hsl := FiniteIO.finiteIO_lookup_sound_weighted (p := p) (reqs ++ internal) (liftWts M.records)
    (I.ioCoins χ)
    (by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact hne r h
      · exact hine r h)
    (by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      exact M.ne_zero q' hq')
    (by
      rw [List.map_append, List.sum_append, hsum]
      have := M.sum_eq
      simp only [liftWts, List.map_map, Function.comp_def]
      rw [this])
    hcount hγ hpole
  intro r hr
  rw [← liftWts_fst]
  exact hsl r (List.mem_append_left _ hr)

/-- **The consumer count from the verifier's check.**  Any request
list within `CF.reqBound` and any internal list within `MF.internalBound` meet the count
hypothesis of `serves_of_weighted_lookup` under `V.Checks (consumerBound CF MF V) (ringChar Kio)`. -/
theorem consumer_count_of_checks (V : VerifierData F K hC S)
    (hV : V.Checks (consumerBound CF MF V) (ringChar Kio)) (a : Fin nAcc)
    (reqs internal : List (Fin (m a) → Kio)) (h₁ : reqs.length ≤ CF.reqBound V a)
    (h₂ : internal.length ≤ MF.internalBound V a) :
    (reqs ++ internal).length < ringChar Kio := by
  have hc := hV.hcons a
  unfold consumerBound at hc
  rw [List.length_append]
  omega

/-- **`MF.serves`' hypotheses suffice for the weighted lookup.** -/
theorem serves_holds_of_weighted_lookup (V : VerifierData F K hC S) (y : MF.Msg0)
    (ρ : Fin nAcc → Kio) (y2 : MF.Msg2) (χ : Coins Φ K) (Q : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (h : ∀ t, Framework.RAP.SatisfiesWithPreprocessing (MF.chip V t y ρ y2 χ)
      (fun j => Q t (Fin.cast (MF.chip_width V t y ρ y2 χ) j)))
    (reqs : ∀ a : Fin nAcc, List (Fin (m a) → Kio))
    (hsum : ∀ a, ((reqs a).map fun r => (FiniteIO.compress (m := m a) (I.ioCoins χ) r)⁻¹).sum = ρ a)
    (hne : ∀ a, ∀ r ∈ reqs a, FiniteIO.compress (m := m a) (I.ioCoins χ) r ≠ 0)
    (hio : ∀ a, I.pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ MF.internal V y Q χ a) (liftWts (MF.respRecords V y Q χ a)))
    (hcount : ∀ a, (reqs a ++ MF.internal V y Q χ a).length < ringChar Kio) :
    ∀ a, ∀ r ∈ reqs a, r ∈ (MF.ioFacts V y ρ y2 χ Q h a).records.map Prod.fst := by
  intro a
  have hio' : I.pair χ ∉ FiniteIO.IOFailureEventW (reqs a ++ MF.internal V y Q χ a)
      (liftWts (MF.ioFacts V y ρ y2 χ Q h a).records) := by
    rw [MF.ioFacts_records]; exact hio a
  exact serves_of_weighted_lookup (p := ringChar Kio) χ a (reqs a) (MF.internal V y Q χ a) (ρ a)
    (MF.ioFacts V y ρ y2 χ Q h a) (hsum a) (hne a) (MF.internal_ne_zero V y ρ y2 χ Q h a) hio'
    (hcount a)

/-! ## 4. The joint summand list -/

/-- The zero-seed summand. -/
def zeroSummand : BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) :=
  seedSummand (F := F) (C := C) (S := S) Z (fun _ => ({0} : Finset Kfp)) 1 (fun _ => by simp)

/-- The low-order seed window at `windowW V y`, weight `lowW W`. -/
def lowSummand (lowW : ℕ → ℕ)
    (hlowW : ∀ W, (SizeWindowCounting.lowOrderRootSeeds (K := Kfp) W).card ≤ lowW W)
    (V : VerifierData F K hC S) (y : MF.Msg0) : BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) :=
  seedSummand Z (fun _ => SizeWindowCounting.lowOrderRootSeeds (K := Kfp) (windowW MF V y))
    (lowW (windowW MF V y)) (fun _ => hlowW _)

/-- The NPR census at the B0 join, weight `10·N·(2W − 1)`. -/
def censusSummand (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) :
    BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) :=
  seedSummand Z (fun b => PreSeedCensus.pairBadSeeds (K := Kfp) (windowW MF V y)
      (censusPairs CF MF V x y b))
    (10 * V.N * (2 * windowW MF V y - 1))
    (fun b => (PreSeedCensus.pairBadSeeds_card_le _ _).trans
      (Nat.mul_le_mul_right _ (censusPairs_length_le CF MF V x y b)))

/-- The record-pair census, weight `3·N·(2W − 1)`. -/
def recSummand (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) :
    BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) :=
  seedSummand Z (fun b => PreSeedCensus.pairBadSeeds (K := Kfp) (windowW MF V y)
      (recPairs CF MF V x y b))
    (3 * V.N * (2 * windowW MF V y - 1))
    (fun b => (PreSeedCensus.pairBadSeeds_card_le _ _).trans
      (Nat.mul_le_mul_right _ (recPairs_length_le CF MF V x y b)))

/-- The inline-record census, weight `3·c·N·(2W − 1)` (`c = inlinePairCount`; `0` at
walk-style instances). -/
def inlineSummand (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) :
    BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) :=
  seedSummand Z (fun b => PreSeedCensus.pairBadSeeds (K := Kfp) (windowW MF V y)
      (inlinePairsList CF MF V x y b))
    (3 * CF.inlinePairCount * V.N * (2 * windowW MF V y - 1))
    (fun b => (PreSeedCensus.pairBadSeeds_card_le _ _).trans
      (Nat.mul_le_mul_right _ (inlinePairsList_length_le CF MF V x y b)))

/-- The root-result pair, weight `2W − 1`. -/
def rootSummand (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) :
    BadSummand Φ K (Traces F C S) (TracesStaged Φ C S) :=
  seedSummand Z (fun b => PreSeedCensus.pairBadSeeds (K := Kfp) (windowW MF V y)
      (rootPairs CF MF V x y b))
    (2 * windowW MF V y - 1)
    (fun b => (PreSeedCensus.pairBadSeeds_card_le _ _).trans (by simp [rootPairs]))

/-- **The joint summands** at `(V, x, y)`, with the low-order window weight `lowW` a parameter. -/
def jointSummands (lowW : ℕ → ℕ)
    (hlowW : ∀ W, (SizeWindowCounting.lowOrderRootSeeds (K := Kfp) W).card ≤ lowW W)
    (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) :
    List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S)) :=
  [zeroSummand (F := F) (C := C) (S := S) (Z := Z), lowSummand MF lowW hlowW V y,
    censusSummand CF MF V x y, recSummand CF MF V x y, rootSummand CF MF V x y,
    inlineSummand CF MF V x y] ++
  List.ofFn (ioSummand CF MF V x y)

/-- The joint summands at the triangular root count (`sizeWindowRootBound`). -/
def jointSummandsStd (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) :
    List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S)) :=
  jointSummands CF MF SizeWindowCounting.sizeWindowRootBound
    (SizeWindowCounting.lowOrderRootSeeds_card_le (K := Kfp)) V x y

end Families

end

end Nock.NockVMROM.Thm54.SVFrame
