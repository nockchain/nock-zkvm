/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestEpsVSQ.lean

  Additive: a NEW module.

  The honest bad events of `honest_accepted_VSQ_run`, priced and summed:
  * the 39th's seed / key-pole events at the first eleven coins (`epsilon_badW`: `(1 + 5·n_C + 3·n_W)/|𝕂|²`),
    lifted to `frameVSQ` through the uniform fibres of `toVCL ∘ toVS` (`card_toVCLQ_preimage`, six free coins);
  * ONE `𝕂′` pole summand (`pairSummandD`, a two-coin cylinder whose bad set reads `dep`): the pair
    `ρH′ = (χ₁₂, χ₁₆)` hits one of the run's record denominators at `γH′ = (χ₁₁, χ₁₅)` (every cell row's export
    record, every walk row's three records, every compute row's `polesOf`), weight `n_C + 3·n_W + 10·N` over
    `|𝕂|² = |𝕂′|` (`pairQ_bad_card`);
  * the walk coin order on `αW = χ₁₃`: `N²/|𝕂|` (as at VS).
  `honestGoodQ_of_notBad` decodes "outside every summand" into `HonestGoodVSQ`; **`vsqCompleteness`**:
  `Pr_χ[¬ HonestGoodVSQ] ≤ epsCVSQ`; **`vsqCompleteness_figure`**: `epsCVSQ < 2^-126` at `|𝕂| = cK = p³`
  (`two_pow_189_le_cK`, from `card_K_value`; `goldilocks_prime` is a theorem) and rows `≤ 2^31`;
  `honest_accepted_VSQ_whp` composes acceptance with the bound.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRunVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestEpsVS
import Nock.NockVMROM.Thm54.VclL.Events.Bound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The fibres of `toVCL ∘ toVS` -/

section Fibre
variable {K : Type} [Fintype K] [DecidableEq K]

/-- `frameVSQ`'s coins split as `frameVCL`'s eleven and the six VSQ coins. -/
def splitVSQ : Coins frameVSQ K ≃ Coins frameVCL K × (Fin 6 → K) where
  toFun χ := (toVCL (toVS χ), fun k => χ ⟨11 + k, by have := k.isLt; change 11 + (k : ℕ) < 17; omega⟩)
  invFun p := fun i => if h : (i : ℕ) < 11 then p.1 ⟨i, h⟩
    else p.2 ⟨i - 11, by have := i.isLt; change (i : ℕ) < 17 at this; omega⟩
  left_inv χ := by
    funext i
    by_cases h : (i : ℕ) < 11
    · simp only [dif_pos h]; rfl
    · simp only [dif_neg h]; congr 1; apply Fin.ext; simp; omega
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext i; simp only [toVCL, toVS]; rw [dif_pos (by exact i.isLt)]
    · funext k; simp only; rw [dif_neg (by omega)]; congr 1; apply Fin.ext; simp

theorem card_toVCLQ_preimage (S : Finset (Coins frameVCL K)) :
    (Finset.univ.filter fun χ : Coins frameVSQ K => toVCL (toVS χ) ∈ S).card = S.card * Fintype.card K ^ 6 := by
  have h : (Finset.univ.filter fun χ : Coins frameVSQ K => toVCL (toVS χ) ∈ S) =
      (S ×ˢ (Finset.univ : Finset (Fin 6 → K))).map splitVSQ.symm.toEmbedding := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_product,
      Equiv.coe_toEmbedding]
    constructor
    · intro hχ; exact ⟨splitVSQ χ, ⟨hχ, trivial⟩, splitVSQ.symm_apply_apply χ⟩
    · rintro ⟨p, ⟨hp, -⟩, rfl⟩
      have : toVCL (toVS (splitVSQ.symm p)) = p.1 := congrArg Prod.fst (splitVSQ.apply_symm_apply p)
      rw [this]; exact hp
  rw [h, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

theorem card_coins_VSQ :
    Fintype.card (Coins frameVSQ K) = Fintype.card (Coins frameVCL K) * Fintype.card K ^ 6 := by
  rw [Fintype.card_congr splitVSQ, Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin]

end Fibre

/-! ## 2. A two-coin cylinder whose bad set reads other coins -/

section Pair
variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
  {Staged : (Coins Φ K → Tr) → Prop}

/-- **A two-coin cylinder**: the pair `(χ i, χ j)` lands in a bad set that reads only the coins `D`. -/
def pairSummandD (i j : Fin Φ.n) (D : Finset (Fin Φ.n)) (hdisj : Disjoint ({i, j} : Finset (Fin Φ.n)) D)
    (bad : Tr → Coins Φ K → Finset (K × K)) (w : ℕ) (hw : ∀ tr χ, (bad tr χ).card ≤ w)
    (hr : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ D (fun χ => bad (Q χ) χ)) :
    BadSummand Φ K Tr Staged where
  coins := {i, j}
  dep := D
  disj := hdisj
  badSet tr χ := Finset.univ.filter fun f => (f ⟨i, by simp⟩, f ⟨j, by simp⟩) ∈ bad tr χ
  weight := w
  card_le tr χ := by
    refine le_trans ?_ (hw tr χ)
    refine Finset.card_le_card_of_injOn (fun f => (f ⟨i, by simp⟩, f ⟨j, by simp⟩)) ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
      exact hf
    · intro f _ f' _ h
      simp only [Prod.mk.injEq] at h
      funext x
      obtain ⟨x, hx⟩ := x
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact h.1
      · rw [Finset.mem_singleton] at hx'; subst hx'; exact h.2
  readsOn Q hQ χ χ' hχ := by
    have e := hr Q hQ χ χ' hχ
    dsimp only at e ⊢
    rw [e]

theorem pairSummandD_mem (i j : Fin Φ.n) (D : Finset (Fin Φ.n)) (hdisj : Disjoint ({i, j} : Finset (Fin Φ.n)) D)
    (bad : Tr → Coins Φ K → Finset (K × K)) (w : ℕ) (hw : ∀ tr χ, (bad tr χ).card ≤ w)
    (hr : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ D (fun χ => bad (Q χ) χ)) (tr : Tr) (χ : Coins Φ K) :
    (pairSummandD i j D hdisj bad w hw hr).mem tr χ ↔ (χ i, χ j) ∈ bad tr χ := by
  show _ ∈ Finset.univ.filter _ ↔ _
  erw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

end Pair

/-! ## 3. The `𝕂′` pole set -/

section PoleQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

open Classical in
/-- The coin pairs `(a, b)` with `a + b√δ + y = 0` for a pole `y ∈ l`. -/
def poleBadQ (l : List (Quad (algebraMap F K δF))) : Finset (K × K) :=
  Finset.univ.filter fun p : K × K => ∃ y ∈ l, Quad.mk (algebraMap F K δF) p.1 p.2 + y = 0

theorem mem_poleBadQ (l : List (Quad (algebraMap F K δF))) (p : K × K) :
    p ∈ poleBadQ δF l ↔ ∃ y ∈ l, Quad.mk (algebraMap F K δF) p.1 p.2 + y = 0 := by
  unfold poleBadQ; simp

/-- **A `𝕂′` pole set has at most one coin pair per pole.** -/
theorem pairQ_bad_card (l : List (Quad (algebraMap F K δF))) : (poleBadQ δF l).card ≤ l.length := by
  have hsub : poleBadQ δF l ⊆
      l.toFinset.image (fun y => (Quad.re _ (-y), Quad.im _ (-y))) := by
    intro p hp
    obtain ⟨y, hy, h⟩ := (mem_poleBadQ δF l p).mp hp
    refine Finset.mem_image.mpr ⟨y, List.mem_toFinset.mpr hy, ?_⟩
    have e : Quad.mk (algebraMap F K δF) p.1 p.2 = -y := eq_neg_of_add_eq_zero_left h
    rw [← e]
    simp [Quad.re_mk, Quad.im_mk]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (List.toFinset_card_le l))

end PoleQ

/-! ## 4. The honest VSQ summands -/

section SummandsQ
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- The base environment of compute row `r` of the honest VSQ run. -/
def eFrQ (χ : Coins frameVSQ K) (r : ℕ) : Env F :=
  baseEnvC H.d.cells (wRows (fW t)) (fW t).length (chalVHQ H.V.basis χ)
    (pubVHQ δF H.V.basis H.V.claim x (rhoVSQ H t χ) χ) r

/-- **Every `𝕂′` record denominator of the honest run, minus the pole coin `ρH′`** (cell rows, walk rows,
compute rows), at `γH′`. -/
def allPolesQ (χ : Coins frameVSQ K) : List (Quad (algebraMap F K δF)) :=
  H.d.cells.map (fun n => recRest (gamHQ δF χ) (expKey (F := F) H.d.cells n)) ++
  (walkRows H.d.cells H.d.preads).flatMap (fun w =>
    [recRest (gamHQ δF χ) (expKey (F := F) H.d.cells w.label.node),
     recRestP (gamHQ δF χ) (Handle.recLH (F := F) H.d.cells w.label),
     recRestP (gamHQ δF χ) (Handle.recRH (F := F) H.d.cells w.label)]) ++
  (List.range (fW t).length).flatMap (fun r =>
    polesOf (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ)) (eFrQ H t x χ r))

theorem allPolesQ_length (χ : Coins frameVSQ K) :
    (allPolesQ H t x χ).length = H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) +
      polesOfLen * (fW t).length := by
  unfold allPolesQ
  simp only [List.length_append, List.length_map, List.length_flatMap, List.length_cons, List.length_nil,
    polesOf_length, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  rw [H.hC0, H.hW0]
  ring

theorem eCQ_gamma (χ : Coins frameVSQ K) :
    (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ)).chal ChipH.chalGammaL = gamHQ δF χ := by
  unfold HonestCompQ.eCQ
  rw [HonestCompQ.eKq_gamma, coinsCV_VSQ]

theorem eCQ_rho (χ : Coins frameVSQ K) :
    (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ)).chal ChipH.chalRhoL = rhoHQ δF χ := by
  unfold HonestCompQ.eCQ
  rw [HonestCompQ.eKq_rho, coinsCV_VSQ]

theorem allPolesQ_reads (χ χ' : Coins frameVSQ K) (h : gamHQ δF χ = gamHQ δF χ') :
    allPolesQ H t x χ = allPolesQ H t x χ' := by
  have e : (List.range (fW t).length).flatMap (fun r =>
      polesOf (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ)) (eFrQ H t x χ r)) =
      (List.range (fW t).length).flatMap (fun r =>
      polesOf (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ')) (eFrQ H t x χ' r)) :=
    List.flatMap_congr fun r _ => polesOf_congr _ _ _ _ (fun c _ => rfl) (by rw [eCQ_gamma, eCQ_gamma, h])
  unfold allPolesQ
  rw [h, e]

def cGamHre : Fin frameVSQ.n := ⟨11, by decide⟩
def cRhoHre : Fin frameVSQ.n := ⟨12, by decide⟩

theorem poleQ_disj : Disjoint ({cRhoHre, cRhoHi} : Finset (Fin frameVSQ.n)) {cGamHre, cGamHi} := by decide

theorem rhoHQ_eq (χ : Coins frameVSQ K) : rhoHQ δF χ = Quad.mk _ (χ cRhoHre) (χ cRhoHi) := rfl

/-- **The `𝕂′` handle pole summand** (coin pair `ρH′ = (χ₁₂, χ₁₆)`, dep `γH′ = (χ₁₁, χ₁₅)`): `ρH′` hits one of
the honest run's record denominators.  Weight `n_C + 3·n_W + polesOfLen·N` over `|𝕂|² = |𝕂′|`. -/
def poleHSQ : BadSummand frameVSQ K Unit (fun _ => True) :=
  pairSummandD cRhoHre cRhoHi {cGamHre, cGamHi} poleQ_disj
    (fun _ χ => poleBadQ δF (allPolesQ H t x χ))
    (H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) + polesOfLen * (fW t).length)
    (fun _ χ => (pairQ_bad_card δF (allPolesQ H t x χ)).trans (le_of_eq (allPolesQ_length H t x χ)))
    (fun _ _ χ χ' hχ => by
      dsimp only
      rw [allPolesQ_reads H t x χ χ' (by
        show Quad.mk _ (χ cGamHre) (χ cGamHi) = Quad.mk _ (χ' cGamHre) (χ' cGamHi)
        rw [hχ cGamHre (Finset.mem_insert_self _ _),
          hχ cGamHi (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))])])

theorem cAlphaWQ_not_empty : (⟨13, by decide⟩ : Fin frameVSQ.n) ∉ (∅ : Finset (Fin frameVSQ.n)) :=
  Finset.notMem_empty _

open Classical in
/-- **The walk coin order summand at `frameVSQ`** (coin `αW = χ₁₃`): order `< N`. -/
def orderSQ : BadSummand frameVSQ K Unit (fun _ => True) :=
  VclL.Compute.SummandsQ7.coinSummand ⟨13, by decide⟩ ∅ cAlphaWQ_not_empty
    (fun _ _ => Finset.univ.filter fun a : K => orderOf a < (fW t).length) ((fW t).length * (fW t).length)
    (fun _ _ => orderBad_card _) (fun _ _ _ _ _ => rfl)

/-- The honest summands at `frameVSQ` beyond the 39th's. -/
def honestVSQ : List (BadSummand frameVSQ K Unit (fun _ => True)) := [poleHSQ H t x, orderSQ (K := K) t]

theorem epsilon_honestVSQ :
    epsilonOf (honestVSQ H t x) =
      ((H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) + polesOfLen * (fW t).length : ℕ) : ℚ) /
          (Fintype.card K : ℚ) ^ 2 +
        (((fW t).length * (fW t).length : ℕ) : ℚ) / Fintype.card K := by
  unfold epsilonOf honestVSQ poleHSQ orderSQ pairSummandD VclL.Compute.SummandsQ7.coinSummand
  have h2 : ({cRhoHre, cRhoHi} : Finset (Fin frameVSQ.n)).card = 2 := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Finset.card_singleton, pow_one,
    add_zero, h2]

end SummandsQ

/-! ## 5. Outside the summands, the bad-event hypotheses of `honest_accepted_VSQ_run` hold -/

section DecodeQ
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- **The honest good event at `frameVSQ`**: the three bad-event hypotheses of `honest_accepted_VSQ_run`. -/
def HonestGoodVSQ (χ : Coins frameVSQ K) : Prop :=
  HonestBadFreeVSQ H (claimBinds H.V.claim) χ (rhoVSQ H t χ) (H.yTot (toVCL (toVS χ))) (yHVSQ H χ)
      (mhvH H (bfsRows (airReorder t))) (kLvH H) (vLvH H) (kRvH H) (vRvH H) ∧
    (∀ r < (vsqOf H.V).N, NotBadRow (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ))
      (baseEnvC H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVHQ H.V.basis χ) (pubVHQ δF H.V.basis H.V.claim x (rhoVSQ H t χ) χ) r)) ∧
    (bfsForest [airReorder t]).length ≤ orderOf ((toVS χ) cAlphaW)

theorem honestGoodQ_of_notBad (hN : (vsqOf H.V).N = (bfsForest [airReorder t]).length) (χ : Coins frameVSQ K)
    (h39 : ∀ s ∈ H.bad (C := tableVS hC),
      ¬ s.mem ((fun _ => 0), fun tt => H.trace (toVCL (toVS χ)) tt) (toVCL (toVS χ)))
    (hVS : ∀ s ∈ honestVSQ H t x, ¬ s.mem () χ) : HonestGoodVSQ H t x χ := by
  obtain ⟨hz, h0, h1, h2⟩ := bad_decodeW H (toVCL (toVS χ)) (fun _ => 0) h39
  have hpole : (χ cRhoHre, χ cRhoHi) ∉ poleBadQ δF (allPolesQ H t x χ) := by
    have := hVS (poleHSQ H t x) (by simp [honestVSQ])
    unfold poleHSQ at this
    erw [pairSummandD_mem] at this; exact this
  have hP : ∀ y ∈ allPolesQ H t x χ, rhoHQ δF χ + y ≠ 0 := fun y hy h =>
    hpole ((mem_poleBadQ δF _ _).mpr ⟨y, hy, h⟩)
  have hord : ¬ orderOf (χ ⟨13, by decide⟩) < (fW t).length := by
    have := hVS (orderSQ t) (by simp [honestVSQ])
    unfold orderSQ at this
    erw [VclL.Compute.SummandsQ7.coinSummand_mem] at this
    simpa using this
  refine ⟨⟨hz, h0, h1, h2, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩, fun r hr => ?_,
    Nat.le_of_not_lt hord⟩
  · rw [cell_dRowQ_eq_recDen, recDen_rest]
    refine hP _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ?_, rfl⟩)))
    have hi : (i : ℕ) < H.d.cells.length := by rw [← H.hC0]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · have hw : wTrie H.d.cells H.d.preads i ∈ walkRows H.d.cells H.d.preads :=
      wTrie_mem _ _ (by rw [← H.hW0]; exact i.isLt)
    rw [(walk_dRowQ_honest H χ _ i).1, recDen_rest]
    exact hP _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hw, by simp⟩)))
  · have hw : wTrie H.d.cells H.d.preads i ∈ walkRows H.d.cells H.d.preads :=
      wTrie_mem _ _ (by rw [← H.hW0]; exact i.isLt)
    rw [(walk_dRowQ_honest H χ _ i).2.1, recDenP_rest]
    exact hP _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hw, by simp⟩)))
  · have hw : wTrie H.d.cells H.d.preads i ∈ walkRows H.d.cells H.d.preads :=
      wTrie_mem _ _ (by rw [← H.hW0]; exact i.isLt)
    rw [(walk_dRowQ_honest H χ _ i).2.2, recDenP_rest]
    exact hP _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hw, by simp⟩)))
  · intro y hy
    rw [eCQ_rho]
    refine hP _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, ?_, hy⟩))
    rw [List.mem_range, ← hN]; exact hr

end DecodeQ

/-! ## 6. The completeness bound at VSQ and its Goldilocks figure -/

section BoundQ
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- **The completeness error at VSQ**: the 39th's memory error, the `𝕂′` handle poles (now over
`|𝕂|² = |𝕂′|`) and the walk coin order. -/
def epsCVSQ : ℚ :=
  (1 + 5 * (H.V.memRows (tCW hT hP) : ℚ) + 3 * (H.V.memRows (tWW hT hP) : ℚ)) / (Fintype.card K : ℚ) ^ 2 +
    ((H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) + polesOfLen * (fW t).length : ℕ) : ℚ) /
      (Fintype.card K : ℚ) ^ 2 +
    (((fW t).length * (fW t).length : ℕ) : ℚ) / Fintype.card K

open Classical in
/-- **`vsqCompleteness`: Pr_χ[some honest bad event at VSQ] ≤ ε_c.** -/
theorem vsqCompleteness (hN : (vsqOf H.V).N = (bfsForest [airReorder t]).length) :
    ((Finset.univ.filter fun χ : Coins frameVSQ K => ¬ HonestGoodVSQ H t x χ).card : ℚ) /
      Fintype.card (Coins frameVSQ K) ≤ epsCVSQ H t := by
  set Q39 : Coins frameVCL K → Traces F (tableVS hC) (shapeVW hT hP) :=
    fun χ => ((fun _ => 0), fun tt => H.trace χ tt)
  have hst : TracesStaged frameVCL (tableVS hC) (shapeVW hT hP) Q39 :=
    ⟨stagedCols_const _ _ _, fun tt => trace_stagedW H tt⟩
  set A := Finset.univ.filter fun χ : Coins frameVSQ K =>
    toVCL (toVS χ) ∈ unionEvent (H.bad (C := tableVS hC)) Q39
  set B := unionEvent (honestVSQ H t x) (fun _ : Coins frameVSQ K => ())
  have hsub : (Finset.univ.filter fun χ : Coins frameVSQ K => ¬ HonestGoodVSQ H t x χ) ⊆ A ∪ B := by
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    by_contra hn
    simp only [Finset.mem_union, A, B, Finset.mem_filter, Finset.mem_univ, true_and, unionEvent,
      not_or, not_exists, not_and] at hn
    exact hχ (honestGoodQ_of_notBad H t x hN χ (fun s hs => hn.1 s hs) (fun s hs => hn.2 s hs))
  have hA : (A.card : ℚ) / Fintype.card (Coins frameVSQ K) ≤ epsilonOf (H.bad (C := tableVS hC)) := by
    have h := union_prob_le (H.bad (C := tableVS hC)) Q39 hst
    have hc : A.card = (unionEvent (H.bad (C := tableVS hC)) Q39).card * Fintype.card K ^ 6 :=
      card_toVCLQ_preimage _
    rw [hc, card_coins_VSQ]
    have hK : (0 : ℚ) < (Fintype.card K : ℚ) ^ 6 := by have := Fintype.card_pos (α := K); positivity
    push_cast
    rw [mul_div_mul_right _ _ hK.ne']
    exact h
  have hB : (B.card : ℚ) / Fintype.card (Coins frameVSQ K) ≤ epsilonOf (honestVSQ H t x) :=
    union_prob_le (honestVSQ H t x) (fun _ => ()) trivial
  have hpos : (0 : ℚ) ≤ Fintype.card (Coins frameVSQ K) := by positivity
  calc ((Finset.univ.filter fun χ : Coins frameVSQ K => ¬ HonestGoodVSQ H t x χ).card : ℚ) /
        Fintype.card (Coins frameVSQ K)
      ≤ ((A ∪ B).card : ℚ) / Fintype.card (Coins frameVSQ K) :=
        div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hpos
    _ ≤ (A.card : ℚ) / Fintype.card (Coins frameVSQ K) + (B.card : ℚ) / Fintype.card (Coins frameVSQ K) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_union_le A B) hpos
    _ ≤ epsilonOf (H.bad (C := tableVS hC)) + epsilonOf (honestVSQ H t x) := add_le_add hA hB
    _ = epsCVSQ H t := by rw [epsilon_badW, epsilon_honestVSQ]; unfold epsCVSQ; ring

/-- **The figure**: at `|𝕂| ≥ 2^189` and cell rows, walk rows and compute rows each `≤ 2^31`, the VSQ
completeness error is `< 2^-126` (the walk coin order `N²/|𝕂| ≤ 2^-127` dominates). -/
theorem epsCVSQ_lt (hK : 2 ^ 189 ≤ Fintype.card K) (hnC : H.V.memRows (tCW hT hP) ≤ 2 ^ 31)
    (hnW : H.V.memRows (tWW hT hP) ≤ 2 ^ 31) (hN : (fW t).length ≤ 2 ^ 31) :
    epsCVSQ H t < 1 / 2 ^ 126 := by
  unfold epsCVSQ
  rw [polesOfLen_eq]
  set nC := H.V.memRows (tCW hT hP)
  set nW := H.V.memRows (tWW hT hP)
  set N := (fW t).length
  have hNN : N * N ≤ 2 ^ 62 := by
    have := Nat.mul_le_mul hN hN; norm_num at this ⊢; exact this
  have h2 : nC + 3 * nW + 10 * N ≤ 2 ^ 35 := by omega
  have h2q : ((nC + 3 * nW + 10 * N : ℕ) : ℚ) ≤ 2 ^ 35 := by exact_mod_cast h2
  have h3q : ((N * N : ℕ) : ℚ) ≤ 2 ^ 62 := by exact_mod_cast hNN
  have h1q : (1 + 5 * (nC : ℚ) + 3 * (nW : ℚ)) ≤ 2 ^ 35 := by
    have a : (nC : ℚ) ≤ 2 ^ 31 := by exact_mod_cast hnC
    have b : (nW : ℚ) ≤ 2 ^ 31 := by exact_mod_cast hnW
    linarith
  have k0 : (2 : ℚ) ^ 189 ≤ (Fintype.card K : ℚ) := by exact_mod_cast hK
  have kpos : (0 : ℚ) < 2 ^ 189 := by positivity
  have t1 : (1 + 5 * (nC : ℚ) + 3 * (nW : ℚ)) / (Fintype.card K : ℚ) ^ 2 ≤ 2 ^ 35 / ((2 : ℚ) ^ 189) ^ 2 :=
    div_le_div₀ (by positivity) h1q (by positivity) (pow_le_pow_left₀ kpos.le k0 2)
  have t2 : ((nC + 3 * nW + 10 * N : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 ≤ 2 ^ 35 / ((2 : ℚ) ^ 189) ^ 2 :=
    div_le_div₀ (by positivity) h2q (by positivity) (pow_le_pow_left₀ kpos.le k0 2)
  have t3 : ((N * N : ℕ) : ℚ) / (Fintype.card K : ℚ) ≤ 2 ^ 62 / (2 : ℚ) ^ 189 :=
    div_le_div₀ (by positivity) h3q kpos k0
  calc _ ≤ 2 ^ 35 / ((2 : ℚ) ^ 189) ^ 2 + 2 ^ 35 / ((2 : ℚ) ^ 189) ^ 2 + 2 ^ 62 / (2 : ℚ) ^ 189 := by
        gcongr
    _ < 1 / 2 ^ 126 := by norm_num

/-- **`2^189 ≤ |𝕂|` at Goldilocks**: `|𝕂| = p³`, `p = 2^64 − 2^32 + 1` (`card_K_value`; `goldilocks_prime` is a
theorem). -/
theorem two_pow_189_le_cK : 2 ^ 189 ≤ VclL.Events.cK := by rw [VclL.Events.cK_eq]; norm_num

/-- **The Goldilocks completeness figure at VSQ**: `ε_c < 2^-126` at `|𝕂| = p³` and rows `≤ 2^31`. -/
theorem vsqCompleteness_figure (hK : Fintype.card K = VclL.Events.cK) (hnC : H.V.memRows (tCW hT hP) ≤ 2 ^ 31)
    (hnW : H.V.memRows (tWW hT hP) ≤ 2 ^ 31) (hN : (fW t).length ≤ 2 ^ 31) :
    epsCVSQ H t < 1 / 2 ^ 126 :=
  epsCVSQ_lt H t (hK ▸ two_pow_189_le_cK) hnC hnW hN

/-- **Completeness at VSQ, composed**: for every coin outside the priced honest bad event (probability
`≤ epsCVSQ`), the honest run's messages are accepted at `frameVSQ`. -/
theorem honest_accepted_VSQ_whp
    {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}
    {fuel : ℕ} {subject formula : Noun} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (hm : HonestClaimMsgFull H.d.cells H.V.claim x)
    (hN : (vsqOf H.V).N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective (vsOf H.V).computeNodes) (hadj : (vsOf H.V).AdjacentC)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = H.V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = H.V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = H.V.claim.result)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (χ : Coins frameVSQ K) (hχ : HonestGoodVSQ H t x χ) :
    AcceptsG (vsqOf H.V) (msgVSQ (sumC := sumC) (sumM := sumM) H t x) χ :=
  honest_accepted_VSQ_run H t hrun hd x hm hN hinj hadj hroot hbs hslot (by rw [hd]; rfl) hat χ
    hχ.1 hχ.2.1 hχ.2.2

end BoundQ

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
