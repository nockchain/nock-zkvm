/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestEpsVS.lean

The honest bad events of `honest_accepted_VS_run` are priced and summed:
  * the 39th's seed / key-pole events at the first eleven coins (`HonestVCLW.bad`, `epsilon_badW`:
    `(1 + 5·n_C + 3·n_W)/|𝕂|²`), lifted to `frameVS` through the uniform fibres of `toVCL`
    (`card_toVCL_preimage`);
  * ONE pole summand on the handle pole coin `ρH` (dep `{γH}`): every cell row's handle-export record
    (`n_C`), every walk row's three records (`3·n_W`) and every compute row's `polesOf` (`polesOfLen·N`),
    weight `n_C + 3·n_W + polesOfLen·N` over `|𝕂|` (`den_bad_card`);
  * the walk coin order on `αW` (`walk_coin_order_few`): weight `N²` over `|𝕂|`.
  `honestGood_of_notBad` decodes "outside every honest summand" into exactly the three bad-event hypotheses
  of `honest_accepted_VS_run` (`HonestBadFreeVSB`, `NotBadRow`, the order); `vsCompleteness` is the bound
  `Pr_χ[some honest bad event] ≤ ε_c`, and `honest_accepted_VS_whp` the composition.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestVS
import Nock.NockVMROM.Thm54.VclL.Handle.WalkCoin

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The fibres of `toVCL` -/

section Fibre
variable {K : Type} [Fintype K] [DecidableEq K]

/-- `frameVS`'s coins split as `frameVCL`'s eleven and the four VS coins. -/
def splitVS : Coins frameVS K ≃ Coins frameVCL K × (Fin 4 → K) where
  toFun χ := (toVCL χ, fun k => χ ⟨11 + k, by have := k.isLt; change 11 + (k : ℕ) < 15; omega⟩)
  invFun p := fun i => if h : (i : ℕ) < 11 then p.1 ⟨i, h⟩
    else p.2 ⟨i - 11, by have := i.isLt; change (i : ℕ) < 15 at this; omega⟩
  left_inv χ := by
    funext i
    by_cases h : (i : ℕ) < 11
    · simp only [dif_pos h]; rfl
    · simp only [dif_neg h]; congr 1; apply Fin.ext; simp; omega
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext i; simp only [toVCL]; rw [dif_pos (by exact i.isLt)]
    · funext k; simp only; rw [dif_neg (by omega)]; congr 1; apply Fin.ext; simp

/-- **The uniform fibres of `toVCL`.** -/
theorem card_toVCL_preimage (S : Finset (Coins frameVCL K)) :
    (Finset.univ.filter fun χ : Coins frameVS K => toVCL χ ∈ S).card = S.card * Fintype.card K ^ 4 := by
  have h : (Finset.univ.filter fun χ : Coins frameVS K => toVCL χ ∈ S) =
      (S ×ˢ (Finset.univ : Finset (Fin 4 → K))).map splitVS.symm.toEmbedding := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_product,
      Equiv.coe_toEmbedding]
    constructor
    · intro hχ; exact ⟨splitVS χ, ⟨hχ, trivial⟩, splitVS.symm_apply_apply χ⟩
    · rintro ⟨p, ⟨hp, -⟩, rfl⟩
      have : toVCL (splitVS.symm p) = p.1 := congrArg Prod.fst (splitVS.apply_symm_apply p)
      rw [this]; exact hp
  rw [h, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

theorem card_coins_VS : Fintype.card (Coins frameVS K) = Fintype.card (Coins frameVCL K) * Fintype.card K ^ 4 := by
  rw [Fintype.card_congr splitVS, Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin]

end Fibre

/-! ## 2. Record denominators as `ρ + rest` -/

section Rest
variable {F L : Type} [Field F] [Field L] [Algebra F L]

def recRest (γ : L) (k : F × (F × F) × (F × F)) : L := recDen 0 γ k
def recRestP (γ : L) (k : F × F × (F × F)) : L := recDenP 0 γ k

theorem recDen_rest (ρ γ : L) (k : F × (F × F) × (F × F)) : recDen ρ γ k = ρ + recRest γ k := by
  unfold recRest recDen; ring
theorem recDenP_rest (ρ γ : L) (k : F × F × (F × F)) : recDenP ρ γ k = ρ + recRestP γ k := by
  unfold recRestP recDenP; ring

end Rest

/-! ## 3. The pole lists and the honest summands -/

section Poles
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]

/-- The number of records a compute row's three slots can consume (`polesOf`'s length, row-independent). -/
def polesOfLen : ℕ := ((ChipH.slots : List (ChipH.SlotSpec ℚ)).map fun S =>
  S.ents.length + (match S.pair with | some _ => 2 | none => 0)).sum

theorem polesOfLen_eq : polesOfLen = 10 := by decide

theorem polesOf_length (eK : Env K) (eF : Env F) : (polesOf eK eF).length = polesOfLen := by
  unfold polesOf polesOfLen ChipH.slots
  simp only [List.length_flatMap, List.length_append, List.length_map, List.map_cons, List.map_nil]
  congr 1

end Poles

section Summands
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- The base environment of compute row `r` of the honest run at the coins `χ`. -/
def eFr (χ : Coins frameVS K) (r : ℕ) : Env F :=
  baseEnvC H.d.cells (wRows (fW t)) (fW t).length (chalVH H.V.basis χ)
    (pubVH δF H.V.basis H.V.claim x (rhoVS H t χ) χ) r

/-- **Every record denominator of the honest run, minus the pole coin** (cell rows, walk rows, compute
rows), at the handle coin `γH`. -/
def allPoles (χ : Coins frameVS K) : List K :=
  H.d.cells.map (fun n => recRest (χ cGamH) (expKey (F := F) H.d.cells n)) ++
  (walkRows H.d.cells H.d.preads).flatMap (fun w =>
    [recRest (χ cGamH) (expKey (F := F) H.d.cells w.label.node),
     recRestP (χ cGamH) (Handle.recLH (F := F) H.d.cells w.label),
     recRestP (χ cGamH) (Handle.recRH (F := F) H.d.cells w.label)]) ++
  (List.range (fW t).length).flatMap (fun r => polesOf (gE H.V.basis (eFr H t x χ r)) (eFr H t x χ r))

theorem allPoles_length (χ : Coins frameVS K) :
    (allPoles H t x χ).length = H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) +
      polesOfLen * (fW t).length := by
  unfold allPoles
  simp only [List.length_append, List.length_map, List.length_flatMap, List.length_cons, List.length_nil,
    polesOf_length, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  rw [H.hC0, H.hW0]
  ring

theorem allPoles_reads (χ χ' : Coins frameVS K) (h : χ cGamH = χ' cGamH) :
    allPoles H t x χ = allPoles H t x χ' := by
  unfold allPoles
  rw [h]
  congr 1
  refine List.flatMap_congr fun r _ => polesOf_congr _ _ _ _ (fun c _ => rfl) ?_
  show limbVal H.V.basis (chalVH H.V.basis χ) ChipH.chalGammaL = limbVal H.V.basis (chalVH H.V.basis χ') ChipH.chalGammaL
  rw [limb_gammaL, limb_gammaL, h]

theorem cGamH_not_rho : cRhoH ∉ ({cGamH} : Finset (Fin frameVS.n)) := by decide

open Classical in
/-- **The handle pole summand** (coin `ρH`, dep `{γH}`): `ρH` hits one of the honest run's record
denominators. -/
def poleHS : BadSummand frameVS K Unit (fun _ => True) :=
  VclL.Compute.SummandsQ7.coinSummand cRhoH {cGamH} cGamH_not_rho
    (fun _ χ => Finset.univ.filter fun ρ : K => ∃ y ∈ allPoles H t x χ, ρ + y = 0)
    (H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) + polesOfLen * (fW t).length)
    (fun _ χ => (den_bad_card _).trans (le_of_eq (allPoles_length H t x χ)))
    (fun _ _ χ χ' hχ => by dsimp only; rw [allPoles_reads H t x χ χ' (hχ cGamH (Finset.mem_singleton_self _))])

theorem cAlphaW_not_empty : cAlphaW ∉ (∅ : Finset (Fin frameVS.n)) := Finset.notMem_empty _

open Classical in
theorem orderBad_card (N : ℕ) : (Finset.univ.filter fun a : K => orderOf a < N).card ≤ N * N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨B, hB, hBo⟩ := walk_coin_order_few (K := K) N hN
  refine le_trans (Finset.card_le_card fun a ha => ?_) hB
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  by_contra hn
  exact absurd (hBo a hn) (by omega)

open Classical in
/-- **The walk coin order summand** (coin `αW`): `αW` has order `< N`. -/
def orderS : BadSummand frameVS K Unit (fun _ => True) :=
  VclL.Compute.SummandsQ7.coinSummand cAlphaW ∅ cAlphaW_not_empty
    (fun _ _ => Finset.univ.filter fun a : K => orderOf a < (fW t).length) ((fW t).length * (fW t).length)
    (fun _ _ => orderBad_card _) (fun _ _ _ _ _ => rfl)

/-- The honest summands at `frameVS` beyond the 39th's. -/
def honestVS : List (BadSummand frameVS K Unit (fun _ => True)) := [poleHS H t x, orderS (K := K) t]

theorem epsilon_honestVS :
    epsilonOf (honestVS H t x) = ((H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) +
      polesOfLen * (fW t).length + (fW t).length * (fW t).length : ℕ) : ℚ) / Fintype.card K := by
  unfold epsilonOf honestVS poleHS orderS VclL.Compute.SummandsQ7.coinSummand
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Finset.card_singleton, pow_one,
    add_zero]
  push_cast
  ring

end Summands

/-! ## 4. Outside the summands, the hypotheses of `honest_accepted_VS_run` hold -/

section Decode
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- The three bad-event hypotheses of `honest_accepted_VS_run`. -/
def HonestGoodVS (χ : Coins frameVS K) : Prop :=
  HonestBadFreeVSB H (claimBinds H.V.claim) χ (rhoVS H t χ) (H.yTot (toVCL χ)) (yHVS H χ)
      (mhvH H (bfsRows (airReorder t))) (kLvH H) (vLvH H) (kRvH H) (vRvH H) ∧
    (∀ r < (vsOf H.V).N, NotBadRow (gE (vsOf H.V).basis (baseEnvC H.d.cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVH (vsOf H.V).basis χ)
        (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x (rhoVS H t χ) χ) r))
      (baseEnvC H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH (vsOf H.V).basis χ) (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x (rhoVS H t χ) χ) r)) ∧
    (bfsForest [airReorder t]).length ≤ orderOf (χ cAlphaW)

/-- **Decoding**: outside the 39th's summands (at `toVCL χ`) and the two VS summands, the three bad-event
hypotheses hold. -/
theorem honestGood_of_notBad (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length) (χ : Coins frameVS K)
    (h39 : ∀ s ∈ H.bad (C := tableVS hC), ¬ s.mem ((fun _ => 0), fun tt => H.trace (toVCL χ) tt) (toVCL χ))
    (hVS : ∀ s ∈ honestVS H t x, ¬ s.mem () χ) : HonestGoodVS H t x χ := by
  obtain ⟨hz, h0, h1, h2⟩ := bad_decodeW H (toVCL χ) (fun _ => 0) h39
  have hpole : χ cRhoH ∉ Finset.univ.filter fun ρ : K => ∃ y ∈ allPoles H t x χ, ρ + y = 0 := by
    have := hVS (poleHS H t x) (by simp [honestVS])
    unfold poleHS at this
    erw [VclL.Compute.SummandsQ7.coinSummand_mem] at this
    exact this
  have hP : ∀ y ∈ allPoles H t x χ, χ cRhoH + y ≠ 0 := fun y hy => den_ne_zero_of_not_bad _ hy hpole
  have hord : ¬ orderOf (χ cAlphaW) < (fW t).length := by
    have := hVS (orderS t) (by simp [honestVS])
    unfold orderS at this
    erw [VclL.Compute.SummandsQ7.coinSummand_mem] at this
    simpa using this
  refine ⟨⟨hz, h0, h1, h2, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩, fun r hr => ?_, Nat.le_of_not_lt hord⟩
  · rw [cell_dRow_eq_recDen, recDen_rest]
    refine hP _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ?_, rfl⟩)))
    have hi : (i : ℕ) < H.d.cells.length := by rw [← H.hC0]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · have hw : wTrie H.d.cells H.d.preads i ∈ walkRows H.d.cells H.d.preads :=
      wTrie_mem _ _ (by rw [← H.hW0]; exact i.isLt)
    rw [(walk_dRow_honest H χ _ i).1, recDen_rest]
    exact hP _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hw, by simp⟩)))
  · have hw : wTrie H.d.cells H.d.preads i ∈ walkRows H.d.cells H.d.preads :=
      wTrie_mem _ _ (by rw [← H.hW0]; exact i.isLt)
    rw [(walk_dRow_honest H χ _ i).2.1, recDenP_rest]
    exact hP _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hw, by simp⟩)))
  · have hw : wTrie H.d.cells H.d.preads i ∈ walkRows H.d.cells H.d.preads :=
      wTrie_mem _ _ (by rw [← H.hW0]; exact i.isLt)
    rw [(walk_dRow_honest H χ _ i).2.2, recDenP_rest]
    exact hP _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hw, by simp⟩)))
  · intro y hy
    have hrho : (gE (vsOf H.V).basis (baseEnvC H.d.cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVH (vsOf H.V).basis χ)
        (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x (rhoVS H t χ) χ) r)).chal ChipH.chalRhoL = χ cRhoH :=
      limb_rhoL H.V.basis χ
    rw [hrho]
    refine hP _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, ?_, hy⟩))
    rw [List.mem_range, ← hN]; exact hr

end Decode

/-! ## 5. The completeness bound -/

section Bound
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- The completeness error at VS: the 39th's memory error plus the handle poles and the walk coin order. -/
def epsCVS : ℚ :=
  (1 + 5 * (H.V.memRows (tCW hT hP) : ℚ) + 3 * (H.V.memRows (tWW hT hP) : ℚ)) / (Fintype.card K : ℚ) ^ 2 +
    ((H.V.memRows (tCW hT hP) + 3 * H.V.memRows (tWW hT hP) + polesOfLen * (fW t).length +
      (fW t).length * (fW t).length : ℕ) : ℚ) / Fintype.card K

open Classical in
/-- **`vsCompleteness`: Pr_χ[some honest bad event at VS] ≤ ε_c.** -/
theorem vsCompleteness (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length) :
    ((Finset.univ.filter fun χ : Coins frameVS K => ¬ HonestGoodVS H t x χ).card : ℚ) /
      Fintype.card (Coins frameVS K) ≤ epsCVS H t := by
  set Q39 : Coins frameVCL K → Traces F (tableVS hC) (shapeVW hT hP) :=
    fun χ => ((fun _ => 0), fun tt => H.trace χ tt)
  have hst : TracesStaged frameVCL (tableVS hC) (shapeVW hT hP) Q39 :=
    ⟨stagedCols_const _ _ _, fun tt => trace_stagedW H tt⟩
  set A := Finset.univ.filter fun χ : Coins frameVS K => toVCL χ ∈ unionEvent (H.bad (C := tableVS hC)) Q39
  set B := unionEvent (honestVS H t x) (fun _ : Coins frameVS K => ())
  have hsub : (Finset.univ.filter fun χ : Coins frameVS K => ¬ HonestGoodVS H t x χ) ⊆ A ∪ B := by
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    by_contra hn
    simp only [Finset.mem_union, A, B, Finset.mem_filter, Finset.mem_univ, true_and, unionEvent,
      not_or, not_exists, not_and] at hn
    exact hχ (honestGood_of_notBad H t x hN χ (fun s hs => hn.1 s hs) (fun s hs => hn.2 s hs))
  have hA : (A.card : ℚ) / Fintype.card (Coins frameVS K) ≤ epsilonOf (H.bad (C := tableVS hC)) := by
    have h := union_prob_le (H.bad (C := tableVS hC)) Q39 hst
    have hc : A.card = (unionEvent (H.bad (C := tableVS hC)) Q39).card * Fintype.card K ^ 4 :=
      card_toVCL_preimage _
    rw [hc, card_coins_VS]
    have hK : (0 : ℚ) < (Fintype.card K : ℚ) ^ 4 := by have := Fintype.card_pos (α := K); positivity
    push_cast
    rw [mul_div_mul_right _ _ hK.ne']
    exact h
  have hB : (B.card : ℚ) / Fintype.card (Coins frameVS K) ≤ epsilonOf (honestVS H t x) :=
    union_prob_le (honestVS H t x) (fun _ => ()) trivial
  have hpos : (0 : ℚ) ≤ Fintype.card (Coins frameVS K) := by positivity
  calc ((Finset.univ.filter fun χ : Coins frameVS K => ¬ HonestGoodVS H t x χ).card : ℚ) /
        Fintype.card (Coins frameVS K)
      ≤ ((A ∪ B).card : ℚ) / Fintype.card (Coins frameVS K) :=
        div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hpos
    _ ≤ (A.card : ℚ) / Fintype.card (Coins frameVS K) + (B.card : ℚ) / Fintype.card (Coins frameVS K) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_union_le A B) hpos
    _ ≤ epsilonOf (H.bad (C := tableVS hC)) + epsilonOf (honestVS H t x) := add_le_add hA hB
    _ = epsCVS H t := by rw [epsilon_badW, epsilon_honestVS]; rfl

/-- **The figure**: at `|𝕂| ≥ 2^189` (Goldilocks cubic) and cell rows, walk rows and compute rows each
`≤ 2^31`, the VS completeness error is `< 2^-120`. -/
theorem epsCVS_lt (hK : 2 ^ 189 ≤ Fintype.card K) (hnC : H.V.memRows (tCW hT hP) ≤ 2 ^ 31)
    (hnW : H.V.memRows (tWW hT hP) ≤ 2 ^ 31) (hN : (fW t).length ≤ 2 ^ 31) :
    epsCVS H t < 1 / 2 ^ 120 := by
  unfold epsCVS
  rw [polesOfLen_eq]
  set nC := H.V.memRows (tCW hT hP)
  set nW := H.V.memRows (tWW hT hP)
  set N := (fW t).length
  have hNN : N * N ≤ 2 ^ 62 := by
    have := Nat.mul_le_mul hN hN; norm_num at this ⊢; exact this
  have h2 : nC + 3 * nW + 10 * N + N * N ≤ 2 ^ 63 := by omega
  have h2q : ((nC + 3 * nW + 10 * N + N * N : ℕ) : ℚ) ≤ 2 ^ 63 := by exact_mod_cast h2
  have h1q : (1 + 5 * (nC : ℚ) + 3 * (nW : ℚ)) ≤ 2 ^ 35 := by
    have a : (nC : ℚ) ≤ 2 ^ 31 := by exact_mod_cast hnC
    have b : (nW : ℚ) ≤ 2 ^ 31 := by exact_mod_cast hnW
    linarith
  have k0 : (2 : ℚ) ^ 189 ≤ (Fintype.card K : ℚ) := by exact_mod_cast hK
  have kpos : (0 : ℚ) < 2 ^ 189 := by positivity
  have t1 : (1 + 5 * (nC : ℚ) + 3 * (nW : ℚ)) / (Fintype.card K : ℚ) ^ 2 ≤ 2 ^ 35 / ((2 : ℚ) ^ 189) ^ 2 :=
    div_le_div₀ (by positivity) h1q (by positivity) (pow_le_pow_left₀ kpos.le k0 2)
  have t2 : ((nC + 3 * nW + 10 * N + N * N : ℕ) : ℚ) / (Fintype.card K : ℚ) ≤ 2 ^ 63 / (2 : ℚ) ^ 189 :=
    div_le_div₀ (by positivity) h2q kpos k0
  calc _ ≤ 2 ^ 35 / ((2 : ℚ) ^ 189) ^ 2 + 2 ^ 63 / (2 : ℚ) ^ 189 := add_le_add t1 t2
    _ < 1 / 2 ^ 120 := by norm_num

/-- **Completeness at VS, composed**: for every coin outside the priced honest bad event (probability
`≤ epsCVS`, `vsCompleteness`), the honest run's messages are accepted at `frameVS`. -/
theorem honest_accepted_VS_whp
    {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}
    {fuel : ℕ} {subject formula : Noun} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (hm : HonestClaimMsgFull H.d.cells H.V.claim x)
    (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective (vsOf H.V).computeNodes) (hadj : (vsOf H.V).AdjacentC)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = H.V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = H.V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = H.V.claim.result)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (χ : Coins frameVS K) (hχ : HonestGoodVS H t x χ) :
    AcceptsG (vsOf H.V) (msgVS (sumC := sumC) (sumM := sumM) H t x) χ :=
  honest_accepted_VS_run H hrun hd x hm hN hinj hadj hroot hbs hslot (by rw [hd]; rfl) hat χ hχ.1 hχ.2.1 hχ.2.2

end Bound

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
