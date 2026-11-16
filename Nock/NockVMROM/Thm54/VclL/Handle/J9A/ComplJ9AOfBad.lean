/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AOfBad.lean

* §1 the pin facts of the new families (`famsNew`): side conditions, pins only, pin counts;
  * §2 the J-8 / J-9 B families at `DA` (`famsJA`): `famsOf_facts`, `famsA9_facts`;
  * §3 **`wtA`**, **`figA`** (cost `≤ 2^66` pins + two walk orders of bound `≤ 2^31`);
  * §4 **`stagedA`**: the twin compute trace (round 0 = RAP columns `< 83`, `trX9_pub`), the axis and split
    traces (base columns coin-free, the `𝕂`-roles in round 2), the J-8 tables as in J-9 B.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfComp
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfBad

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins nOrds costL)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A RowsLe31A)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (invPermX9)

noncomputable section

/-! ## 1. The new families -/

section New
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

theorem noOrd_of_allPin(L : List (BadSpec K)) (h : AllPin L) : ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N := by
  intro e he i N hN
  obtain ⟨j, g, rfl⟩ := h e he
  cases hN

theorem allPin_famAXA : AllPin (famAXA δ Rt hgen (K := K)) := by
  unfold famAXA
  split_ifs with h
  · unfold ComplJ9AChipsOK.famAX ComplJ8Bad.ioPoles
    exact allPin_map _ _ fun x => ⟨_, _, rfl⟩
  · intro e he; simp at he

theorem allPin_famSPA : AllPin (famSPA δ Rt hgen (K := K)) := by
  unfold famSPA ComplJ9AChipsOK.famSP
  exact allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩

theorem allPin_compPoles9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (n : ℕ) : AllPin (compPoles9 δ H pd idOf W n (K := K)) := by
  unfold compPoles9
  exact allPin_flatMap _ _ fun j _ => allPin_flatMap _ _ fun S _ => (slotPoles_len δ S _).2

theorem length_compPoles9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (n : ℕ) : (compPoles9 δ H pd idOf W n (K := K)).length ≤ n * 12 := by
  unfold compPoles9
  refine (ComplJ8Of.length_flatMap_le _ _ 12 fun j _ => ?_).trans (by simp)
  refine (ComplJ8Of.length_flatMap_le _ _ 3 fun S _ => (slotPoles_len δ S _).1).trans ?_
  have := ChipHX9.slotsX9_length (F := ZMod p)
  omega

theorem famsNew_OK : ∀ L ∈ famsNew δ Rt hgen (K := K), ∀ e ∈ L, e.OK := by
  intro L hL e he
  simp only [famsNew, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl
  · unfold famAXA at he
    split_ifs at he with h
    · exact ComplJ9AChipsOK.famAX_OK δ _ _ _ e he
    · simp at he
  · exact ComplJ9AChipsOK.famSP_OK δ _ _ e he
  · unfold compPoles9 at he
    simp only [List.mem_flatMap] at he
    obtain ⟨j, -, S, -, hs⟩ := he
    exact ComplJ8CompPole.slotPoles_OK δ S _ e hs

theorem nPins_famsNew (hX : nXA (p := p) Rt hgen ≤ 2 ^ 31)
    (hS : nSA (p := p) (t := t) ≤ 2 ^ 31) (hN : N9 t ≤ 2 ^ 31) :
    ((famsNew δ Rt hgen (K := K)).map nPins).sum ≤ 17 * 2 ^ 31 := by
  have h1 : nPins (famAXA δ Rt hgen (K := K)) ≤ 3 * nXA (p := p) Rt hgen := by
    refine (nPins_le_length _).trans ?_
    unfold famAXA
    split_ifs with h
    · rw [ComplJ9AChipsOK.famAX_length]
    · simp
  have h2 : nPins (famSPA δ Rt hgen (K := K)) ≤ 2 * nSA (p := p) (t := t) := by
    refine (nPins_le_length _).trans ?_
    unfold famSPA
    rw [ComplJ9AChipsOK.famSP_length]
  have h3 := (nPins_le_length (compPoles9 δ (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (N9 t) (K := K))).trans
    (length_compPoles9 δ _ _ _ _ _)
  simp only [famsNew, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have : N9 t * 12 ≤ 2 ^ 31 * 12 := Nat.mul_le_mul_right _ hN
  omega

end New

/-! ## 2. The run: `wt`, `fig`, `staged` -/

section Run
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (badList_OK badList_counts badList_ord_mem nOrds_eq_zero costL_le
  cost_div_lt sum_w_badOf)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen

theorem mem_N9 : N9 t ∈ sizesA (DA) := by
  unfold sizesA; exact List.mem_append_right _ (List.mem_cons_self ..)

theorem mem_nXA : nXA (p := p) Rt hgen ∈ sizesA (DA) := by
  unfold sizesA; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem mem_nSA : nSA (p := p) (t := t) ∈ sizesA (DA) := by
  unfold sizesA
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem famsJA_facts :
    (∀ L ∈ famsJA δ b Rt hgen hpG h31A (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsJA δ b Rt hgen hpG h31A (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsJA δ b Rt hgen hpG h31A (K := K)).map nPins).sum ≤ 2 ^ 40 + 1 + 15 * 2 ^ 31 := by
  have h31 : ∀ x ∈ sizesJ8 (DA), x ≤ 2 ^ 31 := h31_run Rt hgen h31A
  obtain ⟨o1, p1, c1⟩ := famsOf_facts δ b (K := K) (DA) (hF_run Rt hgen hpG h31A)
    (ComplJ9ADataRec.cellsA_pos Rt hgen) h31
  obtain ⟨o2, p2, c2⟩ := ComplJ9BOf.famsA9_facts δ b (K := K) (DA) (DA) (hF_run Rt hgen hpG h31A)
    (ComplJ9ADataRec.acsA_pos Rt hgen)
  have hacs := h31 _ (show (DA).acs.length ∈ sizesJ8 (DA) by simp [sizesJ8])
  have hnV := h31 _ (show nVOf (DA) ∈ sizesJ8 (DA) by simp [sizesJ8])
  refine ⟨fun L hL => ?_, fun L hL => ?_, ?_⟩
  · rcases List.mem_append.mp hL with h | h
    exacts [o1 L h, o2 L h]
  · rcases List.mem_append.mp hL with h | h
    exacts [p1 L h, p2 L h]
  · show ((famsOf δ b (DA) (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen) ++
      ComplJ9BOf.famsA9 δ b (DA) (DA) (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen)).map nPins).sum ≤ _
    rw [List.map_append, List.sum_append]
    omega

theorem facts_all :
    (∀ L ∈ famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen (K := K)).map nPins).sum ≤ 2 ^ 66 := by
  obtain ⟨o1, p1, c1⟩ := famsJA_facts δ b Rt hgen hpG h31A (K := K)
  have hX : nXA (p := p) Rt hgen ≤ 2 ^ 31 := h31A _ (mem_nXA Rt hgen)
  have hS : nSA (p := p) (t := t) ≤ 2 ^ 31 := h31A _ (mem_nSA Rt hgen)
  have hN : N9 t ≤ 2 ^ 31 := h31A _ (mem_N9 Rt hgen)
  have c2 := nPins_famsNew δ Rt hgen (K := K) hX hS hN
  have pN : ∀ L ∈ famsNew δ Rt hgen (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N := by
    intro L hL
    simp only [famsNew, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact noOrd_of_allPin _ (allPin_famAXA δ Rt hgen)
    · exact noOrd_of_allPin _ (allPin_famSPA δ Rt hgen)
    · exact noOrd_of_allPin _ (allPin_compPoles9 δ _ _ _ _ _)
  refine ⟨fun L hL => ?_, fun L hL => ?_, ?_⟩
  · rcases List.mem_append.mp hL with h | h
    exacts [o1 L h, famsNew_OK δ Rt hgen L h]
  · rcases List.mem_append.mp hL with h | h
    exacts [p1 L h, pN L h]
  · rw [List.map_append, List.sum_append]
    have e40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
    have e31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
    have e66 : (2 : ℕ) ^ 66 = 73786976294838206464 := by norm_num
    rw [e40, e31] at c1; rw [e31] at c2; rw [e66]
    omega

/-- **`wt` at `BA`.** -/
theorem wtA : ∀ e ∈ (BRun9A δ b Rt hgen hpG h31A).bad,
    (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2 :=
  ComplJ8Bad.wt_badOf _ (badList_OK _ _ (facts_all δ b Rt hgen hpG h31A (K := K)).1)

/-- **`fig` at `BA`.** -/
theorem figA : p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK →
    RowsLe31A (BRun9A δ b Rt hgen hpG h31A).Pb → (BRun9A δ b Rt hgen hpG h31A).epsC < 1 / 2 ^ 120 := by
  intro _ hK _
  obtain ⟨o, pn, c⟩ := facts_all δ b Rt hgen hpG h31A (K := K)
  have e : (BRun9A δ b Rt hgen hpG h31A).epsC = (costL (badSA δ b Rt hgen hpG h31A) : ℚ) / Fintype.card K :=
    sum_w_badOf _
  rw [e]
  refine cost_div_lt _ ?_ hK
  have h0 : ∀ L ∈ famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen (K := K), nOrds L = 0 :=
    fun L hL => nOrds_eq_zero L (pn L hL)
  have hN8 : N8 (p := p) Rt hgen ≤ 2 ^ 31 := h31A _ (List.mem_append_left _ (by simp [sizesJ8]))
  have hN9 : N9 t ≤ 2 ^ 31 := h31A _ (mem_N9 Rt hgen)
  have hcnt := badList_counts [(⟨13, by decide⟩, N8 (p := p) Rt hgen), (⟨13, by decide⟩, N9 t)]
    (famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen (K := K)) h0
  have hM : ∀ i N, BadSpec.ord i N ∈ badSA δ b Rt hgen hpG h31A → N ≤ 2 ^ 31 := by
    intro i N hm
    have := badList_ord_mem _ _ pn i N hm
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at this
    rcases this with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have hc := costL_le (badSA δ b Rt hgen hpG h31A) (2 ^ 31) hM
  have hp : nPins (badSA δ b Rt hgen hpG h31A) ≤ 2 ^ 66 := hcnt.1 ▸ c
  have ho : nOrds (badSA δ b Rt hgen hpG h31A) = 2 := by
    exact hcnt.2
  rw [ho] at hc
  have e63 : (2 : ℕ) ^ 31 * 2 ^ 31 = 2 ^ 62 := by norm_num
  have e68 : (2 : ℕ) ^ 68 = 295147905179352825856 := by norm_num
  have e66 : (2 : ℕ) ^ 66 = 73786976294838206464 := by norm_num
  have e62 : (2 : ℕ) ^ 62 = 4611686018427387904 := by norm_num
  rw [e63] at hc
  omega

/-! ### Staging -/

open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage (zero_of_one all_of_two chalVJ8_agree)

/-- The twin trace reads no public vector. -/
theorem trX9_pubA (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (chalV pub1 pub2 : ℕ → ZMod p) (ln cnt acc : ℕ → K) (j c : ℕ) :
    HonestTraceX9.trX9 b δ H pd idOf W chalV pub1 ln cnt acc j c =
      HonestTraceX9.trX9 b δ H pd idOf W chalV pub2 ln cnt acc j c := by
  unfold HonestTraceX9.trX9
  simp only [ComplJ9AOfComp.preT9_pub b δ H pd idOf W chalV pub1 pub2,
    ComplJ9AOfComp.accV9_pub b δ H pd idOf W chalV pub1 pub2]

theorem stC_A : StagedCols frameJ8 crC9
    (fun χ => trCA δ b Rt hgen χ (PbA Rt hgen hpG h31A).nodes) := by
  intro j χ χ' h
  simp only [trCA_def]
  unfold HonestTraceX9.polyX9
  refine congrArg (fun f => Lagrange.interpolate Finset.univ _ f) (funext fun i => ?_)
  by_cases hj : (j : ℕ) < 83
  · have hr : HonestTraceX9.r0 (invPermX9 (j : ℕ)) = true := by
      rw [HonestTraceX9.r0_iff]; simp only [invPermX9]; split_ifs <;> omega
    rw [HonestTraceX9.trX9_base _ _ _ _ _ _ _ _ _ _ _ _ _ hr, HonestTraceX9.trX9_base _ _ _ _ _ _ _ _ _ _ _ _ _ hr]
  · have h0 := zero_of_one χ χ' (crC9 j) (by simp [crC9, hj]) h
    have hcv := chalVJ8_agree b χ χ' h0
    have hα : αA b χ = αA b χ' := by
      simp only [αA]; rw [InhabJ8Comp.αC0_eq, InhabJ8Comp.αC0_eq, h0 _ rfl]
    have hγ : γA b χ = γA b χ' := by
      simp only [γA]; rw [InhabJ8Comp.γC0_eq, InhabJ8Comp.γC0_eq, h0 _ rfl]
    have hn : nodeVA b Rt hgen χ = nodeVA b Rt hgen χ' := by
      simp only [nodeVA, hγ]
    rw [trX9_pubA δ b _ _ _ _ _ (pubCA δ b Rt hgen χ) (pubCA δ b Rt hgen χ'), hcv, hα, hn]

theorem stX_A : StagedCols frameJ8 crAX (fun χ => trXA δ b Rt hgen hpG h31A χ) := by
  intro j χ χ' h
  by_cases hj : (j : ℕ) < 22
  · unfold trXA
    split_ifs with hax
    · unfold ComplJ9AAxisH.polyAx
      refine Chips.ChipRAP.honestQ_congr _ _ _ _ _ _ ?_
      funext i
      simp only [ComplJ9AAxisH.colAx, hj, if_true]
    · rfl
  · have := all_of_two χ χ' (crAX j) (by simp [crAX, hj]) h
    subst this; rfl

theorem stS_A : StagedCols frameJ8 crSP (fun χ => trSA δ b Rt hgen hpG h31A χ) := by
  intro j χ χ' h
  by_cases hj : (j : ℕ) < 72
  · unfold trSA
    split_ifs with hsp
    · show Lagrange.interpolate _ _ _ = Lagrange.interpolate _ _ _
      refine congrArg (fun f => Lagrange.interpolate Finset.univ _ f) (funext fun i => ?_)
      simp only [ComplJ9ASplitH.colS, hj, if_true]
    · rfl
  · have := all_of_two χ χ' (crSP j) (by simp [crSP, hj]) h
    subst this; rfl

/-- **`staged` at `BA`.** -/
theorem stagedA : StJ9A (BRun9A δ b Rt hgen hpG h31A).tr := by
  have hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) →
      encR δ χ = encR δ χ' := fun χ χ' h =>
    encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide)) (h FrameJ8.cY1 (by decide))
      (h FrameJ8.cY2 (by decide))
  refine ⟨stC_A δ b Rt hgen hpG h31A, ?_, ?_, ?_, ?_, ?_, stX_A δ b Rt hgen hpG h31A, stS_A δ b Rt hgen hpG h31A⟩
  · exact ComplJ8Enc.cellTrME_staged δ b (ComplJ9ADataRec.cellsA_pos Rt hgen) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz
  · exact ComplJ8Enc.walkTrWE_staged δ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz
  · exact ComplJ8Jet.stJ δ b _ _ _ (fun χ => rfl)
  · exact ComplJ8Of.stA_run δ b (DA) _ _
  · exact ComplJ9BBalF.stV_run9 δ b (DA) _

end Run

end

#print axioms wtA
#print axioms figA
#print axioms stagedA

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfBad
