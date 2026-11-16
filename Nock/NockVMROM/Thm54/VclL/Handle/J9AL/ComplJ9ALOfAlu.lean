/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALOfAlu.lean

  **J-9 AL completeness: the ALU field, the weights, the figure and the staging of the mixed
  record `ComplJ9ALRun`.**

  * §1 **`hALk_run`**: at every coin outside `badAL`, the ALU field `ALChipOK` of `AcceptsJ9AL` holds at the
    record's layout, message and trace (from `AluSatRun.aluSZChipJ9_sat_run`; `hblk` discharged by
    `AluSatBlock.blockBaseSat_G` / `blockIdentSat_G`).
  * §2 `famsJL_facts` (the twin of `ComplJ9AOfBad.famsJA_facts` at `DL`), `costL_badSA`, **`wtAL`**, `epsAL`,
    **`figAL`** (`< 2^-120` by margin: cost `≤ 2^66 + 2^63 + (2^40 + 1 + 15·2^31) + 5·(2^31 + 1) ≤ 2^68`).
  * §3 **`stagedAL : StJ9AL trAL`**: J-9 A's C/W/V/X/S columns, the C/J/A columns of `B8L` (as `stagedA`), and the
    ALU columns (base `0..93` coin-free by `tbR_fst`; round 1 reads only `yOf`; round 2 free).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALOfAlu

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins nOrds costL)
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg (preLOf)
open Nock.NockVMROM.Thm54.VclL.Handle.AluPoles (yOf famAL)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun
open Nock.Jet.Prim (PrimOp primSpec)

noncomputable section

section Alu
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp)) (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => ComplJ9ALData.j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
local notation "PL" => ComplJ9ALRun.PbL δ b Rt hgen prims hpG h31A h31

/-! ## 1. The ALU field -/

/-- **The ALU field at every coin outside `badAL`** (`AcceptsJ9AL.hALk` at the record).  Binders beyond the
record's: `h31L` (the ALU size), the registry facts `hnd hprim`, and the disclosed `hnoDec hlimb`. -/
theorem hALk_run (h31L : Rows31AL (K := K) δ Rt hgen prims)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t)
    (χ : Coins frameJ8 K) (hχ : ∀ e ∈ badAL δ b Rt hgen prims hpG h31A h31, χ ∉ e.1) :
    AcceptsJ9AL.ALChipOK δ b (PL).aluOn (PL).prims (PL).hnL (PL).nodesL (PL).orbitL (PL).preL (chalsALJ8 δ χ)
      (MAL δ b Rt hgen prims hpG h31A h31 χ).pubsL
      (RealIOJ9AL.qAL δ b (PL) (trAL δ b Rt hgen prims hpG h31A h31 χ) (chalsALJ8 δ χ)
        (MAL δ b Rt hgen prims hpG h31A h31 χ).pubsL) := by
  obtain ⟨hinj, hadj⟩ := nodesL_ok δ Rt hgen prims hpG h31L
  have hlen : (tbR δ Rt hgen prims (yOf δ χ)).length ≤ nLRun (K := K) δ Rt hgen prims := by
    rw [tbR_length]; simp only [nLRun]; omega
  have hgood := goodAL_famAL δ b Rt hgen prims hpG h31A h31 hχ
  have hblk : ∀ cl, CallOK p cl → BlockBaseSat (F := ZMod p) p cl ∧ BlockIdentSat (K := K) δ p cl :=
    fun cl hcl => ⟨AluSatBlock.blockBaseSat_G hpG cl hcl, AluSatBlock.blockIdentSat_G δ hpG cl hcl⟩
  have hnoDecP : ∀ q ∈ psRun (p := p) Rt hgen prims, q.2 ≠ .dec :=
    fun q hq => hnoDec q (List.mem_filter.mp hq).1
  have hpV : Quad.mk _ (pubsLOf δ Rt hgen prims χ AluSZChipJ9.pubALv)
      (pubsLOf δ Rt hgen prims χ (AluSZChipJ9.pubALv + 1)) = SV δ Rt hgen prims (nLRun (K := K) δ Rt hgen prims) χ := by
    simp only [pubsLOf, AluSZChipJ9.pubALv]
    exact pub2_mk2 δ _ 0 rfl
  have hpS : Quad.mk _ (pubsLOf δ Rt hgen prims χ AluSZChipJ9.pubALs)
      (pubsLOf δ Rt hgen prims χ (AluSZChipJ9.pubALs + 1)) = SS δ Rt hgen prims (nLRun (K := K) δ Rt hgen prims) χ := by
    simp only [pubsLOf, AluSZChipJ9.pubALs]
    norm_num
    exact pub2_mk2 δ _ 2 rfl
  have hpX : Quad.mk _ (pubsLOf δ Rt hgen prims χ AluSZChipJ9.pubALx)
      (pubsLOf δ Rt hgen prims χ (AluSZChipJ9.pubALx + 1)) = SX δ Rt hgen prims (nLRun (K := K) δ Rt hgen prims) χ := by
    simp only [pubsLOf, AluSZChipJ9.pubALx]
    norm_num
    exact pub2_mk2 δ _ 4 rfl
  obtain ⟨hsat, hbind, hpreg⟩ := AluSatRun.aluSZChipJ9_sat_run δ b (Nat.succ_pos _) (nodesLRun δ Rt hgen prims hpG)
    (orbL δ Rt hgen prims hpG) (pubsLOf δ Rt hgen prims χ) Rt prims hgen (psRun (p := p) Rt hgen prims)
    (vcRun (p := p) Rt hgen prims) (mRun (t := t) prims) χ hpG h31 hnd hprim hnoDec hnoDecP hlimb hblk hinj hadj
    hlen hgood hpV hpS hpX
  rw [preL_indep δ Rt hgen prims (nodesLRun δ Rt hgen prims hpG) (yOf δ χ)] at hsat hbind hpreg
  have hnp : nLRun (K := K) δ Rt hgen prims < p := by
    have := ComplJ9AChains.hp63_of_G hpG
    unfold Rows31AL at h31L
    simp only [nLRun]
    omega
  exact Or.inl ⟨rfl, hsat, hbind, hinj, hadj, hnp, hpreg⟩

/-! ## 2. Weights and the figure -/

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (badList_OK badList_counts badList_ord_mem nOrds_eq_zero costL_le
  cost_div_lt sum_w_badOf)

/-- **The J-8 families at `DL`**: side conditions, pins only, pin count (the `famsJA_facts` twin). -/
theorem famsJL_facts :
    (∀ L ∈ famsJL δ b Rt hgen prims hpG h31, ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsJL δ b Rt hgen prims hpG h31, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsJL δ b Rt hgen prims hpG h31).map nPins).sum ≤ 2 ^ 40 + 1 + 15 * 2 ^ 31 := by
  have h31' : ∀ x ∈ sizesJ8 (DL), x ≤ 2 ^ 31 := rows31_of_A h31
  obtain ⟨o1, p1, c1⟩ := famsOf_facts δ b (K := K) (DL) (hFL Rt hgen prims hpG h31)
    (cellsL_pos Rt prims hgen) h31'
  obtain ⟨o2, p2, c2⟩ := ComplJ9BOf.famsA9_facts δ b (K := K) (DL) (DL) (hFL Rt hgen prims hpG h31)
    (acsL_pos Rt prims hgen)
  have hacs := h31' _ (show (DL).acs.length ∈ sizesJ8 (DL) by simp [sizesJ8])
  have hnV := h31' _ (show nVOf (DL) ∈ sizesJ8 (DL) by simp [sizesJ8])
  refine ⟨fun L hL => ?_, fun L hL => ?_, ?_⟩
  · rcases List.mem_append.mp hL with h | h
    exacts [o1 L h, o2 L h]
  · rcases List.mem_append.mp hL with h | h
    exacts [p1 L h, p2 L h]
  · show ((famsOf δ b (DL) (hFL Rt hgen prims hpG h31) (cellsL_pos Rt prims hgen) ++
      ComplJ9BOf.famsA9 δ b (DL) (DL) (hFL Rt hgen prims hpG h31) (acsL_pos Rt prims hgen)).map nPins).sum ≤ _
    rw [List.map_append, List.sum_append]
    omega

/-- J-9 A's list costs `≤ 2^66 + 2^63` (the bound inside `figA`). -/
theorem costL_badSA : costL (badSA δ b Rt hgen hpG h31A (K := K)) ≤ 2 ^ 66 + 2 ^ 63 := by
  obtain ⟨o, pn, c⟩ := ComplJ9AOfBad.facts_all δ b Rt hgen hpG h31A (K := K)
  have h0 : ∀ L ∈ famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen (K := K), nOrds L = 0 :=
    fun L hL => nOrds_eq_zero L (pn L hL)
  have hN8 : N8 (p := p) Rt hgen ≤ 2 ^ 31 := h31A _ (List.mem_append_left _ (by simp [sizesJ8]))
  have hN9 : N9 t ≤ 2 ^ 31 := h31A _ (ComplJ9AOfBad.mem_N9 Rt hgen)
  have hcnt := badList_counts [(⟨13, by decide⟩, N8 (p := p) Rt hgen), (⟨13, by decide⟩, N9 t)]
    (famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen (K := K)) h0
  have hM : ∀ i N, BadSpec.ord i N ∈ badSA δ b Rt hgen hpG h31A → N ≤ 2 ^ 31 := by
    intro i N hm
    have := badList_ord_mem _ _ pn i N hm
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at this
    rcases this with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have hc := costL_le (badSA δ b Rt hgen hpG h31A) (2 ^ 31) hM
  have hp : nPins (badSA δ b Rt hgen hpG h31A) ≤ 2 ^ 66 := hcnt.1 ▸ c
  have ho : nOrds (badSA δ b Rt hgen hpG h31A) = 2 := hcnt.2
  rw [ho] at hc
  have e63 : (2 : ℕ) ^ 31 * 2 ^ 31 = 2 ^ 62 := by norm_num
  rw [e63] at hc
  have e62 : (2 : ℕ) ^ 63 = 2 * 2 ^ 62 := by norm_num
  omega

/-- A pins-only list costs its pin count. -/
theorem costL_of_pins (L : List (BadSpec K)) (h : ∀ s ∈ L, ∀ i N, s ≠ BadSpec.ord i N) : costL L ≤ nPins L := by
  have hc := costL_le L 0 fun i N hm => absurd rfl (h _ hm i N)
  rw [nOrds_eq_zero L h] at hc
  simpa using hc

/-- **The weights at the record** (`wt`). -/
theorem wtAL : ∀ e ∈ badAL δ b Rt hgen prims hpG h31A h31,
    (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2 := by
  refine ComplJ8Bad.wt_badOf _ fun sp hs => ?_
  rcases List.mem_append.mp hs with h | h
  · rcases List.mem_append.mp h with h | h
    · exact badList_OK _ _ (ComplJ9AOfBad.facts_all δ b Rt hgen hpG h31A (K := K)).1 sp h
    · obtain ⟨L, hL, hsL⟩ := List.mem_flatten.mp h
      exact (famsJL_facts δ b Rt hgen prims hpG h31).1 L hL sp hsL
  · exact AluPoles.famAL_OK δ _ _ sp h

/-- **The completeness error of the record** is `cost / |K|`, with
`cost = cost(badSA) + #pins(famsJL) + 5 nL`. -/
theorem epsAL : ((badAL δ b Rt hgen prims hpG h31A h31).map Prod.snd).sum =
    ((costL (badSA δ b Rt hgen hpG h31A) + costL (famsJL δ b Rt hgen prims hpG h31).flatten +
      5 * nLRun (K := K) δ Rt hgen prims : ℕ) : ℚ) / Fintype.card K := by
  rw [badAL, sum_w_badOf, badSAL, AluPoles.costL_append, AluPoles.costL_append, AluPoles.famAL_cost]

/-- **The figure** (`fig`): `< 2^-120` at `|K| = cK` and `nL ≤ 2^31` (the second conjunct of `RowsLe31AL`), by
margin (cost `< 2^68`; `fig_famAL`'s `2^67` base does not hold here). -/
theorem figAL (hK : Fintype.card K = VclL.Events.cK) (hnL : (PL).nL ≤ 2 ^ 31) :
    ((badAL δ b Rt hgen prims hpG h31A h31).map Prod.snd).sum < 1 / 2 ^ 120 := by
  rw [epsAL]
  refine cost_div_lt _ ?_ hK
  have h1 := costL_badSA δ b Rt hgen hpG h31A (K := K)
  have hpf : ∀ s ∈ (famsJL δ b Rt hgen prims hpG h31).flatten, ∀ i N, s ≠ BadSpec.ord i N := by
    intro s hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.mp hs
    exact (famsJL_facts δ b Rt hgen prims hpG h31).2.1 L hL s hsL
  have h2 := costL_of_pins _ hpf
  rw [ComplJ8Bad.nPins_flatten] at h2
  have h2' := (famsJL_facts δ b Rt hgen prims hpG h31).2.2
  have h3 : nLRun (K := K) δ Rt hgen prims ≤ 2 ^ 31 := hnL
  have e68 : (2 : ℕ) ^ 68 = 295147905179352825856 := by norm_num
  have e66 : (2 : ℕ) ^ 66 = 73786976294838206464 := by norm_num
  have e63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
  have e40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
  have e31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  rw [e66, e63] at h1; rw [e40, e31] at h2'; rw [e31] at h3; rw [e68]
  omega

/-! ## 3. Staging -/

open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage (zero_of_one all_of_two)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (fullCol)

/-- The ALU column polynomial as a function of the column index's value only (no coin, no public). -/
def colPoly {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (pre : Fin 3 → (ZMod p)[X]) (col : ℕ → Fin n → ZMod p) (j : ℕ) : (ZMod p)[X] :=
  if hj : 2 ≤ j ∧ j < 5 then pre ⟨j - 2, by omega⟩
  else if j = AluSZChipJ9.sL then
    AluTraceFix.fixAt (Lagrange.interpolate Finset.univ nodes (fullCol hn col j)) (AluTraceFix.zNodes nodes)
      (xLast hn nodes orbit)
  else Lagrange.interpolate Finset.univ nodes (fullCol hn col j)

theorem colPoly_congr {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (pre : Fin 3 → (ZMod p)[X]) (col col' : ℕ → Fin n → ZMod p) (j : ℕ) (hc : col j = col' j) :
    colPoly hn nodes orbit pre col j = colPoly hn nodes orbit pre col' j := by
  have : fullCol hn col j = fullCol hn col' j := by funext i; simp only [fullCol, hc]
  simp only [colPoly, this]

theorem trAL_L (χ : Coins frameJ8 K) (j : Fin wAL) :
    (trAL δ b Rt hgen prims hpG h31A h31 χ).L j =
      colPoly (PL).hnL (PL).nodesL (PL).orbitL (PL).preL
        (colAL δ b (tbR δ Rt hgen prims (yOf δ χ)) (r2AL δ (chalsALJ8 δ χ) (tbR δ Rt hgen prims (yOf δ χ)))) j :=
  rfl

/-- **The ALU trace is staged** (`crAL`). -/
theorem stL_AL : StagedCols frameJ8 crAL (fun χ => (trAL δ b Rt hgen prims hpG h31A h31 χ).L) := by
  intro j χ χ' h
  simp only [trAL_L]
  by_cases h0 : (j : ℕ) < 94
  · refine colPoly_congr _ _ _ _ _ _ _ (funext fun i => ?_)
    simp only [colAL, h0, if_true]
    rw [rowAt_tbR_fst δ Rt hgen prims (yOf δ χ), rowAt_tbR_fst δ Rt hgen prims (yOf δ χ')]
  · by_cases h1 : (j : ℕ) < 148
    · have hz := zero_of_one χ χ' (crAL j) (by simp [crAL, h0, h1]) h
      have hy : yOf δ χ = yOf δ χ' := by
        simp only [yOf, hz cY1 FrameJ8.frameJ8_y_round0.1, hz cY2 FrameJ8.frameJ8_y_round0.2.1]
      rw [hy]
      refine colPoly_congr _ _ _ _ _ _ _ (funext fun i => ?_)
      have h18 : ((j : ℕ) - 94) / 3 < 18 := by omega
      simp only [colAL, h0, if_false, roleK, h18, if_true]
    · have := all_of_two χ χ' (crAL j) (by simp [crAL, h0, h1]) h
      subst this; rfl

/-- **`staged` at the record** (`StJ9AL trAL`). -/
theorem stagedAL : StJ9AL (trAL δ b Rt hgen prims hpG h31A h31) := by
  obtain ⟨sC, -, sW, -, -, sV, sX, sS⟩ := ComplJ9AOfBad.stagedA δ b Rt hgen hpG h31A (K := K)
  have hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) →
      encR δ χ = encR δ χ' := fun χ χ' h =>
    encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide)) (h FrameJ8.cY1 (by decide))
      (h FrameJ8.cY2 (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, stL_AL δ b Rt hgen prims hpG h31A h31⟩
  · intro j χ χ' h
    simp only [trAL_C]
    exact sC j χ χ' h
  · exact ComplJ8Enc.cellTrME_staged δ b (cellsL_pos Rt prims hgen) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz
  · intro j χ χ' h
    simp only [trAL_W]
    exact sW j χ χ' h
  · exact ComplJ8Jet.stJ δ b _ _ _ (fun χ => rfl)
  · exact ComplJ8Of.stA_run δ b (DL) _ _
  · intro j χ χ' h
    simp only [trAL_V]
    exact sV j χ χ' h
  · intro j χ χ' h
    simp only [trAL_X]
    exact sX j χ χ' h
  · intro j χ χ' h
    simp only [trAL_S]
    exact sS j χ χ' h

end Alu

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALOfAlu
