/-
the headline-binder package for `nock_e2e_J9AL_succinct`
(J9AL/E2ESuccinctJ9AL.lean) at the executed `add` instance `addALR` (Exec/AddALR.lean): twin of J-9 A's `E2ESuccinctNonVac` 1/2/4.  No file is edited.

* `sideNums_add`: `SideNums (XI170 addALR) .. (31/64) (31/64) (mSX * (2^nD / |KC|))` (nc 1219, tabs 5, nD 13, k 6), `mSX + 1 <= 2^12` (`mSX_add`),
  side-VK budget `2 (total - 1) <= 2^40` (`vk_total_add`), side-tree budgets (`side_budgets_add`).
* `Jm_T_pos_add`: `0 < IG.Jm.T` for every `InstG` over `XI170 addALR` (the generic `Jm_T_pos` of NonVac2 reused).
* `add_Wb`, `main_budgets_add` (twin): ONE `V <= 2^32`, `Pn`, `Q_FS`, `Q_H` with `hterm`/`hconfig` for the main Merkle tree of the headline.
* `binders_add_indep` / `binders_add_dep` (twin): every instance-typed binder of the (S) conclusion is inhabited (`Statement = Salt = Unit`).
* `bad_event_add`: the link gate ACCEPTS `cAddF` at `addALRF` (`linkGate9L`), and (modulo the executed gate `hsh`, as `add_witness_false`) there is a datum `d` with
  `d.c = cAddF` and `¬ HoldsN d.c`.
NO new named hypothesis: `hsh` (the executed `shapeOkF` gate, as at J-9 A) only where `add_witness_false` needs it.  `HF1L` is not needed by any of these.
Not zero-knowledge.
-/
import NockvmE2E.J9AL.E2ESuccinctJ9AL
import NockvmE2E.J9AL.E2EJ9ALToy
import NockvmE2E.J9A.E2ESuccinctNonVac4

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.E2ESuccinctNonVacL
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.Exec.ShapeF NockvmE2E.Exec.E2EGen NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J9AChips
open NockvmE2E.J8.TieJ8G (sizes nsK gbJ chalK)
open NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J9A.LagrJ9A (LagrAt9 numeralOkF)
open NockvmE2E.J9A.RunGate9L (maskOkFL linkGate9L)
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.HtieJ9AL NockvmE2E.J9AL.LagrJ9AL
  NockvmE2E.J9AL.E2EJ9ALQ NockvmE2E.J9AL.E2EJ9ALP
open NockvmE2E.Exec.E2EGenT NockvmE2E.Exec.E2EGen
open NockvmE2E.Exec.E2EJ8P2 (sl0X sl1X)
open NockvmE2E.Exec.E2EJ8F (slotOK_X)
open NockvmE2E.J8.InstJ8 (P)
open NockvmE2E.J8 (TabRestr)
open NockvmE2E.J9AL.E2EJ9AL (hnqPJ9L hmV9L)
open NockvmE2E.Exec.E2EOnlineP
open NockvmE2E.Exec.E2EJ8V (SideRng HfOf FSfOf vkSide)
open NockvmE2E.Exec.SideBoundF (SideNums)
open NockvmE2E.Exec.AddALR (addALR addALRF)
open NockvmE2E.Exec.SideInst (mSX opList)
open NockvmE2E.J9A.E2ESuccinctNonVac (hterm_gen hconfig_gen side_leaf_le instKC_toy opList_length_le fixCols_size_le)
open NockvmE2E.J9A.E2ESuccinctNonVac4 (nv4_rapskel_le nv4_Wb_le nv4_mem_append nv4_instTab_gen nv4_finite_M0 nv4_finite_Mfin)
open NockvmE2E.J9A.E2EJ9AVSat (finite_NQuery)
open ProximityGap CoreDefinitions NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability NockvmE2E.Merkle.SideMerkle

/-! ## numbers at addALR -/

theorem add_nD : (XI170 addALR).nD = 13 := rfl
theorem add_nc : (XI170 addALR).nc = 1219 := rfl
theorem add_r : (XI170 addALR).r = 2 := rfl
theorem add_k : (XI170 addALR).k = 6 := rfl
theorem add_nq : (XI170 addALR).nq = 9 := rfl
theorem add_tabs : (XI170 addALR).tabs.size = 5 := NockvmE2E.J9AL.E2EJ9ALToy.tabs_size
theorem add_nD32 : (XI170 addALR).nD ≤ 32 := by rw [add_nD]; norm_num
theorem add_hk : 1 ≤ (XI170 addALR).k := by rw [add_k]; decide

theorem mSX_genL (XI : ExecInst) (hnc : XI.nc ≤ 1355) (hr : XI.r = 2) (ht : XI.tabs.size ≤ 7) : mSX XI + 1 ≤ 2 ^ 12 := by
  have h := opList_length_le XI
  rw [hr] at h
  unfold mSX
  generalize (opList XI).length = L at h ⊢
  norm_num at h ⊢
  omega

theorem mSX_add : mSX (XI170 addALR) + 1 ≤ 2 ^ 12 :=
  mSX_genL _ (by rw [add_nc]; norm_num) add_r (by rw [add_tabs]; norm_num)

theorem vk_total_genL (XI : ExecInst) (hnc : XI.nc ≤ 1355) (ht : XI.tabs.size ≤ 7) (hD : XI.nD - 1 = 12) :
    2 * ((NockvmE2E.Exec.VKBind.vkSp XI).total - 1) ≤ 2 ^ 40 := by
  rw [NockvmE2E.Exec.VKBind.vkSp_total]
  have h := fixCols_size_le XI
  rw [hD]
  generalize (fixCols XI).size = S at h ⊢
  have : 2 * S * 2 ^ 12 ≤ 2 * 1363 * 2 ^ 12 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  omega

theorem vk_total_add : 2 * ((NockvmE2E.Exec.VKBind.vkSp (XI170 addALR)).total - 1) ≤ 2 ^ 40 :=
  vk_total_genL _ (by rw [add_nc]; norm_num) (by rw [add_tabs]; norm_num) (by rw [add_nD])

/-- `SideNums` at addALR, `θ = δ = 31/64`, `ε = mSX * 2^nD / |KC|` (the `ε` of `nock_e2e_J9AL_numbers`) -/
theorem sideNums_add [SampleableType KC] :
    SideNums (XI170 addALR) add_nD32 (31 / 64 : ℝ) (31 / 64 : ℝ≥0)
      ((mSX (XI170 addALR) * ((2 ^ (XI170 addALR).nD : ℝ≥0) / Fintype.card KC) : ℝ≥0)) := by
  have hr : 64 * (2 ^ (∑ i : Fin ((XI170 addALR).k + 1), (((fun _ : Fin ((XI170 addALR).k + 1) => (1 : ℕ+)) i).1 : ℕ)) * ((1 : ℕ+) : ℕ)) ≤
      2 ^ (XI170 addALR).nD := by
    rw [add_k, add_nD]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, PNat.one_coe, Nat.mul_one]
    have h1 : (1 : ℕ+).1 = 1 := rfl
    simp only [h1, PNat.val_ofNat, PNat.one_coe]
    norm_num
  have hfb : friBound (fun _ : Fin ((XI170 addALR).k + 1) => (1 : ℕ+)) 1 = 2 ^ ((XI170 addALR).k + 1) := by
    unfold friBound
    have h1 : (1 : ℕ+).1 = 1 := rfl
    simp [h1]
  refine ⟨add_hk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [add_k]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, PNat.one_coe, Nat.mul_one, PNat.val_ofNat]
    rw [add_nD]; norm_num
  · exact NockvmE2E.Succ.Numbers.caError_powers_numbers (F := KC) (ω := smoothDomain (XI170 addALR).nD add_nD32)
      (mSX (XI170 addALR)) (N := 2 ^ (∑ i : Fin ((XI170 addALR).k + 1), (((fun _ : Fin ((XI170 addALR).k + 1) => (1 : ℕ+)) i).1 : ℕ)) *
        ((1 : ℕ+) : ℕ)) (by positivity) hr
  · rw [hfb]
  · rw [hfb, add_k, add_nD]; norm_num
  · rw [hfb, add_k]
    refine NockvmE2E.Succ.Numbers.relUDR_rs_ge _ _ ?_
    rw [Fintype.card_fin, add_nD]; norm_num

/-- the challenge instance at addALR's domain, by name -/
noncomputable def iCh_add : ∀ j, SampleableType ((pSpec (XI170 addALR).k
    (ω := smoothDomain (XI170 addALR).nD add_nD32) (fun _ : Fin ((XI170 addALR).k + 1) => (1 : ℕ+)) (XI170 addALR).l).Challenge j) :=
  fun j => by
    haveI := NockvmE2E.FriPort.friChal_finite (k := (XI170 addALR).k) (ω := smoothDomain (XI170 addALR).nD add_nD32)
      (fun _ : Fin ((XI170 addALR).k + 1) => (1 : ℕ+)) (XI170 addALR).l j
    haveI := NockvmE2E.FriPort.friChal_nonempty (k := (XI170 addALR).k) (ω := smoothDomain (XI170 addALR).nD add_nD32)
      (fun _ : Fin ((XI170 addALR).k + 1) => (1 : ℕ+)) (XI170 addALR).l j
    haveI := Fintype.ofFinite ((pSpec (XI170 addALR).k (ω := smoothDomain (XI170 addALR).nD add_nD32)
      (fun _ : Fin ((XI170 addALR).k + 1) => (1 : ℕ+)) (XI170 addALR).l).Challenge j)
    exact SampleableType.ofFintype _

/-- the side-tree budget witness at addALR: `Vf = 6 * 2^13 <= 2^32` -/
noncomputable def side_budgets_add := @NockvmE2E.J9A.E2ESuccinctNonVac.side_budgets_sat instKC_toy (XI170 addALR) add_nD32 iCh_add
  (by rw [add_k, add_nD]; norm_num)

/-- `0 < Jm.T` at the loaded instance `XI170 addALR`, for any bundle (in particular `InstG.ofJ9AL (XI170 addALR) ..`) -/
theorem Jm_T_pos_add {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} (IG : InstG F J (XI170 addALR)) :
    0 < IG.Jm.T :=
  NockvmE2E.J9A.E2ESuccinctNonVac2.Jm_T_pos IG (by rw [add_tabs]; norm_num)

/-- every RAP block width of the loaded instance is `<= 2^11` (`nc = 1219`, `nq = 9`: `<= 1228`) -/
theorem add_Wb : ∀ r : ℕ, r < 4 → Wb (XI170 addALR) r ≤ 2 ^ 11 := by
  intro r _
  have := nv4_Wb_le (XI170 addALR) r
  rw [add_nc, add_nq] at this
  omega

/-! ## the bad event -/

open NockvmE2E.J9AL.E2EJ9ALToy in
/-- the runtime link gate accepts the false claim at its own instance (so `cAddF` is a claim the gate lets through to `verifyOnline'`);
[kernel job; reuses `link_addF`] -/
theorem bad_event_gate_addF : linkGate9L (XI170 addALRF) cAddF = true :=
  decide_eq_true link_addF

open NockvmE2E.J9AL.E2EJ9ALToy in
/-- **`bad_event_add`** [kernel job, modulo the executed gate `hsh` at the twin, as `add_witness_false`]: the gate accepts `cAddF` at `addALRF`, and there is a datum
`d` of the headline with `d.c = cAddF` and `¬ HoldsN d.c`, so the bad event `verifyOnline' ∧ ¬HoldsN c` ranges over a non-empty claim. -/
theorem bad_event_add (hsh : shapeOkF famJ9AL (XI170 addALRF) = true) :
    linkGate9L (XI170 addALRF) cAddF = true ∧ ∃ (d : Datum9AL) (_ : DatumOK9AL d), d.c = cAddF ∧ ¬ Nock.Jet.HoldsN d.c := by
  obtain ⟨⟨d, hdk, L, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -⟩, -, -, hn⟩ := add_witness_false hsh
  exact ⟨bad_event_gate_addF, d, hdk, hc, by rw [hc]; exact hn⟩

/-! ## the datum context of the headline, at `XI0 = addALR` -/

set_option hygiene false in
local notation "XI0" => addALR
set_option hygiene false in
local notation "IG" => InstG.ofJ9AL (XI170 XI0) hsh d hdk L R hT hσ hfree
set_option hygiene false in
local notation "hopsV" => (hops9L_of_chips hsh d hchips hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops9L_of_chips hsh d hchips hnum0).2.1
set_option hygiene false in
local notation "hconsV" => (hops9L_of_chips hsh d hchips hnum0).2.2
set_option hygiene false in
local notation "hszV" => hsz9L hsh d hdk L R hT hσ hfree NockvmE2E.Exec.J8Chips.jMeta hnumV hopsV
set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD (hn32_of_shapeF hsh)
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeXF IG (XI170 XI0).pubOf.size rfl hshX
set_option hygiene false in
local notation "JXn" => (IG).JJ (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "cIV" => cIG IG (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "hcIcol" => hcI_col_G IG (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "hcIpub" => hcI_pub_G IG (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "prV" => prG IG (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "hd1" => ((d_of_shapeF hsh).symm : (1 : ℕ+).val = (XI170 XI0).d)
set_option hygiene false in
local notation "hNHV" => hNH_G IG (XI170 XI0).pubOf.size tp hcapV 1 hd1
set_option hygiene false in
local notation "hpdV" => hpd_G IG (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "GX" => GflatG IG hszV
set_option hygiene false in
local notation "PJ" => (deepParamsJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "AJ" => (airJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "R0P" => R0J JXn prV ωS (31 / 64) (friBound s1 1)
set_option hygiene false in
local notation "RestP" => RestJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "RestVP" => RestVJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeXF hshX).trans (hnqPJ9L XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp).symm : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (hmV9L XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp)
set_option hygiene false in
local notation "HBLK" => hblk_of_shapeXF IG (XI170 XI0).pubOf.size tp hcapV rfl hshX cIV (cI_val_G IG _ tp hcapV rfl cIV hcIcol hcIpub)
set_option hygiene false in
local notation "HBLKQ" => hblkq_F hsh (PJ).nq (HNQ).ge
set_option hygiene false in
local notation "MDV" => mdX (XI170 XI0) (hn1_of_shapeF hsh) (PJ).colRoundX
  (rkP (XI170 XI0) (PJ) rfl HNQ cIV HBLK HBLKQ) toyEncB
set_option hygiene false in
local notation "LV" => LX (XI170 XI0) (hn32_of_shapeF hsh)
set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 1 (XI170 XI0).l DgJ8 encK MDV LV (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame (JXn).Φ0 2) KC (MDV).toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 1 (XI170 XI0).l DgJ8 encK LV
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "ZStmt'" => NockvmE2E.Exec.SideInst.SStmt (XI170 XI0)
set_option hygiene false in
local notation "SMS" => NockvmE2E.Merkle.SideMerkle.bMask (S := KC) s1 1 (XI170 XI0).l LV DgJ8 encK
set_option hygiene false in
local notation "ZOp" => OpenAll DgJ8 (merkleSkels (SMS))
set_option hygiene false in
local notation "Zskels" => NockvmE2E.Exec.SideInst.skelsSide (XI170 XI0)
set_option hygiene false in
local notation "MFIN" => (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin
set_option hygiene false in
local notation "MZERO" => ((PJ).statement (R0P) (RestP)).M0

section Ctx
variable (hsh : shapeOkF famJ9AL (XI170 addALR) = true) (hshX : shapeXOkF famJ9AL (XI170 addALR) = true)
  (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L (XI170 addALR) d) (R : TabRestr (J9AL d hdk))
  (hT : R.T' = (XI170 addALR).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9L (XI170 addALR) (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)
  (hchips : chipsOkF famJ9AL (XI170 addALR) = true)
  (hnum0 : ∀ t : Fin (XI170 addALR).tabs.size,
    (chipNumeralF famJ9AL (XI170 addALR).tabs[t].chip).getD 0 = numOf9L d (sigma9L (XI170 addALR) t))

/-! ## : the main-tree budgets, jointly -/

section Z36
variable [instKC : SampleableType KC] (tp : Fin (IG).Jm.T)
  [iDM0 : DecidableEq ((PJ).statement (R0P) (RestP)).M0] [fM0 : Finite ((PJ).statement (R0P) (RestP)).M0]
  [iDMf : DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [fMf : Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
  [iCh : ∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]

set_option maxHeartbeats 4000000 in
/-- **`main_budgets_add`** (twin): at `XI0 = addALR`, for the main Merkle tree of `nock_e2e_J9AL_succinct`, `V ≤ 2^32` together with `hterm` and `hconfig`, and `Q_FS`, `Q_H`
with `hQFS`, `hQH`, are jointly inhabited: `V = 10 * B`, `Pn = 2 * B`, `B = 2^12 * 2 * 2^11 + 1 + 2^13`. -/
theorem main_budgets_add : ∃ Q_FS Q_H V Pn : ℕ, Q_FS ≤ 2 ^ 64 ∧ Q_H ≤ 2 ^ 64 ∧ V ≤ 2 ^ 32 ∧
    (∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
        (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
        claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V) ∧
    (∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn) := by
  have hnD : (XI170 XI0).nD = 13 := add_nD
  have hRMs : merkleSkels (RM) = (List.range 4).map (fun i => (MDV).toRapMaskData.skel (0 + i)) :=
    NockvmE2E.Exec.E2E.merkleSkels_rapMerkleMask (Φ := extFrame (JXn).Φ0 2) (K := KC) (MDV).toRapMaskData _ I Ifin 4 0
  have hRM' : ∀ s ∈ merkleSkels (RM), s.leafCount ≤ 2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13 := by
    intro s hs
    rw [hRMs] at hs
    simp only [List.mem_map, List.mem_range] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    have := nv4_rapskel_le (2 ^ ((XI170 XI0).nD - 1)) (Wb (XI170 XI0) (0 + i)) (2 ^ 11) (add_Wb (0 + i) (by omega))
    exact this.trans (by rw [hnD]; norm_num)
  have hBM : ∀ s ∈ merkleSkels (BM), s.leafCount ≤ 2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13 := by
    intro s hs
    have := side_leaf_le (XI170 XI0) (hn32_of_shapeF hsh) s hs
    exact this.trans (by rw [hnD]; norm_num)
  have hB : ∀ s ∈ merkleSkels (MC), s.leafCount ≤ 2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13 :=
    nv4_mem_append (RM) (BM) _ hRM' hBM
  have hlenBM : (merkleSkels (BM)).length = 6 :=
    (NockvmE2E.Merkle.SideMerkle.merkleSkels_bMask_length (S := KC) s1 1 (XI170 XI0).l LV DgJ8 encK).trans add_k
  have hlen : (merkleSkels (MC)).length ≤ 10 := by
    have h1 : merkleSkels (MC) = merkleSkels (RM) ++ merkleSkels (BM) := NockvmE2E.Exec.E2E.merkleSkels_append _ _
    rw [h1, List.length_append, hRMs, hlenBM, List.length_map, List.length_range]
  have hBf : ∀ j : Fin (merkleSkels (MC)).length, ((merkleSkels (MC)).get j).leafCount ≤ 2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13 :=
    fun j => hB _ (List.get_mem _ j)
  refine ⟨0, 0, 10 * (2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13), 2 * (2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13), Nat.zero_le _, Nat.zero_le _,
    by norm_num, fun roots h op logs => ?_, hconfig_gen _ _ hBf⟩
  exact (hterm_gen _ _ hBf roots h op logs).trans (Nat.mul_le_mul_right _ hlen)

end Z36

/-! ## : the instance binders -/

section Z37indep
variable [instKC : SampleableType KC] (tp : Fin (IG).Jm.T)

/-- **`binders_add_indep`** (twin, independent binders): `Statement = Salt = Unit` with `DecidableEq`/`Finite`; `hz`; `instKC`, `iCh`, `tp`; `Finite`/`DecidableEq` of
`M0`, `Mfin`; `OracleInterface` of `M0`, of every column block, of `Mfin` (the default interface); `m0`, `mf`. -/
theorem binders_add_indep :
    (Nonempty (DecidableEq Unit) ∧ Nonempty (DecidableEq Unit) ∧ Nonempty (Finite Unit) ∧ Nonempty (Finite Unit)) ∧
    (∃ (encZ : Unit × Unit → List ℕ) (decZ : List ℕ → Unit × Unit), ∀ x, decZ (encZ x) = x) ∧
    Nonempty (SampleableType KC) ∧ Nonempty (Fin (IG).Jm.T) ∧
    Nonempty (∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)) ∧
    Nonempty (DecidableEq MZERO) ∧ Nonempty (Finite MZERO) ∧ Nonempty (DecidableEq MFIN) ∧ Nonempty (Finite MFIN) ∧
    Nonempty (OracleInterface.{0, 0} MZERO) ∧
    Nonempty ((r : ℕ) → OracleInterface.{0, 0} (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r)) ∧
    Nonempty (OracleInterface.{0, 0} MFIN) ∧ Nonempty MZERO ∧ Nonempty (R0P).Mfin := by
  haveI : Finite (R0P).M0 := inferInstanceAs (Finite Unit)
  haveI : Finite (R0P).Mfin := inferInstanceAs (Finite Unit)
  exact ⟨⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩,
    ⟨fun _ => [], fun _ => ((), ()), fun _ => rfl⟩,
    ⟨instKC_toy⟩, ⟨⟨0, Jm_T_pos_add IG⟩⟩, ⟨iCh_add⟩,
    ⟨Classical.decEq _⟩, ⟨nv4_finite_M0 (PJ) (R0P) (RestP)⟩, ⟨Classical.decEq _⟩,
    ⟨nv4_finite_Mfin (PJ) (AJ) (R0P) (RestP) _⟩,
    ⟨OracleInterface.instDefault⟩, ⟨fun _ => OracleInterface.instDefault⟩, ⟨OracleInterface.instDefault⟩,
    ⟨()⟩, ⟨()⟩⟩
end Z37indep

section Z37dep
variable [instKC : SampleableType KC] (tp : Fin (IG).Jm.T)
  [iDM0 : DecidableEq ((PJ).statement (R0P) (RestP)).M0] [fM0 : Finite ((PJ).statement (R0P) (RestP)).M0]
  [iDMf : DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [fMf : Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
  [iCh : ∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]

set_option maxHeartbeats 4000000 in
/-- **`binders_add_dep`** (twin, dependent binders): at `Statement = Salt = Unit`, for EVERY choice of the independent binders, the four table binders are inhabited:
`fQ`, `instTab`, `fQF`, `instTabF`. -/
theorem binders_add_dep :
    Nonempty (Finite (NQuery (merkleSkels (MC)))) ∧
    Nonempty (SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Unit Unit (MC) dd)) ∧
    Nonempty (Finite (NQuery Zskels)) ∧
    Nonempty (SampleableType (∀ d', succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' (Unit × Unit) (SMS) d')) := by
  haveI := finite_NQuery (merkleSkels (MC))
  haveI := finite_NQuery Zskels
  exact ⟨⟨inferInstance⟩, ⟨nv4_instTab_gen DgJ8 (OPN) (NQuery (merkleSkels (MC))) Unit Unit (MC)⟩, ⟨inferInstance⟩,
    ⟨nv4_instTab_gen DgJ8 ZOp (NQuery Zskels) ZStmt' (Unit × Unit) (SMS)⟩⟩

end Z37dep

end Ctx

end NockvmE2E.J9AL.E2ESuccinctNonVacL

#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.mSX_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.vk_total_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.sideNums_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.iCh_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.side_budgets_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.Jm_T_pos_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.add_Wb
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.bad_event_gate_addF
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.bad_event_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.main_budgets_add
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.binders_add_indep
#print axioms NockvmE2E.J9AL.E2ESuccinctNonVacL.binders_add_dep
