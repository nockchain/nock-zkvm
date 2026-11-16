/-
the remaining binders of `nock_e2e_J9A_succinct`, witnessed JOINTLY at the loaded
instance `toy9R`.  No file or statement is edited.

*  `main_budgets_toy`: for the main Merkle tree `merkleSkels (MC)` of the headline, ONE `V`, ONE `Pn` with `hV : V <= 2^32`, `hterm`, `hconfig`
  exactly as the binders of `nock_e2e_J9A_succinct`, plus `Q_FS`, `Q_H` with `hQFS`, `hQH`.  The leaf bound is derived from fields by kernel evaluation
  (`toy9R_Wb`: every RAP block width of `blockLayout` is `<= 2^11`; the FRI trees have `<= 2^nD` leaves, `side_leaf_le`).
  The statement is universal in the datum context (`hsh .. hnum0`, `tp`) and in the instance binders (`I0 I Ifin ..`), as in the headline's conclusion.
*  `binders_toy` (= `binders_toy_indep` ∧ `binders_toy_dep`): every instance-typed binder of the (S) conclusion is inhabited: `Statement := Unit`,
  `Salt := Unit` (the headline is `∀ Statement Salt W`, the exe does not fix them; `Unit` is the `hz_unit` choice) with `DecidableEq`/`Finite`;
  `instKC`, `iCh`, `tp`, `iDM0 fM0 iDMf fMf`, `I0 I Ifin` (the default oracle interface), `m0 mf`, `encZ decZ hz` (`binders_toy_indep`, independent of one another);
  `fQ`, `instTab`, `fQF`, `instTabF` for ANY choice of the former (`binders_toy_dep`, universal in the instances).
Not zero-knowledge.
-/
import NockvmE2E.J9A.E2ESuccinct
import NockvmE2E.J9A.E2ESuccinctNonVac
import NockvmE2E.J9A.E2ESuccinctNonVac2

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

namespace NockvmE2E.J9A.E2ESuccinctNonVac4
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.Exec.ShapeF NockvmE2E.Exec.E2EGen NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J9AChips
open NockvmE2E.J8.TieJ8G (sizes nsK gbJ chalK)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.HtieJ9A NockvmE2E.J9A.LagrJ9A NockvmE2E.J9A.E2EJ9AQ
  NockvmE2E.J9A.E2EJ9AP NockvmE2E.Exec.E2EGenT NockvmE2E.Exec.E2EGen
open NockvmE2E.Exec.E2EJ8P2 (sl0X sl1X)
open NockvmE2E.Exec.E2EJ8F (slotOK_X)
open NockvmE2E.J8.InstJ8 (P)
open NockvmE2E.J8 (TabRestr)
open NockvmE2E.J9A.E2EJ9A (hnqPJ9 hmV9)
open NockvmE2E.Exec.E2EOnlineP
open NockvmE2E.Exec.E2EJ8V (SideRng HfOf FSfOf vkSide)
open NockvmE2E.Exec.SideBoundF (SideNums)
open NockvmE2E.Exec.Toy9R
open NockvmE2E.J9A.E2ESuccinctNonVac (hterm_gen hconfig_gen side_leaf_le instKC_toy iCh_toy toy9R_nD toy9R_nD32)
open NockvmE2E.J9A.E2ESuccinctNonVac2 (toy9R_Jm_T_pos)
open NockvmE2E.J9A.E2EJ9AVSat (finite_NQuery toy9R_k)
open ProximityGap CoreDefinitions NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability NockvmE2E.Merkle.SideMerkle

/-! ## generic pieces -/

/-- a RAP block skeleton `skelOf (ragSpec W h) (h*2*W) (h*2*W)` has `<= h*2*Wmax + 1` leaves (`1` for the empty block) -/
theorem nv4_rapskel_le (h W Wmax : ℕ) (hW : W ≤ Wmax) :
    (skelOf (ragSpec W h) (h * 2 * W) (h * 2 * W)).leafCount ≤ h * 2 * Wmax + 1 := by
  rcases Nat.eq_zero_or_pos W with rfl | hp
  · simp [skelOf, Skeleton.leafCount]
  · by_cases hh : 0 < h
    · rw [leafCount_skelOf _ (wf_ragSpec _ _ hp) _ _ (Nat.mul_pos (Nat.mul_pos hh two_pos) hp) le_rfl]
      have := Nat.mul_le_mul_left (h * 2) hW
      omega
    · have h0 : h = 0 := by omega
      subst h0
      simp [skelOf, Skeleton.leafCount]

/-- one step of the `blockLayout` fold keeps the size and raises each block width by at most one -/
def nv4_f (XJ : ExecInst) (st : Array ℕ × Array ℕ) (c : ℕ) : Array ℕ × Array ℕ :=
  if XJ.blockOf[c]! < 4 then (st.1.modify XJ.blockOf[c]! (· + 1), st.2.set! c st.1[XJ.blockOf[c]!]!) else st

theorem nv4_step (XJ : ExecInst) (st : Array ℕ × Array ℕ) (c : ℕ) (h : st.1.size = 4) :
    (nv4_f XJ st c).1.size = 4 ∧ ∀ b' : ℕ, (nv4_f XJ st c).1[b']! ≤ st.1[b']! + 1 := by
  unfold nv4_f
  by_cases hb : XJ.blockOf[c]! < 4
  · simp only [hb, ite_true]
    refine ⟨by simpa using h, fun b' => ?_⟩
    by_cases hbs : b' < st.1.size
    · rw [getElem!_pos _ b' (by simpa using hbs), getElem!_pos _ b' hbs, Array.getElem_modify]
      split <;> omega
    · rw [getElem!_neg _ b' (by simpa using hbs), getElem!_neg _ b' hbs]
      exact Nat.le_add_right _ _
  · simp only [hb, ite_false]
    exact ⟨h, fun b' => Nat.le_add_right _ _⟩

theorem nv4_fold (XJ : ExecInst) : ∀ (l : List ℕ) (st : Array ℕ × Array ℕ), st.1.size = 4 →
    (l.foldl (nv4_f XJ) st).1.size = 4 ∧ ∀ b' : ℕ, (l.foldl (nv4_f XJ) st).1[b']! ≤ st.1[b']! + l.length
  | [], st, h => ⟨h, fun b' => by simp⟩
  | c :: l, st, h => by
    obtain ⟨h1, h2⟩ := nv4_step XJ st c h
    obtain ⟨h3, h4⟩ := nv4_fold XJ l _ h1
    refine ⟨h3, fun b' => ?_⟩
    have := h4 b'
    have := h2 b'
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- every RAP block width is at most `nc + nq` (generic, no evaluation of the instance) -/
theorem nv4_Wb_le (XJ : ExecInst) (r : ℕ) : Wb XJ r ≤ XJ.nc + XJ.nq := by
  show ((List.range (XJ.nc + XJ.nq)).foldl (nv4_f XJ) (Array.replicate 4 0, Array.replicate (XJ.nc + XJ.nq) 0)).1[r]! ≤ _
  obtain ⟨-, h⟩ := nv4_fold XJ (List.range (XJ.nc + XJ.nq)) (Array.replicate 4 0, Array.replicate (XJ.nc + XJ.nq) 0) (by simp)
  have := h r
  rw [List.length_range] at this
  have h0 : (Array.replicate 4 (0 : ℕ))[r]! = 0 := by
    by_cases hr : r < 4
    · rw [getElem!_pos _ r (by simpa using hr)]; simp
    · rw [getElem!_neg _ r (by simpa using hr)]; rfl
  simp only [h0] at this
  omega

/-- every RAP block width of the loaded instance is `<= 2^11` (`nc = 1355`, `nq = 9` by `rfl` on the fields) -/
theorem toy9R_Wb : ∀ r : ℕ, r < 4 → Wb (XI170 toy9R) r ≤ 2 ^ 11 := by
  intro r _
  have h1 : (XI170 toy9R).nc = 1355 := NockvmE2E.J9A.E2ESuccinctNonVac.toy9R_nc
  have h2 : (XI170 toy9R).nq = 9 := rfl
  have := nv4_Wb_le (XI170 toy9R) r
  rw [h1, h2] at this
  omega

theorem nv4_mem_append {D : Type} [Inhabited D] (a b : MRounds D) (B : ℕ)
    (ha : ∀ s ∈ merkleSkels a, s.leafCount ≤ B) (hb : ∀ s ∈ merkleSkels b, s.leafCount ≤ B) :
    ∀ s ∈ merkleSkels (a ++ b), s.leafCount ≤ B := by
  intro s hs
  rw [NockvmE2E.Exec.E2E.merkleSkels_append] at hs
  rcases List.mem_append.1 hs with h | h
  · exact ha s h
  · exact hb s h

/-- `SampleableType` of the oracle table over the succinct range, from finiteness of everything (`Key.instFinite`, `Round.finiteChallenge`) -/
noncomputable def nv4_instTab_gen (DY Op Query Statement Salt : Type) [Finite DY] [DecidableEq DY] [Nonempty DY] [Finite Op]
    [DecidableEq Op] [Finite Query] [Finite Statement] [Finite Salt] (ms : MRounds DY) :
    SampleableType (∀ dd, succinctRange DY Op Query Statement Salt ms dd) :=
  haveI : Finite (Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DY Op ms)) := inferInstance
  haveI : Fintype (Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DY Op ms)) := Fintype.ofFinite _
  haveI hfin : ∀ dd, Finite (succinctRange DY Op Query Statement Salt ms dd) := fun dd => by
    cases dd with
    | inl _ => exact (inferInstance : Finite DY)
    | inr k => exact (inferInstance : Finite k.Challenge)
  haveI : ∀ dd, Fintype (succinctRange DY Op Query Statement Salt ms dd) := fun dd => Fintype.ofFinite _
  haveI : ∀ dd, Nonempty (succinctRange DY Op Query Statement Salt ms dd) := fun dd => by
    cases dd with
    | inl _ => exact (inferInstance : Nonempty DY)
    | inr k => exact (inferInstance : Nonempty k.Challenge)
  SampleableType.piOfFintype (fun dd => succinctRange DY Op Query Statement Salt ms dd)

section Nonempty
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ} [Fintype ι]
  (P : DeepParams Φ K ι β colRound) {r : ℕ} (A : AirShape P r) (R0 : RapStatement Φ K ι β colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ K → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ K → Prop)

theorem nv4_finite_M0 [h : Finite R0.M0] : Finite (P.statement R0 Rest).M0 := h

theorem nv4_finite_Mfin [h : Finite R0.Mfin] : Finite (deepPlan P A R0 Rest RestV).Mfin :=
  inferInstanceAs (Finite (R0.Mfin × (ι × Fin r → K) × (Fin P.nq → K)))
end Nonempty

/-! ## the datum context of the headline, at `XI0 = toy9R` -/

set_option hygiene false in
local notation "XI0" => toy9R
set_option hygiene false in
local notation "IG" => InstG.ofJ9A (XI170 XI0) hsh d hdk L R hT hσ hfree
set_option hygiene false in
local notation "hopsV" => (hops9_of_chips hsh d hchips hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops9_of_chips hsh d hchips hnum0).2.1
set_option hygiene false in
local notation "hconsV" => (hops9_of_chips hsh d hchips hnum0).2.2
set_option hygiene false in
local notation "hszV" => hsz9 hsh d hdk L R hT hσ hfree NockvmE2E.Exec.J8Chips.jDers NockvmE2E.Exec.J8Chips.jMeta hnumV hopsV
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
local notation "HNQ" => ((nq_of_shapeXF hshX).trans (hnqPJ9 XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp).symm : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (hmV9 XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp)
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
variable (hsh : shapeOkF famJ9A (XI170 toy9R) = true) (hshX : shapeXOkF famJ9A (XI170 toy9R) = true)
  (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 (XI170 toy9R) d) (R : TabRestr (J9A d hdk))
  (hT : R.T' = (XI170 toy9R).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9 (XI170 toy9R) (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)
  (hchips : chipsOkF famJ9A (XI170 toy9R) = true)
  (hnum0 : ∀ t : Fin (XI170 toy9R).tabs.size,
    (chipNumeralF famJ9A (XI170 toy9R).tabs[t].chip).getD 0 = numOf9 d (sigma9 (XI170 toy9R) t))

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
/-- ** `main_budgets_toy`**: at `XI0 = toy9R`, for the main Merkle tree of the headline, `V ≤ 2^32` together with `hterm` and `hconfig` (the binders of
`nock_e2e_J9A_succinct`, E2ESuccinct.lean:205-215), and `Q_FS`, `Q_H` with `hQFS`, `hQH`, are jointly inhabited: `V = 10 * B`, `Pn = 2 * B`,
`B = 2^12 * 2 * 2^11 + 1 + 2^13`. -/
theorem main_budgets_toy : ∃ Q_FS Q_H V Pn : ℕ, Q_FS ≤ 2 ^ 64 ∧ Q_H ≤ 2 ^ 64 ∧ V ≤ 2 ^ 32 ∧
    (∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
        (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
        claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V) ∧
    (∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn) := by
  have hnD : (XI170 XI0).nD = 13 := toy9R_nD
  -- RAP part: the four block skeletons
  have hRMs : merkleSkels (RM) = (List.range 4).map (fun i => (MDV).toRapMaskData.skel (0 + i)) :=
    NockvmE2E.Exec.E2E.merkleSkels_rapMerkleMask (Φ := extFrame (JXn).Φ0 2) (K := KC) (MDV).toRapMaskData _ I Ifin 4 0
  have hRM' : ∀ s ∈ merkleSkels (RM), s.leafCount ≤ 2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13 := by
    intro s hs
    rw [hRMs] at hs
    simp only [List.mem_map, List.mem_range] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    have := nv4_rapskel_le (2 ^ ((XI170 XI0).nD - 1)) (Wb (XI170 XI0) (0 + i)) (2 ^ 11) (toy9R_Wb (0 + i) (by omega))
    exact this.trans (by rw [hnD]; norm_num)
  -- FRI part: the `k` layer trees, `<= 2^nD` leaves
  have hBM : ∀ s ∈ merkleSkels (BM), s.leafCount ≤ 2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13 := by
    intro s hs
    have := side_leaf_le (XI170 XI0) (hn32_of_shapeF hsh) s hs
    exact this.trans (by rw [hnD]; norm_num)
  have hB : ∀ s ∈ merkleSkels (MC), s.leafCount ≤ 2 ^ 12 * 2 * 2 ^ 11 + 1 + 2 ^ 13 :=
    nv4_mem_append (RM) (BM) _ hRM' hBM
  have hlenBM : (merkleSkels (BM)).length = 6 :=
    (NockvmE2E.Merkle.SideMerkle.merkleSkels_bMask_length (S := KC) s1 1 (XI170 XI0).l LV DgJ8 encK).trans toy9R_k
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

/--  (independent binders): `Statement = Salt = Unit` with `DecidableEq`/`Finite`; `hz`; `instKC`, `iCh`, `tp`; `Finite`/`DecidableEq` of `M0`, `Mfin`;
`OracleInterface` of `M0`, of every column block, of `Mfin` (the default interface); `m0`, `mf`. -/
theorem binders_toy_indep :
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
    ⟨instKC_toy⟩, ⟨⟨0, toy9R_Jm_T_pos IG⟩⟩, ⟨iCh_toy⟩,
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
/--  (dependent binders): at `Statement = Salt = Unit`, for EVERY choice of the independent binders, the four table binders are inhabited:
`fQ`, `instTab`, `fQF`, `instTabF` (finiteness of `NQuery`, and the uniform table over the succinct range). -/
theorem binders_toy_dep :
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

end NockvmE2E.J9A.E2ESuccinctNonVac4

#print axioms NockvmE2E.J9A.E2ESuccinctNonVac4.toy9R_Wb
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac4.nv4_instTab_gen
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac4.main_budgets_toy
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac4.binders_toy_indep
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac4.binders_toy_dep
