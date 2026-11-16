import Nock.NockVMROM.Thm54.VclL.Compute.LogUpAcc

/-!
# V4T step 1b : the export / path accumulators on the VCL chip, and `reqFacts`

.

* **Two accumulators** (DESIGN §2 (II): "2 accumulators (export, path)"): export reads slot 0
  (always), slot 1 on `s2 s5 s6 s7 s8 s9`, slot 2 on `s6`; path reads slot 1 on `s0`, slot 2 on `s9`.
  Accumulator limbs `226..228` / `229..231`; terminals `ρ_export` / `ρ_path` at public limbs
  `42..44` / `45..47` (post-challenge publics, the `requests` precedent; the chip takes them through
  `pubVal`, i.e. the frame's `chip V x ρ χ`).
* **The chip** `computeChipVCLE`: `vclGatesD` plus `18` accumulator gates,
  `(e, w, s, d, k) = (3, 232, 339, 4, 2)`.  **Round correction** (`colRoundVCLE`): every column that
  reads the IO coins — the slot inverses `214..219`, `223..225` and the accumulators — is round `2`
  (the frame samples the IO coins after B1, `frameVCL.sampledAfter = 1`); `colRoundVCL` had the
  inverses at round `1`.
* **`exportReqFacts` / `pathReqFacts`**: on `N` accepted rows (shift, masks, one-hot), the active
  records of each accumulator form `SVFrame.ReqIOFacts (compress coins) ρ` (the frame's `reqFacts`
  at `Kio = K`), with `≤ 3N` / `≤ 2N` records (`exportRecords_length_le` / `pathRecords_length_le`;
  the path count is `≤ N` by one-hot, recorded, not used).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open scoped Polynomial

set_option maxRecDepth 300000

noncomputable section

/-! ## 1. Slots, columns, gates -/

def accExportBase : ℕ := 226
def accPathBase : ℕ := 229
def rhoExportPub : ℕ := 42
def rhoPathPub : ℕ := 45
def vclWidthE : ℕ := 232

section gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

def accSlotsX : List (Slot F) :=
  [⟨.const 1, inv0Base⟩, ⟨selSum slot1ExportSels, lookupInvBase 0⟩, ⟨selVar 6, lookupInvBase 1⟩]

def accSlotsP : List (Slot F) := [⟨selVar 0, lookupInvBase 0⟩, ⟨selVar 9, lookupInvBase 1⟩]

theorem exportSlots_act_degree : ∀ s ∈ accSlotsX (F := F), s.act.degree ≤ 1 := by
  intro s hs
  simp only [accSlotsX, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · simp [CoeffExpr.degree]
  · exact selSum_degree _
  · simp [selVar, CoeffExpr.degree]

theorem pathSlots_act_degree : ∀ s ∈ accSlotsP (F := F), s.act.degree ≤ 1 := by
  intro s hs
  simp only [accSlotsP, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> simp [selVar, CoeffExpr.degree]

/-- **The gates of `computeChipVCLE`**: `vclGatesD` and the two accumulators. -/
def vclGatesE (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  vclGatesD n b γc ρc ++ accGates 3 accSlotsX accExportBase rhoExportPub ++
    accGates 3 accSlotsP accPathBase rhoPathPub

theorem vclGatesE_length (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    (vclGatesE n b γc ρc).length = 339 := by
  simp [vclGatesE, vclGatesD_length, accGates_length]

theorem vclGatesE_degree (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ vclGatesE n b γc ρc, g.degree ≤ 4 := by
  intro g hg
  simp only [vclGatesE, List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact vclGatesD_degree n b γc ρc g h
  · exact (accGates_degree 3 _ exportSlots_act_degree _ _ g h).trans (by omega)
  · exact (accGates_degree 3 _ pathSlots_act_degree _ _ g h).trans (by omega)

end gates

/-- The coin-round schedule of `computeChipVCLE`: B0 as `colRoundVCLD`; every IO-coin reader
(slot inverses, accumulators) at round `2`. -/
def colRoundVCLE (c : ℕ) : ℕ :=
  if 214 ≤ c ∧ c < 220 then 2 else if c < 222 then colRoundVCL c
  else if c = fIdxCol then 0 else 2

theorem colRoundVCLE_zero_iff : ∀ c : Fin 232, colRoundVCLE c = 0 ↔ IsB0VCLD c := by
  unfold IsB0VCLD IsB0VCL axCol fIdxCol; decide +kernel

def vclRAPE {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 24]
    w := vclWidthE
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthE]
    h := h
    d := 4
    s := (vclGatesE n b γc ρc).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((vclGatesE n b γc ρc).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (vclGatesE_degree n b γc ρc _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCLE`**: `computeChipVCLD` with the export / path accumulators. -/
def computeChipVCLE
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPE (n := n) b γc ρc chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [vclRAPE]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < vclRound0
          simp only [vclRound0]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem computeChipVCLE_sat_iff
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLE hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLE hn nodes b γc ρc chalV pubVal orbit) P ↔
      (computeChipVCLE hn nodes b γc ρc chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGatesE n b γc ρc,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLE hn nodes b γc ρc chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLE hn nodes b γc ρc chalV pubVal orbit).rap.compose P i).eval x =
        ((vclGatesE n b γc ρc).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalV pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

/-- **The new chip tuple** `(3, 232, 339, 4, 2)` (was `(3, 226, 321, 4, 2)`): `+6` columns (two
`𝕂` accumulators), `+18` gates. -/
theorem vclRAPE_fingerprint
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := vclRAPE (n := n) b γc ρc chalV pubVal orbit H
    R.w = 232 ∧ R.s = 339 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 ∧ R.wRAP = ![208, 24] :=
  ⟨rfl, vclGatesE_length n b γc ρc, rfl, rfl, rfl, rfl⟩

/-! ## 2. Per-row slot data -/

section rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]

/-- The export slot activities in `K` (slot order). -/
def actX (env : Env F) : ℕ → K
  | 0 => 1
  | 1 => algebraMap F K ((selSum (F := F) slot1ExportSels).eval env)
  | 2 => algebraMap F K (env.trace 6)
  | _ => 0

def invBaseX : ℕ → ℕ
  | 0 => inv0Base
  | 1 => lookupInvBase 0
  | _ => lookupInvBase 1

def recX (b : Basis (Fin 3) F K) (env : Env F) : ℕ → Fin 10 → K
  | 0 => recVal b env formulaRec
  | 1 => recVal b env tailRec
  | _ => recVal b env ttRec

def actP (env : Env F) : ℕ → K
  | 0 => algebraMap F K (env.trace 0)
  | 1 => algebraMap F K (env.trace 9)
  | _ => 0

def invBaseP : ℕ → ℕ
  | 0 => lookupInvBase 0
  | _ => lookupInvBase 1

def recP (b : Basis (Fin 3) F K) (env : Env F) : ℕ → Fin 8 → K
  | 0 => recVal b env op0PathRec
  | _ => recVal b env op9PathRec

theorem invVal_eq_limbVal (b : Basis (Fin 3) F K) (env : Env F) (base : ℕ) :
    invVal b env base = limbVal b env.trace base := rfl

theorem termVal_export (b : Basis (Fin 3) F K) (env : Env F) :
    termVal b (accSlotsX (F := F)) env =
      ∑ s ∈ Finset.range 3, actX env s * invVal b env (invBaseX s) := by
  simp [termVal, accSlotsX, Finset.sum_range_succ, actX, invBaseX, invVal_eq_limbVal,
    Algebra.smul_def, CoeffExpr.eval, selVar, add_assoc]

theorem termVal_path (b : Basis (Fin 3) F K) (env : Env F) :
    termVal b (accSlotsP (F := F)) env =
      ∑ s ∈ Finset.range 2, actP env s * invVal b env (invBaseP s) := by
  simp [termVal, accSlotsP, Finset.sum_range_succ, actP, invBaseP, invVal_eq_limbVal,
    Algebra.smul_def, selVar, CoeffExpr.eval]

/-- One-hot selector index of a state (`opCol`). -/
def selIdx : State → ℕ
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4 | .s5 => 5 | .s6 => 6 | .s7 => 7
  | .s8 => 8 | .s9 => 9 | .cons => 10

theorem selAt_trace {env : Env F} {st : State} (h : SelAt env st) (i : ℕ) (hi : i < 11) :
    env.trace i = if i = selIdx st then 1 else 0 := by
  have := h i hi
  rw [this]; cases st <;> rfl

theorem actX_bool (env : Env F) (st : State) (h : SelAt env st) (s : ℕ) :
    actX (K := K) env s = 0 ∨ actX (K := K) env s = 1 := by
  have ht := selAt_trace h
  rcases s with _ | _ | _ | s
  · right; rfl
  · simp only [actX, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
      ht 8 (by norm_num), ht 9 (by norm_num)]
    cases st <;> simp [selIdx]
  · simp only [actX]; rw [ht 6 (by norm_num)]; cases st <;> simp [selIdx]
  · left; rfl

theorem actP_bool (env : Env F) (st : State) (h : SelAt env st) (s : ℕ) :
    actP (K := K) env s = 0 ∨ actP (K := K) env s = 1 := by
  have ht := selAt_trace h
  rcases s with _ | _ | s
  · simp only [actP]; rw [ht 0 (by norm_num)]; cases st <;> simp [selIdx]
  · simp only [actP]; rw [ht 9 (by norm_num)]; cases st <;> simp [selIdx]
  · left; rfl

/-- Active export slots have their reciprocal: `inv · compress(rec) = 1`. -/
theorem export_inv (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n : ℕ) (env : Env F) (st : State)
    (h : SelAt env st) (hg : ∀ g ∈ vclGatesE n b γc ρc, g.eval env = 0) (s : ℕ)
    (hs : s < 3) (ha : actX (K := K) env s = 1) :
    invVal b env (invBaseX s) * FiniteIO.compress (coinsAt b env γc ρc) (recX b env s) = 1 := by
  have hD : ∀ g ∈ lookupGatesD b γc ρc, g.eval env = 0 := fun g hm =>
    hg g (by simp only [vclGatesE, vclGatesD, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm)))
  have ht := selAt_trace h
  rcases s with _ | _ | _ | s
  · exact slot0_sound b γc ρc env fun g hm => hD g (by simp [lookupGatesD, hm])
  · have hx : st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9 := by
      simp only [actX, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at ha
      rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
        ht 8 (by norm_num), ht 9 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    have hsel : SelAt env st := h
    exact slot1_sound_export b γc ρc env st hsel hx fun g hm => hD g (by simp [lookupGatesD, hm])
  · have h6 : st = .s6 := by
      simp only [actX] at ha; rw [ht 6 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h6
    exact slot2_sound_s6 b γc ρc env h fun g hm => hD g (by simp [lookupGatesD, hm])
  · omega

theorem path_inv (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n : ℕ) (env : Env F) (st : State)
    (h : SelAt env st) (hg : ∀ g ∈ vclGatesE n b γc ρc, g.eval env = 0) (s : ℕ)
    (hs : s < 2) (ha : actP (K := K) env s = 1) :
    invVal b env (invBaseP s) * FiniteIO.compress (coinsAt b env γc ρc) (recP b env s) = 1 := by
  have hD : ∀ g ∈ lookupGatesD b γc ρc, g.eval env = 0 := fun g hm =>
    hg g (by simp only [vclGatesE, vclGatesD, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm)))
  have ht := selAt_trace h
  rcases s with _ | _ | s
  · have h0 : st = .s0 := by
      simp only [actP] at ha; rw [ht 0 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h0
    exact slot1_sound_s0 b γc ρc env h fun g hm => hD g (by simp [lookupGatesD, hm])
  · have h9 : st = .s9 := by
      simp only [actP] at ha; rw [ht 9 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h9
    exact slot2_sound_s9 b γc ρc env h fun g hm => hD g (by simp [lookupGatesD, hm])
  · omega

end rows

/-! ## 3. `reqFacts`: the active records of each accumulator -/

section facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]

/-- **The accepted row family** of `computeChipVCLE`: `N` row envs with the gates, the row shift,
the masks, a one-hot state, constant challenges and publics. -/
structure AcceptedRows (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n N : ℕ) (envs : ℕ → Env F)
    (chalV pubVal : ℕ → F) : Prop where
  hN : 0 < N
  gates : ∀ i < N, ∀ g ∈ vclGatesE n b γc ρc, g.eval (envs i) = 0
  shift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j
  first : (envs 0).trace 11 = 1
  notLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0
  last : (envs (N - 1)).trace 12 = 1
  sel : ∀ i < N, ∃ st, SelAt (envs i) st
  chal : ∀ i, (envs i).chal = chalV
  pub : ∀ i, (envs i).pub = pubVal

/-- The IO coins the chip's denominators read (constant over rows). -/
def coinsV (b : Basis (Fin 3) F K) (chalV : ℕ → F) (γc ρc : ℕ) : FiniteIO.IOCoins K :=
  ⟨∑ k : Fin 3, chalV (γc + (k : ℕ)) • b k, ∑ k : Fin 3, chalV (ρc + (k : ℕ)) • b k⟩

theorem coinsAt_eq (b : Basis (Fin 3) F K) (γc ρc : ℕ) (env : Env F) (chalV : ℕ → F)
    (h : env.chal = chalV) : coinsAt b env γc ρc = coinsV b chalV γc ρc := by
  simp [coinsAt, coinsV, chalVal, h]

/-- The active export records (row-major). -/
def exportRecords (b : Basis (Fin 3) F K) (N : ℕ) (envs : ℕ → Env F) : List (Fin 10 → K) :=
  activeRecords N 3 (fun i s => actX (envs i) s) (fun i s => recX b (envs i) s)

def pathRecords (b : Basis (Fin 3) F K) (N : ℕ) (envs : ℕ → Env F) : List (Fin 8 → K) :=
  activeRecords N 2 (fun i s => actP (envs i) s) (fun i s => recP b (envs i) s)

theorem exportRecords_length_le (b : Basis (Fin 3) F K) (N : ℕ) (envs : ℕ → Env F) :
    (exportRecords b N envs).length ≤ 3 * N := by
  have := activeRecords_length_le N 3 (fun i s => actX (K := K) (envs i) s)
    (fun i s => recX b (envs i) s)
  unfold exportRecords; omega

theorem pathRecords_length_le (b : Basis (Fin 3) F K) (N : ℕ) (envs : ℕ → Env F) :
    (pathRecords b N envs).length ≤ 2 * N := by
  have := activeRecords_length_le N 2 (fun i s => actP (K := K) (envs i) s)
    (fun i s => recP b (envs i) s)
  unfold pathRecords; omega

/-- **The export accumulator's `reqFacts`**: on an accepted row family, the active export records
have reciprocal compressed denominators summing to the public `ρ_export`. -/
def exportReqFacts (b : Basis (Fin 3) F K) (γc ρc n N : ℕ) (envs : ℕ → Env F) (chalV pubVal : ℕ → F)
    (A : AcceptedRows b γc ρc n N envs chalV pubVal) :
    ReqIOFacts (FiniteIO.compress (m := 10) (coinsV b chalV γc ρc)) (limbVal b pubVal rhoExportPub) := by
  classical
  let act : ℕ → ℕ → K := fun i s => if i < N then actX (envs i) s else 0
  let inv : ℕ → ℕ → K := fun i s => if act i s = 1 then invVal b (envs i) (invBaseX s) else 0
  have hbool : ∀ i s, act i s = 0 ∨ act i s = 1 := by
    intro i s
    by_cases hi : i < N
    · obtain ⟨st, hst⟩ := A.sel i hi
      simp only [act, hi, if_true]; exact actX_bool _ st hst s
    · left; simp [act, hi]
  have hinv : ∀ i s, s < 3 → inv i s *
      FiniteIO.compress (coinsV b chalV γc ρc) (recX b (envs i) s) = act i s := by
    intro i s hs
    by_cases ha : act i s = 1
    · have hi : i < N := by by_contra hi; simp [act, hi] at ha
      obtain ⟨st, hst⟩ := A.sel i hi
      have ha' : actX (K := K) (envs i) s = 1 := by simpa [act, hi] using ha
      simp only [inv, ha, if_true]
      rw [← coinsAt_eq b γc ρc (envs i) chalV (A.chal i)]
      exact export_inv b γc ρc n (envs i) st hst (A.gates i hi) s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 3, act i s * inv i s =
      limbVal b pubVal rhoExportPub := by
    have hrows := acc_rows b accSlotsX accExportBase rhoExportPub N A.hN envs
      (fun i hi g hm => A.gates i hi g (by
        simp only [vclGatesE, List.mem_append]; exact Or.inl (Or.inr hm)))
      A.shift A.first A.notLast A.last _ (by rw [A.pub])
    rw [← hrows]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    rw [termVal_export]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases hbool i s with h0 | h1
    · have : actX (K := K) (envs i) s = 0 := by simpa [act, hi'] using h0
      rw [h0, this]; ring
    · have : actX (K := K) (envs i) s = 1 := by simpa [act, hi'] using h1
      simp [inv, h1, this]
  -- restrict to `s < 3`: `act` vanishes beyond
  exact reqIOFacts_of_rows N 3 act inv (fun i s => recX b (envs i) s)
    (FiniteIO.compress (coinsV b chalV γc ρc)) _ hbool
    (fun i s => by
      by_cases hs : s < 3
      · exact hinv i s hs
      · have h0 : act i s = 0 := by
          rcases s with _ | _ | _ | s
          · omega
          · omega
          · omega
          · by_cases hi : i < N <;> simp [act, hi, actX]
        simp [inv, h0])
    hsum

/-- **The path accumulator's `reqFacts`.** -/
def pathReqFacts (b : Basis (Fin 3) F K) (γc ρc n N : ℕ) (envs : ℕ → Env F) (chalV pubVal : ℕ → F)
    (A : AcceptedRows b γc ρc n N envs chalV pubVal) :
    ReqIOFacts (FiniteIO.compress (m := 8) (coinsV b chalV γc ρc)) (limbVal b pubVal rhoPathPub) := by
  classical
  let act : ℕ → ℕ → K := fun i s => if i < N then actP (envs i) s else 0
  let inv : ℕ → ℕ → K := fun i s => if act i s = 1 then invVal b (envs i) (invBaseP s) else 0
  have hbool : ∀ i s, act i s = 0 ∨ act i s = 1 := by
    intro i s
    by_cases hi : i < N
    · obtain ⟨st, hst⟩ := A.sel i hi
      simp only [act, hi, if_true]; exact actP_bool _ st hst s
    · left; simp [act, hi]
  have hinv : ∀ i s, s < 2 → inv i s *
      FiniteIO.compress (coinsV b chalV γc ρc) (recP b (envs i) s) = act i s := by
    intro i s hs
    by_cases ha : act i s = 1
    · have hi : i < N := by by_contra hi; simp [act, hi] at ha
      obtain ⟨st, hst⟩ := A.sel i hi
      have ha' : actP (K := K) (envs i) s = 1 := by simpa [act, hi] using ha
      simp only [inv, ha, if_true]
      rw [← coinsAt_eq b γc ρc (envs i) chalV (A.chal i)]
      exact path_inv b γc ρc n (envs i) st hst (A.gates i hi) s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 2, act i s * inv i s =
      limbVal b pubVal rhoPathPub := by
    have hrows := acc_rows b accSlotsP accPathBase rhoPathPub N A.hN envs
      (fun i hi g hm => A.gates i hi g (by
        simp only [vclGatesE, List.mem_append]; exact Or.inr hm))
      A.shift A.first A.notLast A.last _ (by rw [A.pub])
    rw [← hrows]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    rw [termVal_path]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases hbool i s with h0 | h1
    · have : actP (K := K) (envs i) s = 0 := by simpa [act, hi'] using h0
      rw [h0, this]; ring
    · have : actP (K := K) (envs i) s = 1 := by simpa [act, hi'] using h1
      simp [inv, h1, this]
  exact reqIOFacts_of_rows N 2 act inv (fun i s => recP b (envs i) s)
    (FiniteIO.compress (coinsV b chalV γc ρc)) _ hbool
    (fun i s => by
      by_cases hs : s < 2
      · exact hinv i s hs
      · have h0 : act i s = 0 := by
          rcases s with _ | _ | s
          · omega
          · omega
          · by_cases hi : i < N <;> simp [act, hi, actP]
        simp [inv, h0])
    hsum

/-- The records of `exportReqFacts` are `exportRecords` (by construction). -/
theorem exportReqFacts_records (b : Basis (Fin 3) F K) (γc ρc n N : ℕ) (envs : ℕ → Env F)
    (chalV pubVal : ℕ → F) (A : AcceptedRows b γc ρc n N envs chalV pubVal) :
    (exportReqFacts b γc ρc n N envs chalV pubVal A).records.length ≤ 3 * N := by
  unfold exportReqFacts
  exact (activeRecords_length_le N 3 _ _).trans (by rw [Nat.mul_comm])

end facts

end

end VclL.Compute
end Nock.NockVMROM.Thm54
