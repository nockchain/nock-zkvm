import Nock.NockVMROM.Thm54.VclL.Compute.ReqFactsQ7
import Nock.NockVMROM.Thm54.VclL.Compute.WalkSatQ7
import Nock.NockVMROM.Thm54.VclL.RecordViewVCL

/-!
.  The export
record becomes `(p, l, r, idx, side)` (`m_x = 11`, `RecordViewVCL`); on the compute chip the side is a
per-slot CONSTANT: `1` at slot 0 (the formula cell, child `f_t`, axis 3), `0` at slots 1 / 2 (tail
cells, child = head, axis 2).  So only slot 0's denominator changes, by the constant-coin term
`γ^10 · 1` (`denVecS`); slots 1 / 2 and the path records are unchanged (side `0` adds nothing,
`compress_snoc`); the accumulators sum inverses only and are unchanged.  0 new columns, 0 new gates.

* `compress_snoc`: `compress (r ++ [s]) = compress r + γ^m · s`; `coord_compressS`, `slot0S_sound`;
* `lookupGatesDS`, `vclGatesQ7S` (321 gates, degree `≤ 4`), `vclRAPQ7S`, **`computeChipVCLQ7S`**
  (tuple `(3, 232, 321, 4, 2)`, `vclRAPQ7S_fingerprint`), `computeChipVCLQ7S_sat_iff`,
  `VclSourceObligationsQ7.of_vclGatesQ7S`, `WalkQ7.RowFactsQ7.of_satS` (so every `WalkSatQ7` result
  holds at the side chip);
* `recX11` (the 11-wide export record of slot `s`), `export_invQ7S`, `AcceptedRowsQ7S`,
  **`exportReqFactsQ7S`** (`m = 11`), `pathReqFactsQ7S`, `acceptedRowsQ7S_of_sat`;
* `recX11_view`: at `RV.recordViewVCL` the slot-`s` record has key `export (idx, s = 0)`, child
  `f_t` / the head, axis `3` / `2` — the three `node_records` value clauses are record-determined;
* `computeChipQ7S` at `frameVCL` coins.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State FP)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeFinal Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open scoped Polynomial

set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The side term -/

theorem compress_snoc {K : Type} [Field K] (coins : FiniteIO.IOCoins K) {m : ℕ} (v : Fin m → K) (s : K) :
    FiniteIO.compress coins (Fin.snoc (α := fun _ => K) v s) =
      FiniteIO.compress coins v + coins.gamma ^ m * s := by
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.coe_castSucc, Fin.val_last]
  ring

/-- **NC (the side is read)**: at a nonzero record coin, side `1` changes the compressed denominator,
so the 10-wide (side-less) slot-0 inverse is not the 11-wide one. -/
theorem side_term_ne {K : Type} [Field K] (coins : FiniteIO.IOCoins K) {m : ℕ} (v : Fin m → K)
    (hγ : coins.gamma ≠ 0) :
    FiniteIO.compress coins (Fin.snoc (α := fun _ => K) v 1) ≠ FiniteIO.compress coins v := by
  rw [compress_snoc, mul_one]
  intro h
  exact pow_ne_zero m hγ (by linear_combination h)

section gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem chalVec_degree (c : ℕ) (j : Fin 3) : (chalVec (F := F) c j).degree ≤ 0 := by
  simp [chalVec, CoeffExpr.degree]

/-- **Slot 0's denominator with the side `1`**: `den(formulaRec) + γ^10`. -/
def denVecS (b : Basis (Fin 3) F K) (γc ρc : ℕ) {m : ℕ} (r : Fin m → Entry) : Fin 3 → CoeffExpr F :=
  fun k => .add (denVec b γc ρc r k) (powVec b (chalVec γc) m k)

theorem denVecS_degree (b : Basis (Fin 3) F K) (γc ρc : ℕ) {m : ℕ} (r : Fin m → Entry) (k : Fin 3) :
    (denVecS b γc ρc r k).degree ≤ 1 := by
  simp only [denVecS, CoeffExpr.degree]
  refine max_le (denVec_degree b γc ρc r k) ?_
  have := degree_powVec_le b (chalVec γc) 0 (chalVec_degree γc) m k
  omega

/-- **Slot 0's gates at the side chip**: `inv₀ · (den₀ + γ^10) − 1 = 0`. -/
def slot0GatesS (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  lookupInvGates b inv0Base (denVecS b γc ρc formulaRec)

def lookupGatesDS (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  slot0GatesS b γc ρc ++ slot1Gates b γc ρc ++ slot2Gates b γc ρc

theorem lookupGatesDS_length (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    (lookupGatesDS b γc ρc).length = 9 := by
  simp [lookupGatesDS, slot0GatesS, slot1Gates, slot2Gates]

theorem lookupGatesDS_degree (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ lookupGatesDS b γc ρc, g.degree ≤ 3 := by
  intro g hg
  simp only [lookupGatesDS, List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact (lookupInvGates_degree b inv0Base _ 1 (denVecS_degree b γc ρc formulaRec) g h).trans
      (by omega)
  · exact slot1Gates_degree b γc ρc g h
  · exact slot2Gates_degree b γc ρc g h

/-- **The gates of the side chip**: `vclGatesQ7` with `lookupGatesDS`. -/
def vclGatesQ7S (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  ((keptGatesQ7 n b).map reindexE ++ serialGates) ++ axGates b ++ lookupGatesDS b γc ρc ++
    accGates 3 accSlotsX accExportBase rhoExportPub ++ accGates 3 accSlotsP accPathBase rhoPathPub

theorem vclGatesQ7S_length (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    (vclGatesQ7S n b γc ρc).length = 321 := by
  have h := vclGatesQ7_length n b γc ρc
  simp only [vclGatesQ7, List.length_append, lookupGatesD_length] at h
  simp only [vclGatesQ7S, List.length_append, lookupGatesDS_length]
  omega

theorem vclGatesQ7S_degree (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ vclGatesQ7S n b γc ρc, g.degree ≤ 4 := by
  intro g hg
  simp only [vclGatesQ7S, List.mem_append] at hg
  rcases hg with ((((hk | hs) | hax) | hl) | hx) | hp
  · exact vclGatesQ7_degree n b γc ρc g (by
      simp only [vclGatesQ7, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hk)))))
  · exact vclGatesQ7_degree n b γc ρc g (by
      simp only [vclGatesQ7, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs)))))
  · exact vclGatesQ7_degree n b γc ρc g (by
      simp only [vclGatesQ7, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hax))))
  · exact (lookupGatesDS_degree b γc ρc g hl).trans (by omega)
  · exact vclGatesQ7_degree n b γc ρc g (by
      simp only [vclGatesQ7, List.mem_append]; exact Or.inl (Or.inr hx))
  · exact vclGatesQ7_degree n b γc ρc g (by
      simp only [vclGatesQ7, List.mem_append]; exact Or.inr hp)

end gates

section sound
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem coord_compressS (b : Basis (Fin 3) F K) (envF : Env F) (γc ρc : ℕ) {m : ℕ}
    (r : Fin m → Entry) (k : Fin 3) :
    coord b (FiniteIO.compress (coinsAt b envF γc ρc) (Fin.snoc (α := fun _ => K) (recVal b envF r) 1)) k =
      (denVecS b γc ρc r k).eval envF := by
  rw [compress_snoc, mul_one, coord_add, coord_compress]
  simp only [denVecS, CoeffExpr.eval]
  congr 1
  exact eval_powVec b envF (chalVec γc) (chalVal b envF γc) (fun j => coord_chalVal b envF γc j) m k

/-- **Slot 0 at the side chip**: `inv₀` is the reciprocal of the compressed 11-wide formula-cell
record (side `1`). -/
theorem slot0S_sound (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envF : Env F)
    (h : ∀ g ∈ slot0GatesS b γc ρc, g.eval envF = 0) :
    invVal b envF inv0Base *
      FiniteIO.compress (coinsAt b envF γc ρc) (Fin.snoc (α := fun _ => K) (recVal b envF formulaRec) 1) = 1 :=
  lookupInvGates_sound b inv0Base _ envF _ _ (fun j => coord_invVal b envF inv0Base j)
    (fun j => coord_compressS b envF γc ρc formulaRec j) h

end sound

/-! ## 2. The side chip -/

def vclRAPQ7S {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 24]
    w := vclWidthE
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthE]
    h := h
    d := 4
    s := (vclGatesQ7S n b γc ρc).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((vclGatesQ7S n b γc ρc).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (vclGatesQ7S_degree n b γc ρc _ (List.get_mem _ _))
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

/-- **`computeChipVCLQ7S`**: the Q7 chip with the side slot in slot 0's denominator. -/
def computeChipVCLQ7S
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPQ7S (n := n) b γc ρc chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [vclRAPQ7S]
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

theorem computeChipVCLQ7S_sat_iff
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7S hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLQ7S hn nodes b γc ρc chalV pubVal orbit) P ↔
      (computeChipVCLQ7S hn nodes b γc ρc chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGatesQ7S n b γc ρc,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLQ7S hn nodes b γc ρc chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLQ7S hn nodes b γc ρc chalV pubVal orbit).rap.compose P i).eval x =
        ((vclGatesQ7S n b γc ρc).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
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



/-- **The side-chip tuple** `(3, 232, 321, 4, 2)` (unchanged from Q7: no column, no gate). -/
theorem vclRAPQ7S_fingerprint
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := vclRAPQ7S (n := n) b γc ρc chalV pubVal orbit H
    R.w = 232 ∧ R.s = 321 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 ∧ R.wRAP = ![208, 24] :=
  ⟨rfl, vclGatesQ7S_length n b γc ρc, rfl, rfl, rfl, rfl⟩

/-- **The side chip at `frameVCL` coins** (`γc = 21`, `ρc = 24`). -/
def computeChipQ7S
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (χ : Coins frameVCL K) (pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    FixedPreprocessingRAP F :=
  computeChipVCLQ7S hn nodes b 21 24 (chalVQ7 b χ) pubVal orbit

section obligations
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Acceptance of the Q7 gates at a VCL row gives the kept Q7 gates at the pull-back. -/
theorem keptGatesQ7_of_vclGatesQ7S (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envV : Env F)
    (h : ∀ g ∈ vclGatesQ7S n b γc ρc, g.eval envV = 0) :
    ∀ g ∈ keptGatesQ7 n b, g.eval (pullEnv envV) = 0 := by
  intro g hg
  have hr := h (reindexE g) (by
    simp only [vclGatesQ7S, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hg, rfl⟩)))))
  rwa [eval_reindexE g (pullEnv envV) envV (keptGates309_colsIn n b g (keptGatesQ7_sub n b g hg))
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl] at hr

/-- **Acceptance of the Q7 gates at a VCL row gives the Q7 obligations** at the gathered
pull-back. -/
theorem VclSourceObligationsQ7.of_vclGatesQ7S (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ)
    (envV : Env F) (h : ∀ g ∈ vclGatesQ7S n b γc ρc, g.eval envV = 0) :
    VclSourceObligationsQ7 n (gather309 b (pullEnv envV)) (pullEnv envV) :=
  VclSourceObligationsQ7.of_kept n b _ (keptGatesQ7_of_vclGatesQ7S n b γc ρc envV h)


end obligations

/-! ## 3. The 11-wide export record and `reqFacts` -/

section recs
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The side of export slot `s`: `1` at slot 0, `0` elsewhere. -/
def sideVal (s : ℕ) : K := if s = 0 then 1 else 0

theorem sideVal_ne (s : ℕ) (hs : s ≠ 0) : sideVal (K := K) s = 0 := if_neg hs

/-- **The 11-wide export record of slot `s`**: `recX` with the side appended. -/
def recX11 (b : Basis (Fin 3) F K) (env : Env F) (s : ℕ) : Fin 11 → K :=
  Fin.snoc (α := fun _ => K) (recX b env s) (sideVal s)

theorem compress_recX11 (coins : FiniteIO.IOCoins K) (b : Basis (Fin 3) F K) (env : Env F) (s : ℕ) :
    FiniteIO.compress coins (recX11 b env s) =
      FiniteIO.compress coins (recX b env s) + coins.gamma ^ 10 * sideVal s :=
  compress_snoc coins _ _

end recs

section rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]

/-- Active export slots have their reciprocal: `inv · compress(rec) = 1`. -/
theorem export_invQ7S (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n : ℕ) (env : Env F) (st : State)
    (h : SelAt env st) (hg : ∀ g ∈ vclGatesQ7S n b γc ρc, g.eval env = 0) (s : ℕ)
    (hs : s < 3) (ha : actX (K := K) env s = 1) :
    invVal b env (invBaseX s) * FiniteIO.compress (coinsAt b env γc ρc) (recX11 b env s) = 1 := by
  have hD : ∀ g ∈ lookupGatesDS b γc ρc, g.eval env = 0 := fun g hm =>
    hg g (by simp only [vclGatesQ7S, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm)))
  have ht := selAt_trace h
  rcases s with _ | _ | _ | s
  · exact slot0S_sound b γc ρc env fun g hm => hD g (by simp [lookupGatesDS, hm])
  · have hx : st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9 := by
      simp only [actX, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at ha
      rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
        ht 8 (by norm_num), ht 9 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    have hsel : SelAt env st := h
    rw [compress_recX11, sideVal_ne 1 (by decide), mul_zero, add_zero]
    exact slot1_sound_export b γc ρc env st hsel hx fun g hm => hD g (by simp [lookupGatesDS, hm])
  · have h6 : st = .s6 := by
      simp only [actX] at ha; rw [ht 6 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h6
    rw [compress_recX11, sideVal_ne 2 (by decide), mul_zero, add_zero]
    exact slot2_sound_s6 b γc ρc env h fun g hm => hD g (by simp [lookupGatesDS, hm])
  · omega

theorem path_invQ7S (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n : ℕ) (env : Env F) (st : State)
    (h : SelAt env st) (hg : ∀ g ∈ vclGatesQ7S n b γc ρc, g.eval env = 0) (s : ℕ)
    (hs : s < 2) (ha : actP (K := K) env s = 1) :
    invVal b env (invBaseP s) * FiniteIO.compress (coinsAt b env γc ρc) (recP b env s) = 1 := by
  have hD : ∀ g ∈ lookupGatesDS b γc ρc, g.eval env = 0 := fun g hm =>
    hg g (by simp only [vclGatesQ7S, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm)))
  have ht := selAt_trace h
  rcases s with _ | _ | s
  · have h0 : st = .s0 := by
      simp only [actP] at ha; rw [ht 0 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h0
    exact slot1_sound_s0 b γc ρc env h fun g hm => hD g (by simp [lookupGatesDS, hm])
  · have h9 : st = .s9 := by
      simp only [actP] at ha; rw [ht 9 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h9
    exact slot2_sound_s9 b γc ρc env h fun g hm => hD g (by simp [lookupGatesDS, hm])
  · omega



end rows

section facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]

structure AcceptedRowsQ7S (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n N : ℕ) (envs : ℕ → Env F)
    (chalV pubVal : ℕ → F) : Prop where
  hN : 0 < N
  gates : ∀ i < N, ∀ g ∈ vclGatesQ7S n b γc ρc, g.eval (envs i) = 0
  shift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j
  first : (envs 0).trace 11 = 1
  notLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0
  last : (envs (N - 1)).trace 12 = 1
  sel : ∀ i < N, ∃ st, SelAt (envs i) st
  chal : ∀ i, (envs i).chal = chalV
  pub : ∀ i, (envs i).pub = pubVal

/-- **The export accumulator's `reqFacts`**: on an accepted row family, the active export records
have reciprocal compressed denominators summing to the public `ρ_export`. -/
def exportReqFactsQ7S (b : Basis (Fin 3) F K) (γc ρc n N : ℕ) (envs : ℕ → Env F) (chalV pubVal : ℕ → F)
    (A : AcceptedRowsQ7S b γc ρc n N envs chalV pubVal) :
    ReqIOFacts (FiniteIO.compress (m := 11) (coinsV b chalV γc ρc)) (limbVal b pubVal rhoExportPub) := by
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
      FiniteIO.compress (coinsV b chalV γc ρc) (recX11 b (envs i) s) = act i s := by
    intro i s hs
    by_cases ha : act i s = 1
    · have hi : i < N := by by_contra hi; simp [act, hi] at ha
      obtain ⟨st, hst⟩ := A.sel i hi
      have ha' : actX (K := K) (envs i) s = 1 := by simpa [act, hi] using ha
      simp only [inv, ha, if_true]
      rw [← coinsAt_eq b γc ρc (envs i) chalV (A.chal i)]
      exact export_invQ7S b γc ρc n (envs i) st hst (A.gates i hi) s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 3, act i s * inv i s =
      limbVal b pubVal rhoExportPub := by
    have hrows := acc_rows b accSlotsX accExportBase rhoExportPub N A.hN envs
      (fun i hi g hm => A.gates i hi g (by
        simp only [vclGatesQ7S, List.mem_append]; exact Or.inl (Or.inr hm)))
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
  exact reqIOFacts_of_rows N 3 act inv (fun i s => recX11 b (envs i) s)
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
def pathReqFactsQ7S (b : Basis (Fin 3) F K) (γc ρc n N : ℕ) (envs : ℕ → Env F) (chalV pubVal : ℕ → F)
    (A : AcceptedRowsQ7S b γc ρc n N envs chalV pubVal) :
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
      exact path_invQ7S b γc ρc n (envs i) st hst (A.gates i hi) s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 2, act i s * inv i s =
      limbVal b pubVal rhoPathPub := by
    have hrows := acc_rows b accSlotsP accPathBase rhoPathPub N A.hN envs
      (fun i hi g hm => A.gates i hi g (by
        simp only [vclGatesQ7S, List.mem_append]; exact Or.inr hm))
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


end facts

section chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The one-hot state in `𝔽` from the gates** of `computeChipVCLE` at a row. -/
theorem selAt_of_gatesQ7S [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) (env : Env F)
    (hg : ∀ g ∈ vclGatesQ7S n b γc ρc, g.eval env = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) : ∃ st, SelAt env st := by
  have hs := VclSourceObligationsQ7.of_vclGatesQ7S n b γc ρc env hg
  obtain ⟨st, hone⟩ := oneHot_of_base15 n b _ hs.base15 hchar
  refine ⟨st, fun i hi => ?_⟩
  obtain ⟨t, rfl⟩ := exists_selIdx i hi
  have h1 := hone t
  rw [selIdx_opCol, source_trace_base _ _ (by cases t <;> decide)] at h1
  have h2 : (pullEnv env).trace (selIdx t) = env.trace (selIdx t) :=
    pullEnv_trace_lt _ _ (by cases t <;> decide)
  change algebraMap F K ((pullEnv env).trace (selIdx t)) = _ at h1
  rw [h2] at h1
  have hF : env.trace (selIdx t) = if t = st then 1 else 0 := by
    by_cases ht : t = st
    · rw [if_pos ht] at h1 ⊢
      exact (algebraMap F K).injective (by rw [h1, map_one])
    · rw [if_neg ht] at h1 ⊢
      exact (algebraMap F K).injective (by rw [h1, map_zero])
  cases st <;> cases t <;> simpa [selIdx] using hF

/-- **Acceptance gives an accepted row family**, hence the chip's `reqFacts`. -/
theorem acceptedRowsQ7S_of_sat [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (γc ρc : ℕ)
    (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7S hn nodes b γc ρc chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) :
    AcceptedRowsQ7S b γc ρc n n (rowEnvs (h := h) nodes orbit.ω P chalV pubVal) chalV pubVal := by
  have hs := (computeChipVCLQ7S_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP
  have hmem : ∀ i (hi : i < n), nodes ⟨i, hi⟩ ∈ rowNodeSet nodes := fun i hi => by simp [rowNodeSet]
  have henv : ∀ i (hi : i < n), rowEnvs (h := h) nodes orbit.ω P chalV pubVal i =
      envOfTrace P orbit.ω (nodes ⟨i, hi⟩) chalV pubVal := fun i hi => by simp [rowEnvs, hi]
  have hgates : ∀ i < n, ∀ g ∈ vclGatesQ7S n b γc ρc,
      g.eval (rowEnvs (h := h) nodes orbit.ω P chalV pubVal i) = 0 := by
    intro i hi g hg
    rw [henv i hi]; exact hs.2 _ (hmem i hi) g hg
  have h11 : (11 : ℕ) < 232 := by norm_num
  have h12 : (12 : ℕ) < 232 := by norm_num
  have m0 : P ⟨11, h11⟩ = firstRowMask nodes := hs.1 ⟨0, by change 0 < 2; norm_num⟩
  have m1 : P ⟨12, h12⟩ = lastRowMask hn nodes := hs.1 ⟨1, by change 1 < 2; norm_num⟩
  have htr11 : ∀ i (hi : i < n), (rowEnvs (h := h) nodes orbit.ω P chalV pubVal i).trace 11 =
      if i = 0 then 1 else 0 := by
    intro i hi
    rw [henv i hi]
    simp only [envOfTrace, dif_pos h11]
    rw [m0, Nock.Framework.firstRowMask_eval _ hinj]
  have htr12 : ∀ i (hi : i < n), (rowEnvs (h := h) nodes orbit.ω P chalV pubVal i).trace 12 =
      if i = n - 1 then 1 else 0 := by
    intro i hi
    rw [henv i hi]
    simp only [envOfTrace, dif_pos h12]
    rw [m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]
  refine ⟨hn, hgates, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j
    rw [henv i (by omega), henv (i + 1) hi]
    have ha := hadj ⟨i, by omega⟩ hi
    simp only [envOfTrace]
    split_ifs with hj
    · rw [ha]
    · rfl
  · rw [htr11 0 hn, if_pos rfl]
  · intro i hi
    rw [htr12 i (by omega), if_neg (by omega)]
  · rw [htr12 (n - 1) (by omega), if_pos rfl]
  · intro i hi
    exact selAt_of_gatesQ7S n b γc ρc _ (hgates i hi) hchar
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl




end chip

/-! ## 4. The record view of the side records -/

section view
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {C : TableSpec} {S : MemShape} {hC : ℕ}

/-- **`recX11` at the shared record view**: key `export (idx, s = 0)`, axis `3` at slot 0 and `2`
at slots 1 / 2, child the record's `l` (entries 3..5) or, at slot 0, its `r` (entries 6..8). -/
theorem recX11_view (b : Basis (Fin 3) F K) (env : Env F) (s : ℕ) (V : VerifierData F K hC S)
    (b0c : B0Cols F C) (bm : ∀ t, B0Cols F (S.table t)) :
    (RV.recordViewVCL F K K C S hC).key 1 (recX11 b env s) =
        .export (RecordCarrier.natLift (recX b env s 9)) (decide (s = 0)) ∧
      (RV.recordViewVCL F K K C S hC).axis 1 V b0c bm (recX11 b env s) = (if s = 0 then 3 else 2) ∧
      (RV.recordViewVCL F K K C S hC).child 1 (recX11 b env s) =
        (if s = 0 then ⟨recX b env s 6, recX b env s 7, recX b env s 8⟩
          else ⟨recX b env s 3, recX b env s 4, recX b env s 5⟩) := by
  obtain ⟨hk, -, hc, ha⟩ := RV.recordViewVCL_export (C := C) (recX11 b env s) V b0c bm
  have h10 : recX11 b env s 10 = sideVal s := by
    unfold recX11; exact Fin.snoc_last (α := fun _ => K) _ _
  have hlt : ∀ i : ℕ, (hi : i < 10) → recX11 b env s ⟨i, by omega⟩ = recX b env s ⟨i, hi⟩ := by
    intro i hi
    simp [recX11, Fin.snoc, hi]
  have h9 : recX11 b env s 9 = recX b env s 9 := hlt 9 (by omega)
  by_cases hs : s = 0
  · have h1 : recX11 b env s 10 = 1 := by rw [h10, hs]; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hk, h9, RV.sideOf, h1]; simp [hs]
    · rw [ha, if_pos h1, if_pos hs]
    · rw [hc, if_pos h1, if_pos hs]
      simp only [RV.fpAt]
      rw [hlt 6 (by omega), hlt 7 (by omega), hlt 8 (by omega)]; rfl
  · have h1 : recX11 b env s 10 ≠ 1 := by rw [h10, sideVal_ne s hs]; exact zero_ne_one
    refine ⟨?_, ?_, ?_⟩
    · rw [hk, h9, RV.sideOf]; simp [h1, hs]
    · rw [ha, if_neg h1, if_neg hs]
    · rw [hc, if_neg h1, if_neg hs]
      simp only [RV.fpAt]
      rw [hlt 3 (by omega), hlt 4 (by omega), hlt 5 (by omega)]; rfl

end view

end

namespace WalkQ7
open Nock.NockVMROM.Thm54.OptimizedStrictPackage Nock.NockVMROM.Thm54.SVCompute

section rf
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
  (D : ChipData F K h) (chalV pubVal : ℕ → F) (Q : Fin vclWidthE → F[X])

/-- **Acceptance at `computeChipVCLQ7S` gives the Q7 row facts** (injective nodes only). -/
theorem RowFactsQ7.of_satS (γc ρc : ℕ) (hinj : D.Injective)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S D.hN D.nodes D.basis γc ρc chalV pubVal D.orbit) Q) :
    RowFactsQ7 D.toG chalV pubVal Q := by
  have hs := (computeChipVCLQ7S_sat_iff D.hN D.nodes D.basis γc ρc chalV pubVal D.orbit Q).1 hsat
  have hmem : ∀ i : Fin D.N, D.nodes i ∈ rowNodeSet D.nodes := fun i => by simp [rowNodeSet]
  have h11 : (11 : ℕ) < vclWidthE := by norm_num [vclWidthE]
  have h12 : (12 : ℕ) < vclWidthE := by norm_num [vclWidthE]
  have m0 : Q ⟨11, h11⟩ = firstRowMask D.nodes := hs.1 ⟨0, by change 0 < 2; norm_num⟩
  have m1 : Q ⟨12, h12⟩ = lastRowMask D.hN D.nodes := hs.1 ⟨1, by change 1 < 2; norm_num⟩
  refine ⟨fun i => VclSourceObligationsQ7.of_vclGatesQ7S D.N D.basis γc ρc _ (hs.2 _ (hmem i)),
    fun (i : Fin D.N) => ⟨?_, ?_⟩⟩
  · simp only [envQ, envOfTrace, dif_pos h11, SVCompute.ChipData.toG]
    rw [m0, Nock.Framework.firstRowMask_eval _ hinj]
  · simp only [envQ, envOfTrace, dif_pos h12, SVCompute.ChipData.toG]
    rw [m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]
    first | rfl | congr


end rf
end WalkQ7

end VclL.Compute
end Nock.NockVMROM.Thm54
