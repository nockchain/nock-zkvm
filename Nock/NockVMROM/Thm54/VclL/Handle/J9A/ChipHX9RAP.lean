/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ChipHX9RAP.lean

The twin `ChipHX9` (width 137) APPENDS its round-0 columns `123..136` AFTER the J-8 round-1 block
  `69..122`.  `RAP.wRAP` is prefix-ordered (round 0 = the first `wRAP 0` columns), so the assembly
  applies an explicit column PERMUTATION `permX9` to the final (compiled) base-field gate list:

  | twin column | RAP column | round |
  |---|---|---|
  | `0..68` | `0..68` | 0 |
  | `123..136` | `69..82` | 0 |
  | `69..122` | `83..136` | 1 |

  `wRAP = ![83, 54]`.  The twin's gate list (`gatesHX9`, in twin columns) is NOT edited; the RAP's
  constraints are `(gatesHX9 b δ).map (renC permX9)` (`gatesHX9P`), related to the twin's gates by
  `eval_renC` (a gate at permuted columns = the twin gate on the permuted environment) and
  `permX9_*` (bijection `[0,137) → [0,137)`, the round split).  Preprocessing columns `17, 18` are
  fixed by `permX9`.

  Also here: `walkGatesX9`, the J-8 walk gates over
  `statesX9` and `childrenX9`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9

namespace Nock.NockVMROM.Thm54
namespace VclL.Handle
namespace ChipHX9

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.Framework

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The column permutation -/

/-- **The round permutation** twin column ↦ RAP column: round 0 is `0..68 ++ 123..136`
(RAP columns `0..82`), round 1 is the J-8 coin block `69..122` (RAP columns `83..136`). -/
def permX9 (c : ℕ) : ℕ := if c < 69 then c else if c < 123 then c + 14 else c - 54

def round0WX9 : ℕ := 83

theorem permX9_lt {c : ℕ} (h : c < widthHX9) : permX9 c < widthHX9 := by
  simp only [permX9, widthHX9] at *; split_ifs <;> omega

theorem permX9_inj {c d : ℕ} (hc : c < widthHX9) (hd : d < widthHX9) (h : permX9 c = permX9 d) :
    c = d := by
  simp only [permX9, widthHX9] at *; split_ifs at h <;> omega

theorem permX9_surj {d : ℕ} (hd : d < widthHX9) : ∃ c, c < widthHX9 ∧ permX9 c = d := by
  simp only [permX9, widthHX9] at *
  by_cases h1 : d < 69
  · exact ⟨d, by omega, by simp [h1]⟩
  · by_cases h2 : d < 83
    · exact ⟨d + 54, by omega, by split_ifs <;> omega⟩
    · exact ⟨d - 14, by omega, by split_ifs <;> omega⟩

/-- The round split: twin columns `0..68` and `123..136` land in round 0 (`< 83`), `69..122` in round 1. -/
theorem permX9_round0_iff {c : ℕ} (hc : c < widthHX9) :
    permX9 c < round0WX9 ↔ (c < 69 ∨ 123 ≤ c) := by
  simp only [permX9, round0WX9, widthHX9] at *; split_ifs <;> omega

theorem permX9_fixes_pre (c : ℕ) (h : c < 69) : permX9 c = c := by simp [permX9, h]

theorem round0X9_tiles : round0WX9 = round0WX + 14 ∧ widthHX9 = round0WX9 + 54 := by
  refine ⟨?_, ?_⟩ <;> simp [round0WX9, round0WX, widthHX9]

/-! ## 2. Column renaming on compiled gates -/

section Ren
variable {F : Type} [Field F]

/-- Rename the trace columns (current and next row) of a base-field gate. -/
def renC (π : ℕ → ℕ) : CoeffExpr F → CoeffExpr F
  | .const c => .const c
  | .var .traceCur i => .var .traceCur (π i)
  | .var .traceNext i => .var .traceNext (π i)
  | .var .challenge i => .var .challenge i
  | .var .publicVal i => .var .publicVal i
  | .add a b => .add (renC π a) (renC π b)
  | .sub a b => .sub (renC π a) (renC π b)
  | .mul a b => .mul (renC π a) (renC π b)
  | .neg a => .neg (renC π a)
  | .pow a n => .pow (renC π a) n

/-- The environment read through the renaming. -/
def Env.viaPerm (π : ℕ → ℕ) (env : Env F) : Env F :=
  { env with trace := fun i => env.trace (π i), traceNext := fun i => env.traceNext (π i) }

theorem eval_renC (π : ℕ → ℕ) (g : CoeffExpr F) (env : Env F) :
    (renC π g).eval env = g.eval (Env.viaPerm π env) := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b ha hb => simp only [renC, CoeffExpr.eval, ha, hb]
  | sub a b ha hb => simp only [renC, CoeffExpr.eval, ha, hb]
  | mul a b ha hb => simp only [renC, CoeffExpr.eval, ha, hb]
  | neg a ha => simp only [renC, CoeffExpr.eval, ha]
  | pow a n ha => simp only [renC, CoeffExpr.eval, ha]

theorem degree_renC (π : ℕ → ℕ) (g : CoeffExpr F) : (renC π g).degree = g.degree := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b ha hb => simp only [renC, CoeffExpr.degree, ha, hb]
  | sub a b ha hb => simp only [renC, CoeffExpr.degree, ha, hb]
  | mul a b ha hb => simp only [renC, CoeffExpr.degree, ha, hb]
  | neg a ha => simp only [renC, CoeffExpr.degree, ha]
  | pow a n ha => simp only [renC, CoeffExpr.degree, ha]

end Ren

/-! ## 3. The twin's gate list (twin columns), with the walk gates over 20 states -/

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

def childSumX9 (kind : VarKind) (st : ℕ) : MixedExpr F :=
  sumM (((childrenX9 st).zipIdx).map fun p =>
    .Mul (.Pow (.Var .challenge chalAlphaW) (p.2 + 1)) (rlcKeyL kind chalGammaW 0 p.1))

def ccLX9 (kind : VarKind) : MixedExpr F :=
  sumM (statesX9.map fun st => .Scale (kv kind st) (childSumX9 kind st))

def cmLX9 (kind : VarKind) : MixedExpr F :=
  sumM (statesX9.map fun st => .Scale (kv kind st) (.Pow (.Var .challenge chalAlphaW) (childrenX9 st).length))

/-- **The walk gates over the 20 states** (`walkGatesX` with `statesX9`, `childrenX9`). -/
def walkGatesX9 : List (MixedExpr F) :=
  let αW : MixedExpr F := .Var .challenge chalAlphaW
  let lnC := wv .traceCur wLnX; let lnN := wv .traceNext wLnX
  let cnC := wv .traceCur wCntX; let cnN := wv .traceNext wCntX
  let acC := wv .traceCur wAccX; let acN := wv .traceNext wAccX
  [.Scale (notC lastX) (.Sub lnN (.Mul αW lnC)),
   .Scale (notC lastX) (.Sub cnN (.Mul cnC (cmLX9 .traceNext))),
   .Scale (notC lastX) (.Sub (.Sub (.Add (.Mul lnN (curLX .traceNext)) acN) acC) (.Mul cnC (ccLX9 .traceNext))),
   .Scale (cc firstX) (.Sub lnC αW),
   .Scale (cc firstX) (.Sub cnC (.Mul (.Var .publicVal pubIC) (cmLX9 .traceCur))),
   .Scale (cc firstX) (.Sub (.Add (.Mul lnC (curLX .traceCur)) acC)
      (.Add (.Mul (.Var .publicVal pubIC) (ccLX9 .traceCur)) (.Var .publicVal pubSeed))),
   .Scale (notC lastX) (.Sub (.Mul (wv .traceCur wInvX) (.Sub cnC lnC)) (.Const 1)),
   .Scale (cc lastX) (.Sub cnC lnC),
   .Scale (cc lastX) (.Sub acC (.Var .publicVal pubOut))]

def baseGatesFX9 : List (CoeffExpr F) := (baseGatesHX9).map (mapC (fun q : ℚ => (q : F)))

def walkGatesFX9 : List (MixedExpr F) := (walkGatesX9 (F := ℚ)).map (mapM (fun q : ℚ => (q : F)))

/-- **The twin's compiled gate list, in TWIN columns** (base, the four slot pairs, the walk gates). -/
def gatesHX9 (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  baseGatesFX9 ++ (slotPairsX9 F δ).flatMap (qGates b) ++
    (walkGatesFX9 (F := F)).flatMap fun g => List.ofFn (mixedCompile b col0Id g)

/-- **The RAP's gate list**: the twin's gates at permuted columns. -/
def gatesHX9P (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  (gatesHX9 b δ).map (renC permX9)

theorem walkTemplateX9_degree :
    ((walkGatesX9 (F := ℚ)).all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem baseGatesFX9_degree : ∀ g ∈ (baseGatesFX9 : List (CoeffExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapC]
  simpa using List.all_eq_true.mp baseTemplateX9_degree t ht

theorem walkGatesFX9_degree : ∀ g ∈ (walkGatesFX9 : List (MixedExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapM]
  simpa using List.all_eq_true.mp walkTemplateX9_degree t ht

/-- Degree `≤ 4` for every twin gate. -/
theorem gatesHX9_degree (b : Basis (Fin 3) F K) (δ : F) : ∀ g ∈ gatesHX9 b δ, g.degree ≤ 4 := by
  intro g hg
  simp only [gatesHX9, List.mem_append, List.mem_flatMap, List.mem_ofFn] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨m, hm, k, rfl⟩
  · exact baseGatesFX9_degree g hg
  · have hd := slotPairsX9_degree δ q hq
    simp only [qGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact (mixedCompile_degree_le b _ q.1 k).trans (le_trans (le_max_left _ _) hd)
    · exact (mixedCompile_degree_le b _ q.2 k).trans (le_trans (le_max_right _ _) hd)
  · exact (mixedCompile_degree_le b _ m k).trans (walkGatesFX9_degree m hm)

theorem gatesHX9P_degree (b : Basis (Fin 3) F K) (δ : F) : ∀ g ∈ gatesHX9P b δ, g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_renC]
  exact gatesHX9_degree b δ t ht

/-- **The permuted chip's gates are the twin's gates at permuted columns.** -/
theorem gatesHX9P_eval (b : Basis (Fin 3) F K) (δ : F) (env : Env F) :
    (∀ g ∈ gatesHX9P b δ, g.eval env = 0) ↔
      ∀ g ∈ gatesHX9 b δ, g.eval (Env.viaPerm permX9 env) = 0 := by
  constructor
  · intro h g hg
    have := h _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rwa [eval_renC] at this
  · intro h g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    rw [eval_renC]; exact h t ht

theorem gatesHX9P_length (b : Basis (Fin 3) F K) (δ : F) :
    (gatesHX9P b δ).length = (gatesHX9 b δ).length := List.length_map _

end Gates

/-! ## 4. The RAP and the chip -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Generic form of the `I_bound` obligation (abstract width, avoids unfolding `Fin 137`). -/
theorem Ibound9 (w h : ℕ) (hpos : 0 < h) :
    ∀ q ∈ (Finset.univ ×ˢ ({0, 1} : Finset ℕ) : Finset (Fin w × ℕ)), q.2 < 2 ^ h := by
  intro q hq
  have h2 : q.2 ∈ ({0, 1} : Finset ℕ) := (Finset.mem_product.mp hq).2
  have hge : 2 ≤ 2 ^ h := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hpos
  rcases Finset.mem_insert.mp h2 with h3 | h3
  · rw [h3]; omega
  · rw [Finset.mem_singleton.mp h3]; omega

/-- **The J-9 A handle compute RAP** (`wRAP = ![83, 54]`: round 0 = twin columns `0..68 ++ 123..136`,
round 1 = the coin block `69..122`). -/
def vclRAPHX9 [FiniteDimensional F K] {h : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![round0WX9, 54]
    w := widthHX9
    w_eq := by simp [Fin.sum_univ_two, round0WX9, widthHX9]
    h := h
    d := 4
    s := (gatesHX9P b δ).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((gatesHX9P b δ).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (gatesHX9P_degree b δ _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := Ibound9 widthHX9 h orbit.h_pos }

/-- **`computeChipVCLHX9`**: the J-9 A compute chip (preprocessing `isFirst` / `isLast` at `17` / `18`,
fixed by `permX9`). -/
def computeChipVCLHX9 [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPHX9 b δ chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := Nat.two_pos
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨17 + (j : ℕ), by
          have := j.isLt
          change 17 + (j : ℕ) < round0WX9
          simp only [round0WX9]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem computeChipVCLHX9_width [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w = 137 := rfl

theorem computeChipVCLHX9_wRAP [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.wRAP = ![83, 54] := rfl

/-- The chip's constraints are the reified permuted twin gates (`gatesHX9P`, definitionally). -/
theorem computeChipVCLHX9_C [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (i : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.s) :
    (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.C i =
      coeffToMv chalV pubVal ((gatesHX9P b δ).get i) := rfl


/-- **The transport lemma.**  A trace satisfying the permuted chip's RAP satisfies EVERY
compiled twin gate (base gates, the `𝕂′` slot pairs' coordinate gates, the walk gates, the accumulator and public
column references: all are entries of `gatesHX9`) at the row environment read through the permutation.  Row lemmas
stated at the unpermuted twin layout (an `Env` whose `trace`/`traceNext` are twin columns) apply to
`Env.viaPerm permX9 (envOfTrace P ω x chalV pubVal)`; the round split is `permX9_round0_iff`. -/
theorem computeChipVCLHX9_sat_twin [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hsat : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.Satisfies P)
    (x : F) (hx : x ∈ rowNodeSet nodes) :
    ∀ g ∈ gatesHX9 b δ,
      g.eval (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) = 0 := by
  intro g hg
  have hmem : renC permX9 g ∈ gatesHX9P b δ := List.mem_map.mpr ⟨g, hg, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  have h1 := (Nock.Framework.Reify.compose_eval
    (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap P i x).symm.trans (hsat i x hx)
  have h2 : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.C i =
      coeffToMv chalV pubVal ((gatesHX9P b δ).get i) := rfl
  rw [h2, eval_coeffToMv, hi, eval_renC] at h1
  exact h1

/-- Every slot-pair coordinate gate of the twin is among the RAP's gates, at permuted columns. -/
theorem slotGates_mem_gatesHX9P (b : Basis (Fin 3) F K) (δ : F) :
    ∀ q ∈ slotPairsX9 F δ, ∀ g ∈ qGates b q, renC permX9 g ∈ gatesHX9P b δ := by
  intro q hq g hg
  refine List.mem_map.mpr ⟨g, ?_, rfl⟩
  simp only [gatesHX9, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨q, hq, hg⟩)

end Chip

end

end ChipHX9
end VclL.Handle
end Nock.NockVMROM.Thm54

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
#print axioms permX9_lt
#print axioms permX9_inj
#print axioms permX9_surj
#print axioms permX9_round0_iff
#print axioms eval_renC
#print axioms degree_renC
#print axioms walkTemplateX9_degree
#print axioms gatesHX9_degree
#print axioms gatesHX9P_degree
#print axioms gatesHX9P_eval
#print axioms computeChipVCLHX9_width
#print axioms computeChipVCLHX9_wRAP
#print axioms computeChipVCLHX9_C
#print axioms computeChipVCLHX9_sat_twin
#print axioms slotGates_mem_gatesHX9P
end Axioms
