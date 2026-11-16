/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/RapWalkX9.lean

Row environments are read through the permutation: `EN9 r = CompReqsX9.envsN9 .. r =
  Env.viaPerm permX9 (TeleC.envsN .. r)`.  The one-hot bound used is `20 < p` (20 states).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.CompReqsX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RowSemSatX9
import Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9

open Nock Nock.Reified Nock.Framework Nock.Edit
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd chalAlphaW chalGammaW pubIC pubSeed pubOut cc selS mapC mapM)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (CSt)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (csIdx)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Row facts -/

section Sat
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (b : Basis (Fin 3) (ZMod p) K) (δ : ZMod p)
  (chalV pubVal : ℕ → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
  (P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X])

/-- **Walk row facts**: every `walkGatesX9` gate vanishes (as `evalMQ`) at the gathered environment of the
permuted row environment. -/
theorem walkX9_of_sat (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit) P)
    (x : ZMod p) (hx : x ∈ rowNodeSet nodes) (t : MixedExpr ℚ) (ht : t ∈ (walkGatesX9 : List (MixedExpr ℚ))) :
    evalMQ t (Compute.TowerD.gatherEnv b (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)))
      (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) = 0 := by
  have hall := computeChipVCLHX9_sat_twin hn nodes b δ chalV pubVal orbit P hsat.1 x hx
  have hm : mapM (fun q : ℚ => (q : ZMod p)) t ∈ (walkGatesFX9 : List (MixedExpr (ZMod p))) :=
    List.mem_map_of_mem ht
  have h0 : ∀ k, (mixedCompile b Compute.TowerD.col0Id (mapM (fun q : ℚ => (q : ZMod p)) t) k).eval
      (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) = 0 := fun k =>
    hall _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hm, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
  have h1 := (mixedCompile_zero_iff b Compute.TowerD.col0Id
    (Compute.TowerD.isCoordEnv_gather b (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal))) _).mpr h0
  rwa [eval_mapM_cast] at h1

/-- The endpoint masks of the twin compute chip, at the permuted row environment (`firstX = 17`, `lastX = 18`
are fixed by `permX9`). -/
theorem masksCX9 (hbind : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (Env.viaPerm permX9 (rEF nodes chalV pubVal orbit P i)).trace firstX = (if (i : ℕ) = 0 then 1 else 0) ∧
      (Env.viaPerm permX9 (rEF nodes chalV pubVal orbit P i)).trace lastX =
        (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w = 137 := rfl
  have h0 : P ⟨17, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : P ⟨18, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  have e1 : permX9 firstX = 17 := permX9_fixes_pre 17 (by norm_num)
  have e2 : permX9 lastX = 18 := permX9_fixes_pre 18 (by norm_num)
  show (rEF nodes chalV pubVal orbit P i).trace (permX9 firstX) = _ ∧
    (rEF nodes chalV pubVal orbit P i).trace (permX9 lastX) = _
  rw [e1, e2]
  have e3 : (rEF nodes chalV pubVal orbit P i).trace 17 =
      (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).trace 17 := rfl
  have e4 : (rEF nodes chalV pubVal orbit P i).trace 18 =
      (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).trace 18 := rfl
  rw [e3, e4, envOfTrace_trace P _ _ _ _ (show 17 < _ by rw [hw]; omega),
    envOfTrace_trace P _ _ _ _ (show 18 < _ by rw [hw]; omega), h0, h1,
    firstRowMask_eval nodes hinj i, lastRowMask_eval hn nodes hinj i]
  refine ⟨rfl, ?_⟩
  by_cases hi : (i : ℕ) = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

end Sat

/-! ## 2. The one-hot state over the 20 twin states -/

section OneHot
variable {F : Type} [Field F]

/-- The `j`-th of the twenty one-hot columns (`0..16`, then `123, 124, 125`). -/
def idx20 (j : ℕ) : ℕ := if j < 17 then j else j + 106

theorem idx20_mem {j : ℕ} (hj : j < 20) : idx20 j ∈ statesX9 := by
  simp only [idx20, statesX9, newStates, sS0B, sS10B, sS10S, nStates, List.mem_append, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false]
  split_ifs <;> omega

theorem idx20_inj {i j : ℕ} (hi : i < 20) (hj : j < 20) (h : idx20 i = idx20 j) : i = j := by
  simp only [idx20] at h; split_ifs at h <;> omega

theorem mem_idx20 {i : ℕ} (hi : i ∈ statesX9) : ∃ j < 20, idx20 j = i := by
  simp only [statesX9, newStates, sS0B, sS10B, sS10S, nStates, List.mem_append, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi
  · exact ⟨i, by omega, by simp [idx20, show i < 17 by omega]⟩
  · exact ⟨17, by omega, by simp [idx20]; omega⟩
  · exact ⟨18, by omega, by simp [idx20]; omega⟩
  · exact ⟨19, by omega, by simp [idx20]; omega⟩

theorem csIdx_surj : ∀ j < 20, ∃ cs : CSt, csIdx cs = idx20 j := by
  intro j hj
  by_cases h17 : j < 17
  · obtain ⟨st, hst⟩ := RapWalkJ8.stIdx_surj j (by simpa [nStates] using h17)
    exact ⟨.old st, by simp [csIdx, hst, idx20, h17]⟩
  · have : j = 17 ∨ j = 18 ∨ j = 19 := by omega
    rcases this with rfl | rfl | rfl
    · exact ⟨.s0B, by simp [csIdx, idx20, sS0B]⟩
    · exact ⟨.s10B, by simp [csIdx, idx20, sS10B]⟩
    · exact ⟨.s10S, by simp [csIdx, idx20, sS10S]⟩

/-- **One-hot over the 20 twin states** from the twin base gates, `20 < char`. -/
theorem oneHotX9_of_base {env : Env F} (hB : BaseHoldsX9 env) (hc : 20 < ringChar F) :
    ∃ cs : CSt, OneHotAt9 env (csIdx cs) := by
  have hb : ∀ j < 20, env.trace (idx20 j) * (env.trace (idx20 j) - 1) = 0 := fun j hj => by
    by_cases h17 : j < 17
    · have hm : boolG (cc j) ∈ (arithKeptX9 : List (CoeffExpr ℚ)) := by
        have key : ∀ j ∈ List.range nStates, boolG (cc j) ∈ (arithKeptX9 : List (CoeffExpr ℚ)) := by
          decide +kernel
        exact key j (List.mem_range.mpr h17)
      have hm2 : boolG (cc j) ∈ (arithGatesX9 : List (CoeffExpr ℚ)) := by
        simp only [arithGatesX9, arithSF9, List.mem_append]
        tauto
      have := arith_of_base9 hB hm2
      simpa [idx20, h17, boolG, evalQX, cc] using this
    · have hmem : boolG (cc (idx20 j)) ∈ (arithGatesX9 : List (CoeffExpr ℚ)) := by
        have hj' : idx20 j ∈ newStates := by
          simp only [idx20, newStates, sS0B, sS10B, sS10S, List.mem_cons, List.not_mem_nil, or_false]
          split_ifs <;> omega
        have hn' : boolG (cc (idx20 j)) ∈ (newBoolG9 : List (CoeffExpr ℚ)) :=
          List.mem_append_left _ (List.mem_map.mpr ⟨_, hj', rfl⟩)
        simp only [arithGatesX9, arithSF9, List.mem_append]
        tauto
      have := arith_of_base9 hB hmem
      simpa [boolG, evalQX, cc] using this
  have hsum : ((List.range 20).map fun j => env.trace (idx20 j)).sum = 1 := by
    have h0 := arith_of_base9 hB (g := oneHotSumX9) (by decide +kernel)
    simp only [oneHotSumX9, evalQX, RapWalkJ8.evalQX_selS] at h0
    have e : (List.range 20).map (fun j => env.trace (idx20 j)) =
        (List.range nStates).map env.trace ++ newStates.map env.trace := by
      simp [List.range_succ, idx20, newStates, sS0B, sS10B, sS10S, nStates]
    rw [e, List.sum_append]
    simpa [sub_eq_zero] using h0
  obtain ⟨j0, hj0, hsel⟩ := RapWalkJ8.onehotN 20 (fun j => env.trace (idx20 j)) hb hsum hc
  obtain ⟨cs, hcs⟩ := csIdx_surj j0 hj0
  refine ⟨cs, fun i hi => ?_⟩
  obtain ⟨j, hj, rfl⟩ := mem_idx20 hi
  rw [hcs, hsel j hj]
  by_cases hjj : j = j0
  · subst hjj; simp
  · rw [if_neg hjj, if_neg]
    intro he; exact hjj (idx20_inj hj hj0 he)

open Classical in
/-- The decoded twin chip state of a row (`old s0` if there is none). -/
def stX9 (env : Env F) : CSt :=
  if h : ∃ cs : CSt, OneHotAt9 env (csIdx cs) then Classical.choose h else .old .s0

theorem stX9_spec {env : Env F} (hB : BaseHoldsX9 env) (hc : 20 < ringChar F) :
    OneHotAt9 env (csIdx (stX9 env)) := by
  have h := oneHotX9_of_base hB hc
  simp only [stX9, dif_pos h]
  exact Classical.choose_spec h

end OneHot

/-! ## 3. The extraction context -/

section Chip
variable {p : ℕ} [Fact p.Prime] [DecidableEq (ZMod p)] {K : Type} [Field K] [Algebra (ZMod p) K]
  [FiniteDimensional (ZMod p) K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (b : Basis (Fin 3) (ZMod p) K) (δ : ZMod p)
  (chalV pubVal : ℕ → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
  (P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X])

/-- **The extraction context** of the twin compute walk: an accepted trace on an injective `ω`-adjacent node set,
`20 < p`, and the walk coins / publics (limb values). -/
structure XCtx (α γ seed : K) : Prop where
  hp : 20 < p
  hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit) P
  hinj : Function.Injective nodes
  hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω
  hα : Compute.LogUp.limbVal b chalV chalAlphaW = α
  hγ : Compute.LogUp.limbVal b chalV chalGammaW = γ
  hIC : Compute.LogUp.limbVal b pubVal pubIC = α
  hSeed : Compute.LogUp.limbVal b pubVal pubSeed = seed
  hOut : Compute.LogUp.limbVal b pubVal pubOut = 0

local notation "EN9" => CompReqsX9.envsN9 hn nodes orbit chalV pubVal P

variable {hn nodes b δ chalV pubVal orbit P} {α γ seed : K}
  (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed)
include C

theorem envsN9_lt (k : ℕ) (hk : k < n) :
    CompReqsX9.envsN9 hn nodes orbit chalV pubVal P k =
      Env.viaPerm permX9 (rEF nodes chalV pubVal orbit P ⟨k, hk⟩) := by
  simp [CompReqsX9.envsN9, TeleC.envsN, hk]

theorem charX9 : 20 < ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n]; exact C.hp

theorem baseE9 {r : ℕ} (hr : r < n) : BaseHoldsX9 (EN9 r) := by
  rw [envsN9_lt C r hr]
  exact RowSemSatX9.baseX9_of_sat hn nodes b δ chalV pubVal orbit P C.hsat.1 _ (mem_rowNodeSet nodes _)

theorem ohE9 {r : ℕ} (hr : r < n) : OneHotAt9 (EN9 r) (csIdx (stX9 (EN9 r))) :=
  stX9_spec (baseE9 C hr) (charX9 C)

theorem tnE9 {r : ℕ} (hr : r + 1 < n) : (EN9 r).traceNext = (EN9 (r + 1)).trace := by
  funext j
  rw [envsN9_lt C r (by omega), envsN9_lt C (r + 1) hr]
  exact traceNext_eq nodes orbit P chalV pubVal C.hadj ⟨r, by omega⟩ hr (permX9 j)

theorem chalE9 (r : ℕ) : (EN9 r).chal = chalV := by
  unfold CompReqsX9.envsN9 TeleC.envsN; split_ifs <;> rfl

theorem pubE9 (r : ℕ) : (EN9 r).pub = pubVal := by
  unfold CompReqsX9.envsN9 TeleC.envsN; split_ifs <;> rfl

theorem firstE9 {r : ℕ} (hr : r < n) : (EN9 r).trace firstX = (if r = 0 then 1 else 0) := by
  rw [envsN9_lt C r hr]
  exact (masksCX9 hn nodes b δ chalV pubVal orbit P C.hsat.2 C.hinj ⟨r, hr⟩).1

theorem lastE9 {r : ℕ} (hr : r < n) : (EN9 r).trace lastX = (if r = n - 1 then 1 else 0) := by
  rw [envsN9_lt C r hr]
  exact (masksCX9 hn nodes b δ chalV pubVal orbit P C.hsat.2 C.hinj ⟨r, hr⟩).2

/-- Every `walkGatesX9` gate vanishes at the gathered environment of every row `r < n`. -/
theorem walkE9 {r : ℕ} (hr : r < n) (g : MixedExpr ℚ) (hg : g ∈ (walkGatesX9 : List (MixedExpr ℚ))) :
    evalMQ g (Compute.TowerD.gatherEnv b (EN9 r)) (EN9 r) = 0 := by
  rw [envsN9_lt C r hr]
  exact walkX9_of_sat hn nodes b δ chalV pubVal orbit P C.hsat _ (mem_rowNodeSet nodes _) g hg

/-- The `base` and `oh` facts at an accepted trace. -/
theorem base_oh_of_sat9 :
    (∀ r < n, BaseHoldsX9 (EN9 r)) ∧
      (∀ r < n, OneHotAt9 (EN9 r) (csIdx (stX9 (EN9 r)))) :=
  ⟨fun _ hr => baseE9 C hr, fun _ hr => ohE9 C hr⟩

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9

open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms walkX9_of_sat
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms masksCX9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms oneHotX9_of_base
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms stX9_spec
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms envsN9_lt
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms baseE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms ohE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms tnE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms chalE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms pubE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms firstE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms lastE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms walkE9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 in
#print axioms base_oh_of_sat9
