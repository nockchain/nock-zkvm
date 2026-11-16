/-
  Nock/NockVMROM/Thm54/VclL/Handle/RapWalkJ8.lean

  **The RAP → `WalkRowsX` layer of the J-8
  compute chip `computeChipVCLHX`** (the `TeleC` / `CWalkChipVS` pattern at the X chip).  New
  module, additive.

  * `computeChipVCLHX_sat_iff`, `baseX_of_sat` (`BaseHoldsX` at every row), `walkX_of_sat` (the nine
    `walkGatesX` at the gathered `𝕂` environment of every row), `masksCX` (preprocessing `17 / 18`).
  * `onehotN` / **`oneHotX_of_base`** — the `oneHotG` gates (booleanity of `0..16` and their sum `= 1`)
    under `17 < p` give a `StateX` `st` with `OneHotAt env (stIdx st)`; `stX env` is that state.
  * **`walkRowsX_of_sat`** — at an accepted `computeChipVCLHX` trace whose walk coins / publics read
    `α`, `γ`, `seed`, `0` (limb values), the row environments `envsN` / `gatherEnv b ∘ envsN` / `stX ∘ envsN`
    form a `WalkBridgeJ8.WalkRowsX` (so `cwalkX_sat` applies), and `base` / `oh` of `RowsAccX` hold.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TeleC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8

open Nock Nock.Reified Nock.Framework Nock.Edit
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd chalAlphaW chalGammaW pubIC pubSeed pubOut cc selS mapC mapM)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.Edit
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. `sat_iff` and the row facts -/

section Sat
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

set_option maxHeartbeats 4000000 in
/-- **`sat_iff` for the J-8 compute chip** (copy of `TeleC.computeChipVCLH_sat_iff`). -/
theorem computeChipVCLHX_sat_iff {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P ↔
      (computeChipVCLHX hn nodes b δ chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ gatesHX b δ,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.compose P i).eval x =
        ((gatesHX b δ).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
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

theorem evalQX_eq (g : CoeffExpr ℚ) (env : Env F) : evalQX g env = evalQ g env := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b iha ihb => simp only [evalQX, evalQ, iha, ihb]
  | sub a b iha ihb => simp only [evalQX, evalQ, iha, ihb]
  | mul a b iha ihb => simp only [evalQX, evalQ, iha, ihb]
  | neg a iha => simp only [evalQX, evalQ, iha]
  | pow a n iha => simp only [evalQX, evalQ, iha]

variable {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])

/-- **Base row facts**: `BaseHoldsX` at every row. -/
theorem baseX_of_sat (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes) : BaseHoldsX (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
  intro t ht
  have h0 := ((computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mp hsat).2 x hx
    (mapC (fun q : ℚ => (q : F)) t)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ht)))
  rwa [eval_mapC_cast, ← evalQX_eq] at h0

/-- **Walk row facts**: every `walkGatesX` gate vanishes (as `evalMQ`) at the gathered environment. -/
theorem walkX_of_sat (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes) (t : MixedExpr ℚ) (ht : t ∈ (walkGatesX : List (MixedExpr ℚ))) :
    evalMQ t (Compute.TowerD.gatherEnv b (Reify.envOfTrace P orbit.ω x chalV pubVal))
      (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have hall := ((computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mp hsat).2 x hx
  have hm : mapM (fun q : ℚ => (q : F)) t ∈ (walkGatesFX : List (MixedExpr F)) := List.mem_map_of_mem ht
  have h0 : ∀ k, (mixedCompile b Compute.TowerD.col0Id (mapM (fun q : ℚ => (q : F)) t) k).eval
      (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := fun k =>
    hall _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hm, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
  have h1 := (mixedCompile_zero_iff b Compute.TowerD.col0Id
    (Compute.TowerD.isCoordEnv_gather b (Reify.envOfTrace P orbit.ω x chalV pubVal)) _).mpr h0
  rwa [eval_mapM_cast] at h1

/-- The endpoint masks of the J-8 compute chip (preprocessing columns `17 / 18`). -/
theorem masksCX (hbind : (computeChipVCLHX hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (rEF nodes chalV pubVal orbit P i).trace firstX = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rEF nodes chalV pubVal orbit P i).trace lastX = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w = 123 := rfl
  have h0 : P ⟨17, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : P ⟨18, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  rw [show firstX = 17 from rfl, show lastX = 18 from rfl,
    envOfTrace_trace P _ _ _ _ (show 17 < _ by rw [hw]; omega),
    envOfTrace_trace P _ _ _ _ (show 18 < _ by rw [hw]; omega), h0, h1,
    firstRowMask_eval nodes hinj i, lastRowMask_eval hn nodes hinj i]
  refine ⟨rfl, ?_⟩
  by_cases hi : (i : ℕ) = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

end Sat

/-! ## 2. The one-hot state from `oneHotG` -/

section OneHot
variable {F : Type} [Field F]

/-- **One-hot over `m` columns**: booleans summing to `1`, `m < char`, exactly one is on. -/
theorem onehotN (m : ℕ) (s : ℕ → F) (hb : ∀ j < m, s j * (s j - 1) = 0)
    (hsum : ((List.range m).map s).sum = 1) (hc : m < ringChar F) :
    ∃ j0 < m, ∀ j < m, s j = if j = j0 then 1 else 0 := by
  classical
  have hb' : ∀ j < m, s j = 0 ∨ s j = 1 := fun j hj => by
    rcases mul_eq_zero.mp (hb j hj) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hcount : ∀ l : List ℕ, (∀ j ∈ l, s j = 0 ∨ s j = 1) →
      (l.map s).sum = ((l.filter fun j => s j = 1).length : F) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih fun j hj => hl j (List.mem_cons_of_mem _ hj),
        List.filter_cons]
      rcases hl a List.mem_cons_self with h | h
      · simp [h]
      · simp [h]; ring
  set L := (List.range m).filter fun j => s j = 1 with hL
  have hlen : (L.length : F) = 1 := by
    rw [← hcount _ (fun j hj => hb' j (List.mem_range.mp hj)), hsum]
  have hle : L.length ≤ m := (List.length_filter_le _ _).trans (by simp)
  have hpos : 1 ≤ L.length := by
    by_contra hc0
    have : L.length = 0 := by omega
    rw [this, Nat.cast_zero] at hlen; exact zero_ne_one hlen
  have h1 : L.length = 1 := by
    have hz : ((L.length - 1 : ℕ) : F) = 0 := by
      rw [Nat.cast_sub hpos, hlen, Nat.cast_one, sub_self]
    have hdvd := (ringChar.spec F _).mp hz
    have : L.length - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  obtain ⟨j0, hj0⟩ := List.length_eq_one_iff.mp h1
  have hmem : j0 ∈ L := by rw [hj0]; exact List.mem_singleton_self _
  rw [hL, List.mem_filter, List.mem_range] at hmem
  refine ⟨j0, hmem.1, fun j hj => ?_⟩
  by_cases hjj : j = j0
  · subst hjj; simpa using hmem.2
  · rw [if_neg hjj]
    rcases hb' j hj with h | h
    · exact h
    · exfalso
      have : j ∈ L := by rw [hL, List.mem_filter, List.mem_range]; exact ⟨hj, by simpa using h⟩
      rw [hj0, List.mem_singleton] at this
      exact hjj this

theorem stIdx_surj : ∀ j < nStates, ∃ st : StateX, stIdx st = j := by
  intro j hj
  simp only [nStates] at hj
  interval_cases j
  exacts [⟨.s0, rfl⟩, ⟨.s1, rfl⟩, ⟨.s2, rfl⟩, ⟨.s3, rfl⟩, ⟨.s4, rfl⟩, ⟨.s5, rfl⟩, ⟨.s6, rfl⟩,
    ⟨.s7, rfl⟩, ⟨.s8, rfl⟩, ⟨.s9, rfl⟩, ⟨.cons, rfl⟩, ⟨.s10, rfl⟩, ⟨.s10L, rfl⟩, ⟨.s10T, rfl⟩,
    ⟨.s11s, rfl⟩, ⟨.s11d, rfl⟩, ⟨.s11j, rfl⟩]

theorem evalQX_selS (l : List ℕ) (env : Env F) :
    evalQX (selS (F := ℚ) l) env = (l.map env.trace).sum := by
  induction l with
  | nil => simp [selS, CoeffExpr.sumList, evalQX]
  | cons a l ih =>
    have : evalQX (selS (F := ℚ) (a :: l)) env = env.trace a + evalQX (selS (F := ℚ) l) env := by
      simp [selS, CoeffExpr.sumList, evalQX, cc]
    rw [this, ih]; simp

/-- **`oh` from `oneHotG`**: a row whose base gates hold, over a field of characteristic `> 17`, has a
one-hot `StateX`. -/
theorem oneHotX_of_base {env : Env F} (hB : BaseHoldsX env) (hc : nStates < ringChar F) :
    ∃ st : StateX, OneHotAt env (stIdx st) := by
  have hb : ∀ j < nStates, env.trace j * (env.trace j - 1) = 0 := fun j hj => by
    have := arith_of_base hB (RowSemChipX.oneHotG_sub _
      (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    simpa [boolG, evalQX, cc] using this
  have hsum : ((List.range nStates).map env.trace).sum = 1 := by
    have := arith_of_base hB (RowSemChipX.oneHotG_sub _
      (by simp [oneHotG] : (.sub (selS (List.range nStates)) (.const 1) : CoeffExpr ℚ) ∈ oneHotG))
    rw [evalQX, evalQX_selS] at this
    simpa [evalQX, sub_eq_zero] using this
  obtain ⟨j0, hj0, hsel⟩ := onehotN nStates env.trace hb hsum hc
  obtain ⟨st, rfl⟩ := stIdx_surj j0 hj0
  exact ⟨st, hsel⟩

open Classical in
/-- The decoded state of a row (the one-hot `StateX`, `s0` if there is none). -/
def stX (env : Env F) : StateX :=
  if h : ∃ st : StateX, OneHotAt env (stIdx st) then Classical.choose h else .s0

theorem stX_spec {env : Env F} (hB : BaseHoldsX env) (hc : nStates < ringChar F) :
    OneHotAt env (stIdx (stX env)) := by
  have h := oneHotX_of_base hB hc
  simp only [stX, dif_pos h]
  exact Classical.choose_spec h

end OneHot

/-! ## 3. The accepted chip as a `WalkRowsX` -/

section Chip
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (b : Basis (Fin 3) (ZMod p) K) (δ : ZMod p)
  (chalV pubVal : ℕ → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
  (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X])

/-- **The extraction context** of the J-8 compute walk: an accepted trace on an injective
`ω`-adjacent node set, `17 < p`, and the walk coins / publics (limb values). -/
structure XCtx (α γ seed : K) : Prop where
  hp : 17 < p
  hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P
  hinj : Function.Injective nodes
  hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω
  hα : Compute.LogUp.limbVal b chalV chalAlphaW = α
  hγ : Compute.LogUp.limbVal b chalV chalGammaW = γ
  hIC : Compute.LogUp.limbVal b pubVal pubIC = α
  hSeed : Compute.LogUp.limbVal b pubVal pubSeed = seed
  hOut : Compute.LogUp.limbVal b pubVal pubOut = 0

local notation "EN" => envsN hn nodes chalV pubVal orbit P

variable {hn nodes b δ chalV pubVal orbit P} {α γ seed : K}
  (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed)
include C

theorem envsN_ltX (k : ℕ) (hk : k < n) :
    envsN hn nodes chalV pubVal orbit P k = rEF nodes chalV pubVal orbit P ⟨k, hk⟩ := by
  simp [envsN, hk]

theorem charX : nStates < ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n]; exact C.hp

theorem baseE {r : ℕ} (hr : r < n) : BaseHoldsX (EN r) := by
  rw [envsN_ltX C r hr]
  exact baseX_of_sat hn nodes b δ chalV pubVal orbit P C.hsat _ (mem_rowNodeSet nodes _)

theorem ohE {r : ℕ} (hr : r < n) : OneHotAt (EN r) (stIdx (stX (EN r))) :=
  stX_spec (baseE C hr) (charX C)

theorem tnE {r : ℕ} (hr : r + 1 < n) : (EN r).traceNext = (EN (r + 1)).trace := by
  funext j
  rw [envsN_ltX C r (by omega),
    envsN_ltX C (r + 1) hr]
  exact traceNext_eq nodes orbit P _ _ C.hadj ⟨r, by omega⟩ hr j

theorem chalE (r : ℕ) : (EN r).chal = chalV := by
  unfold envsN; split_ifs <;> rfl

theorem pubE (r : ℕ) : (EN r).pub = pubVal := by
  unfold envsN; split_ifs <;> rfl

/-- **An accepted `computeChipVCLHX` trace is a `WalkRowsX`** (so
`WalkBridgeJ8.cwalkX_sat` gives `Walk.WalkSat` over `rowsWX`). -/
theorem walkRowsX_of_sat :
    WalkRowsX n (fun r => EN r) (fun r => Compute.TowerD.gatherEnv b (EN r))
      (fun r => stX (EN r)) α γ seed where
  hn := hn
  oh := fun r hr => ohE C hr
  gate := fun r hr g hg => by
    show evalMQ g (Compute.TowerD.gatherEnv b (EN r)) (EN r) = 0
    rw [envsN_ltX C r hr]
    exact walkX_of_sat hn nodes b δ chalV pubVal orbit P C.hsat _ (mem_rowNodeSet nodes _) g hg
  next := fun r hr => tnE C hr
  nextK := fun r hr => by
    show Compute.LogUp.limbVal b (EN r).traceNext = Compute.LogUp.limbVal b (EN (r + 1)).trace
    rw [tnE C hr]
  first := fun r hr => by
    have hb := ((computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mp C.hsat).1
    rw [envsN_ltX C r hr]
    exact (masksCX hn nodes b δ chalV pubVal orbit P hb C.hinj ⟨r, hr⟩).1
  last := fun r hr => by
    have hb := ((computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mp C.hsat).1
    rw [envsN_ltX C r hr]
    exact (masksCX hn nodes b δ chalV pubVal orbit P hb C.hinj ⟨r, hr⟩).2
  chA := fun r => by
    show Compute.LogUp.limbVal b (EN r).chal chalAlphaW = α
    rw [chalE C r, C.hα]
  chG := fun r => by
    show Compute.LogUp.limbVal b (EN r).chal chalGammaW = γ
    rw [chalE C r, C.hγ]
  pIC := fun r => by
    show Compute.LogUp.limbVal b (EN r).pub pubIC = α
    rw [pubE C r, C.hIC]
  pSeed := fun r => by
    show Compute.LogUp.limbVal b (EN r).pub pubSeed = seed
    rw [pubE C r, C.hSeed]
  pOut := fun r => by
    show Compute.LogUp.limbVal b (EN r).pub pubOut = 0
    rw [pubE C r, C.hOut]

/-- The compute walk of an accepted J-8 trace (`cwalkX_sat` at `walkRowsX_of_sat`). -/
theorem cwalkX_of_sat
    (hseed : seed = Walk.rlc γ (encT (K := K)
      (rowW (EN 0) (stX (EN 0))).trip) * α) :
    ∃ ln cnt acc : ℕ → K,
      Walk.WalkSat (fun i => Walk.rlc γ (WalkLblVSX.enc (lblOf (rowsWX (fun r => EN r)
          (fun r => stX (EN r))) i)))
        (fun i l => Walk.rlc γ (WalkLblVSX.enc (clabOf (rowsWX (fun r => EN r)
          (fun r => stX (EN r))) i l)))
        (foOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) ln cnt acc α
        (∑ i ∈ Finset.Icc 1 1, Walk.rlc γ (WalkLblVSX.enc (lblOf (rowsWX (fun r => EN r)
          (fun r => stX (EN r))) i)) * α ^ i)
        (α ^ 1) n ∧
      acc n = 0 ∧ (∀ i, 1 ≤ i → i < n → cnt i ≠ ln i) ∧ cnt n = ln n :=
  cwalkX_sat (walkRowsX_of_sat C) hseed

/-- The `base` and `oh` fields of `RowsAccX` hold at an accepted trace. -/
theorem base_oh_of_sat :
    (∀ r < n, BaseHoldsX (EN r)) ∧
      (∀ r < n, OneHotAt (EN r) (stIdx (stX (EN r)))) :=
  ⟨fun _ hr => baseE C hr, fun _ hr => ohE C hr⟩

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
