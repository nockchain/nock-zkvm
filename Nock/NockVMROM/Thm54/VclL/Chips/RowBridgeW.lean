/-
  Nock/NockVMROM/Thm54/VclL/Chips/RowBridgeW.lean

  No coin event: the queue validity and the tiling come from the base-field counter `q`
  (`q₁ = kroots + fo₁ − 1`, `q′ = q + fo′ − 1`, `q · qinv = 1` off the last row, `q = 0` on it).
  Queue validity REUSES trunk's `Batch478.bfsValidF_of_ratio_gate` (the BFS combinatorics: the
  first underflow passes through `0`), instantiated at `α = 2 ∈ ℚ`, where `2^{k + Sf i} ≠ 2^i` is
  exactly `k + Sf i ≠ i`; the tiling is the last-row `q = 0` with `3n < p` (no wrap).
  The depth guard (`len.val < 62`) is the certificate `len + Σ 2^i bᵢ = 61` with the exclusion
  `b₁ b₂ b₃ b₄ b₅ = 0` (`certNat_le_61`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.WalkChip
import Nock.NockVMROM.Thm54.VclL.Chips.PathModel
import Nock.NockVMROM.Thm54.VclL.Chips.RowModel
import Nock.NockVMROM.Thm54.VclL.Walk.WalkEvent
import Nock.RedTeam.Batch478Thm54QueueGateRatioForm

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Row-local gates, masks, gathered coins -/

section Local
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **Walk chip, row-local** (`pathChip_rowLocal` twin). -/
theorem walkChip_rowLocal (Q : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (∀ g ∈ WChip.baseGates (F := F) kroots,
        g.eval (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 21 chals) (slotVal b 21 pubs)) = 0) ∧
      (∀ g ∈ WChip.mixedGates δF kroots,
        g.eval (gatherEnv b ((walkTemplate δF kroots).col0 3)
            (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 21 chals) (slotVal b 21 pubs)))
          (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 21 chals) (slotVal b 21 pubs)) = 0) := by
  have hl := (expandChip_satisfies_iff_language (walkTemplate δF kroots) b (slotVal b 21 chals)
    (slotVal b 21 pubs) orbit (rowNodeSet nodes) Q).mp hsat (nodes i) (mem_rowNodeSet nodes i)
  exact ⟨hl.1, hl.2.2.2⟩

/-- **Walk chip masks** (`pathChip_masks` twin, plus `rootMask`). -/
theorem walkChip_masks (Q : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (Q ⟨0, by rw [(walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1]; omega⟩).eval
        (nodes i) = (if (i : ℕ) = 0 then 1 else 0) ∧
      (Q ⟨1, by rw [(walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1]; omega⟩).eval
        (nodes i) = (if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0) ∧
      (Q ⟨2, by rw [(walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1]; omega⟩).eval
        (nodes i) = (if (i : ℕ) < kroots then 1 else 0) := by
  have h0 := hbind ⟨0, by show 0 < 3; omega⟩
  have h1 := hbind ⟨1, by show 1 < 3; omega⟩
  have h2 := hbind ⟨2, by show 2 < 3; omega⟩
  refine ⟨?_, ?_, ?_⟩
  · have : Q ⟨0, _⟩ = firstRowMask nodes := h0
    rw [this, firstRowMask_eval nodes hinj i]
  · have : Q ⟨1, _⟩ = lastRowMask hn nodes := h1
    rw [this, lastRowMask_eval hn nodes hinj i]
  · have : Q ⟨2, _⟩ = rootRowMaskW nodes kroots := h2
    rw [this, rootRowMaskW_eval nodes kroots hinj i]

theorem gather_chal_walk (env : Env F) (henv : env.chal = slotVal b 21 chals) (idx : ℕ) :
    (gatherEnv b ((walkTemplate δF kroots).col0 3) env).chal idx = chals idx := by
  simp only [gatherEnv, ChipTemplate.col0, walkTemplate_baseCols, henv]
  exact sum_slotVal b 21 idx chals

theorem gather_pub_walk (env : Env F) (henv : env.pub = slotVal b 21 pubs) (idx : ℕ) :
    (gatherEnv b ((walkTemplate δF kroots).col0 3) env).pub idx = pubs idx := by
  simp only [gatherEnv, ChipTemplate.col0, walkTemplate_baseCols, henv]
  exact sum_slotVal b 21 idx pubs

end Local

/-! ## 2. Row environments -/

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- Row `i`'s base environment on the walk chip (rows past `n` read row `0`; never used). -/
def walkEnvF {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) : Env F :=
  Reify.envOfTrace Q orbit.ω (if hi : i < n then nodes ⟨i, hi⟩ else nodes ⟨0, hn⟩)
    (slotVal b 21 chals) (slotVal b 21 pubs)

/-- Row `i`'s gathered `𝕂` environment. -/
def walkEnvK {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) : Env K :=
  gatherEnv b ((walkTemplate δF kroots).col0 3) (walkEnvF b hn nodes orbit chals pubs Q i)

theorem walkEnvF_eq {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) (hi : i < n) :
    walkEnvF b hn nodes orbit chals pubs Q i =
      Reify.envOfTrace Q orbit.ω (nodes ⟨i, hi⟩) (slotVal b 21 chals) (slotVal b 21 pubs) := by
  simp [walkEnvF, hi]

variable (Q : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- Row `i`'s gates in the row environments: base, walk (`𝕂`), IO (`𝕂′`). -/
theorem walk_gates (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (i : ℕ) (hi : i < n) :
    (∀ g ∈ WChip.baseGates (F := F) kroots, g.eval (walkEnvF b hn nodes orbit chals pubs Q i) = 0) ∧
      (∀ g ∈ WChip.walkGates (F := F) kroots,
        g.eval (walkEnvK δF kroots b hn nodes orbit chals pubs Q i)
          (walkEnvF b hn nodes orbit chals pubs Q i) = 0) ∧
      (∀ e ∈ WChip.qEqs δF, e.ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q i)
        (walkEnvF b hn nodes orbit chals pubs Q i) = 0) := by
  have hl := walkChip_rowLocal δF kroots b hn nodes orbit chals pubs Q hsat ⟨i, hi⟩
  unfold walkEnvK
  rw [walkEnvF_eq b hn nodes orbit chals pubs Q i hi]
  refine ⟨hl.1, fun g hg => hl.2 g (List.mem_append_left _ hg), fun e he =>
    ev_eq_zero_of_gates δF _ _ e fun g hg => hl.2 g (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨e, he, hg⟩))⟩

variable (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
include hadj

theorem walk_traceNext (i : ℕ) (hi : i + 1 < n) (j : ℕ) :
    (walkEnvF b hn nodes orbit chals pubs Q i).traceNext j =
      (walkEnvF b hn nodes orbit chals pubs Q (i + 1)).trace j := by
  rw [walkEnvF_eq b hn nodes orbit chals pubs Q i (by omega),
    walkEnvF_eq b hn nodes orbit chals pubs Q (i + 1) hi]
  exact traceNext_eq nodes orbit Q _ _ hadj ⟨i, by omega⟩ hi j

theorem walkK_traceNext (i : ℕ) (hi : i + 1 < n) (r : ℕ) :
    (walkEnvK δF kroots b hn nodes orbit chals pubs Q i).traceNext r =
      (walkEnvK δF kroots b hn nodes orbit chals pubs Q (i + 1)).trace r := by
  simp only [walkEnvK, gatherEnv, ChipTemplate.col0,
    walk_traceNext δF kroots b hn nodes orbit chals pubs Q hadj i hi]

omit hadj in
/-- The three masks at row `i`. -/
theorem walk_masks (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : ℕ) (hi : i < n) :
    (walkEnvF b hn nodes orbit chals pubs Q i).trace WChip.isF = (if i = 0 then 1 else 0) ∧
      (walkEnvF b hn nodes orbit chals pubs Q i).trace WChip.isL = (if i + 1 = n then 1 else 0) ∧
      (walkEnvF b hn nodes orbit chals pubs Q i).trace WChip.rM = (if i < kroots then 1 else 0) := by
  have hw : (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = 132 :=
    (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1
  obtain ⟨m0, m1, m2⟩ := walkChip_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj ⟨i, hi⟩
  rw [walkEnvF_eq b hn nodes orbit chals pubs Q i hi]
  refine ⟨?_, ?_, ?_⟩
  · rw [show WChip.isF = 0 from rfl, envOfTrace_trace Q _ _ _ _ (show 0 < _ by rw [hw]; omega), m0]
  · rw [show WChip.isL = 1 from rfl, envOfTrace_trace Q _ _ _ _ (show 1 < _ by rw [hw]; omega), m1]
    by_cases hh : i + 1 = n
    · rw [if_pos (Fin.ext (by simp; omega)), if_pos hh]
    · rw [if_neg (fun e => hh (by have := congrArg Fin.val e; simp at this; omega)), if_neg hh]
  · rw [show WChip.rM = 2 from rfl, envOfTrace_trace Q _ _ _ _ (show 2 < _ by rw [hw]; omega), m2]

end Env

/-! ## 3. -/

section Model
variable {F : Type} [Field F] [DecidableEq F]

/-- A base-field value as an element of `ZMod p` (through `natOf`). -/
def zq (x : F) : ZMod (ringChar F) := (natOf x : ZMod (ringChar F))

def sideOf (s : WalkVCL.St) (l : ℕ) : Bool := if l = 1 then !s.1 else true

def childDT {q : ℕ} {Kfp : Type} (k : XKey Kfp) (b : Bool) (d : WalkVCL.DT q Kfp) :
    WalkVCL.DT q Kfp :=
  ⟨WalkVCL.tgt k b, 2 * d.pre + WalkVCL.bitZ b, d.root, d.ridx, d.len + 1⟩

/-- **`F` holds on a row whose children are the in-gate ones** (all but the depth guard is by
construction). -/
theorem F_of_parts {q : ℕ} {Kfp : Type} [Field Kfp] [DecidableEq Kfp] (X : List (XKey Kfp))
    (k : XKey Kfp) (hkX : k ∈ X) (s : WalkVCL.St) (d : WalkVCL.DT q Kfp) (hk1 : k.1 = d.node)
    (hlen : d.len.val < 62) :
    WalkVCL.F X 62 (s, d) (fun j : Fin 2 => if (j : ℕ) < WalkVCL.fanout s then
      some (((false, false), childDT k (sideOf s (j + 1)) d) : WalkVCL.LT q Kfp) else none) := by
  refine ⟨hlen, ?_, k, hkX, hk1, ?_, ?_⟩
  · intro j
    by_cases hj : (j : ℕ) < WalkVCL.fanout s <;> simp [hj]
  · intro h1
    have h0 : (0 : ℕ) < WalkVCL.fanout s := by
      rcases s with ⟨s1, s2⟩; simp only at h1; subst h1; cases s2 <;> simp [WalkVCL.fanout]
    refine ⟨_, by simp only [Fin.val_zero]; rw [if_pos h0], ?_⟩
    rcases s with ⟨s1, s2⟩; simp only at h1; subst h1
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro h2
    rcases s with ⟨s1, s2⟩; simp only at h2; subst h2
    cases s1
    · refine ⟨_, by simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_zero]; rw [if_pos (by simp [WalkVCL.fanout])], ?_⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨_, by simp only [↓reduceIte, Fin.val_one]; rw [if_pos (by simp [WalkVCL.fanout])], ?_⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

variable {K : Type} [Field K] [Algebra F K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

def lblRow (eK : Env K) (eF : Env F) : WalkVCL.LT (ringChar F) (Quad (algebraMap F K δF)) :=
  ((decide (eF.trace WChip.cL = 1), decide (eF.trace WChip.cR = 1)),
    ⟨(QFP.var WChip.pR).ev δF eK eF, zq (eF.trace WChip.pre), (QFP.var WChip.rootR).ev δF eK eF,
      zq (eF.trace WChip.ridx), zq (eF.trace WChip.len)⟩)

/-- **The export key a walk row consumes**: `(fp p, fp l, fp r, idx)` (side slot `0` is constant). -/
def keyRow (eK : Env K) (eF : Env F) : XKey (Quad (algebraMap F K δF)) :=
  ((QFP.var WChip.pR).ev δF eK eF, (QFP.var WChip.lR).ev δF eK eF, (QFP.var WChip.rR).ev δF eK eF,
    natOf (eF.trace WChip.idx))

end Model

/-- `Sf fo k ≤ 2k` (arity `≤ 2`). -/
theorem Sf_le_two (fo : ℕ → ℕ) (hfo : ∀ i, fo i ≤ 2) (k : ℕ) : Nock.Walk.Sf fo k ≤ 2 * k := by
  unfold Nock.Walk.Sf
  calc ∑ i ∈ Finset.Icc 1 k, fo i ≤ ∑ _i ∈ Finset.Icc 1 k, 2 := Finset.sum_le_sum fun i _ => hfo i
    _ = 2 * k := by simp [mul_comm]

/-! ## 4. The walk data of an accepted trace, `WalkHyps`, `RootGate` -/

section Hyps
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

def walkDataOf {w : ℕ} (Q : Fin w → F[X]) : WalkVCL.WalkData (ringChar F) (Quad (algebraMap F K δF)) where
  X := List.ofFn fun i : Fin n =>
    keyRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q i) (walkEnvF b hn nodes orbit chals pubs Q i)
  lbl i := lblRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q (i - 1))
    (walkEnvF b hn nodes orbit chals pubs Q (i - 1))
  clab i l := ((false, false), childDT
    (keyRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q (i - 1))
      (walkEnvF b hn nodes orbit chals pubs Q (i - 1)))
    (sideOf (lblRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q (i - 1))
      (walkEnvF b hn nodes orbit chals pubs Q (i - 1))).1 l)
    (lblRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q (i - 1))
      (walkEnvF b hn nodes orbit chals pubs Q (i - 1))).2)
  fo i := WalkVCL.fanout (lblRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q (i - 1))
    (walkEnvF b hn nodes orbit chals pubs Q (i - 1))).1
  kroots := kroots
  h := n

/-- A boolean field value's `decide (· = 1)` indicator cast back. -/
theorem bit_cast {x : F} (hx : x = 0 ∨ x = 1) : ((if decide (x = 1) then 1 else 0 : ℕ) : F) = x := by
  rcases hx with rfl | rfl <;> simp

/-- **The certificate**: six boolean bits, `b₁ b₂ b₃ b₄ b₅ = 0` and `len + Σ 2^i bᵢ = 61` give
`natOf len ≤ 61` (`61 < p`). -/
theorem certNat_le_61 (hF : GeneratedField.PrimeFieldElems F) (hp : 64 ≤ ringChar F)
    (bt : ℕ → F) (hb : ∀ i < 6, bt i * (bt i - 1) = 0)
    (hx : bt 1 * bt 2 * bt 3 * bt 4 * bt 5 = 0) (len : F)
    (hc : len + ∑ i ∈ Finset.range 6, (2 : F) ^ i * bt i - 61 = 0) : natOf len ≤ 61 := by
  have hbn : ∀ i < 6, ∃ β : ℕ, β ≤ 1 ∧ bt i = (β : F) := by
    intro i hi
    rcases CertBound.bool_cases (hb i hi) with h0 | h1
    · exact ⟨0, by omega, by simp [h0]⟩
    · exact ⟨1, le_refl _, by simp [h1]⟩
  obtain ⟨β0, h0, e0⟩ := hbn 0 (by norm_num)
  obtain ⟨β1, h1, e1⟩ := hbn 1 (by norm_num)
  obtain ⟨β2, h2, e2⟩ := hbn 2 (by norm_num)
  obtain ⟨β3, h3, e3⟩ := hbn 3 (by norm_num)
  obtain ⟨β4, h4, e4⟩ := hbn 4 (by norm_num)
  obtain ⟨β5, h5, e5⟩ := hbn 5 (by norm_num)
  have hp1 : (1 : ℕ) < ringChar F := by omega
  have hprod : β1 * β2 * β3 * β4 * β5 = 0 := by
    have hle : β1 * β2 * β3 * β4 * β5 ≤ 1 := by
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4) h5
    have hcast : ((β1 * β2 * β3 * β4 * β5 : ℕ) : F) = ((0 : ℕ) : F) := by
      push_cast; rw [← e1, ← e2, ← e3, ← e4, ← e5, hx]
    exact natCast_inj_lt (by omega) (by omega) hcast
  set s : ℕ := β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4 + 32 * β5 with hs
  have hs61 : s ≤ 61 := by
    by_contra hc
    have h11 : β1 = 1 ∧ β2 = 1 ∧ β3 = 1 ∧ β4 = 1 ∧ β5 = 1 := by omega
    obtain ⟨r1, r2, r3, r4, r5⟩ := h11
    rw [r1, r2, r3, r4, r5] at hprod
    norm_num at hprod
  have hsum : ∑ i ∈ Finset.range 6, (2 : F) ^ i * bt i = (s : F) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      e0, e1, e2, e3, e4, e5, hs]
    push_cast; ring
  have hk := natOf_lt hF len
  have heq : ((natOf len + s : ℕ) : F) = ((61 : ℕ) : F) := by
    push_cast; rw [natOf_cast hF len, ← hsum]; linear_combination hc
  rw [CharP.natCast_eq_natCast F (ringChar F)] at heq
  rcases le_or_gt 61 (natOf len + s) with hge | hlt
  · have hdvd : ringChar F ∣ natOf len + s - 61 := (Nat.modEq_iff_dvd' hge).mp heq.symm
    have hz : natOf len + s - 61 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · omega

variable (Q : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
  (hF : GeneratedField.PrimeFieldElems F)
include hsat hF

/-- **The depth guard at every row**: `natOf len ≤ 61`. -/
theorem walk_len_le (hp : 64 ≤ ringChar F) (i : ℕ) (hi : i < n) :
    natOf ((walkEnvF b hn nodes orbit chals pubs Q i).trace WChip.len) ≤ 61 := by
  have hb := (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat i hi).1
  set eF := walkEnvF b hn nodes orbit chals pubs Q i
  have gb : ∀ j < 6, eF.trace (WChip.bit0 + j) * (eF.trace (WChip.bit0 + j) - 1) = 0 := by
    intro j hj
    have := hb (boolE (WChip.bt j))
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    simpa [CoeffExpr.eval, cv, boolE, WChip.bt] using this
  have gu := hb (.sub (cv WChip.u) (.mul (WChip.bt 1) (WChip.bt 2))) (by simp [WChip.baseGates])
  have gx := hb (.mul (.mul (cv WChip.u) (WChip.bt 3)) (.mul (WChip.bt 4) (WChip.bt 5)))
    (by simp [WChip.baseGates])
  have gc := hb (.sub (.add (cv WChip.len) (bitSum WChip.bit0 6)) (.const 61))
    (by simp [WChip.baseGates])
  simp only [CoeffExpr.eval] at gu gx
  have gc' : eF.trace WChip.len + ∑ i ∈ Finset.range 6, (2 : F) ^ i * eF.trace (WChip.bit0 + i)
      - 61 = 0 := by
    rw [← eval_bitSum]; exact gc
  refine certNat_le_61 hF hp (fun j => eF.trace (WChip.bit0 + j)) gb ?_ _ gc'
  rw [← sub_eq_zero.mp gu]; linear_combination gx

theorem walk_F_rows (hp : 64 ≤ ringChar F) :
    ∀ i, 1 ≤ i → i ≤ n →
      WalkVCL.F (walkDataOf δF kroots b hn nodes orbit chals pubs Q).X 62
        ((walkDataOf δF kroots b hn nodes orbit chals pubs Q).lbl i)
        (fun j : Fin 2 => if (j : ℕ) < (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo i
          then some ((walkDataOf δF kroots b hn nodes orbit chals pubs Q).clab i (j + 1)) else none) := by
  intro i hi1 hin
  have hj : i - 1 < n := by omega
  have hlen := walk_len_le δF kroots b hn nodes orbit chals pubs Q hsat hF hp (i - 1) hj
  have hlt := natOf_lt hF ((walkEnvF b hn nodes orbit chals pubs Q (i - 1)).trace WChip.len)
  refine F_of_parts _ _ (List.mem_ofFn.mpr ⟨⟨i - 1, hj⟩, rfl⟩) _ _ rfl ?_
  show (zq _ : ZMod (ringChar F)).val < 62
  rw [zq, ZMod.val_natCast_of_lt hlt]; omega

/-- The fanout of row `j + 1` cast to `F` is `cL + cR`. -/
theorem walk_fo_cast (j : ℕ) (hj : j < n) :
    (((walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo (j + 1) : ℕ) : F) =
      (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cL +
        (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cR := by
  have hb := (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat j hj).1
  have gL := hb (boolE (cv WChip.cL)) (by simp [WChip.baseGates])
  have gR := hb (boolE (cv WChip.cR)) (by simp [WChip.baseGates])
  simp only [CoeffExpr.eval] at gL gR
  have bL := bool_val gL
  have bR := bool_val gR
  show ((WalkVCL.fanout (lblRow δF _ _).1 : ℕ) : F) = _
  simp only [Nat.add_sub_cancel, lblRow, WalkVCL.fanout]
  push_cast
  rw [← bit_cast bL, ← bit_cast bR]
  simp

include hbind hinj hadj

/-- **The queue counter's closed form**: `q(row j) = kroots + Sf fo (j + 1) − (j + 1)`. -/
theorem walk_q_closed :
    ∀ j < n, (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.q =
      (((kroots + Nock.Walk.Sf (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo (j + 1) : ℕ)) : F)
        - ((j + 1 : ℕ) : F) := by
  intro j
  induction j with
  | zero =>
    intro h0
    have hb := (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat 0 h0).1
    have g := hb (.mul (cv WChip.isF) (.add (.sub (.sub (.sub (cv WChip.q) (.const (kroots : F)))
      (cv WChip.cL)) (cv WChip.cR)) (.const 1))) (by simp [WChip.baseGates])
    have hm := (walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj 0 h0).1
    have hfo := walk_fo_cast δF kroots b hn nodes orbit chals pubs Q hsat hF 0 h0
    simp only [CoeffExpr.eval, cv] at g hfo ⊢
    rw [hm, if_pos rfl, one_mul] at g
    rw [Nock.Walk.Sf_one]
    push_cast
    rw [hfo]; linear_combination g
  | succ m ih =>
    intro hm1
    have hb := (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat m (by omega)).1
    have g := hb (.mul (notE (cv WChip.isL)) (.add (.sub (.sub (.sub (nv WChip.q) (cv WChip.q))
      (nv WChip.cL)) (nv WChip.cR)) (.const 1))) (by simp [WChip.baseGates])
    have hm := (walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj m (by omega)).2.1
    have hfo := walk_fo_cast δF kroots b hn nodes orbit chals pubs Q hsat hF (m + 1) hm1
    have hnx := walk_traceNext δF kroots b hn nodes orbit chals pubs Q hadj m hm1
    simp only [CoeffExpr.eval, cv, nv, notE, hnx] at g
    rw [hm, if_neg (by omega), sub_zero, one_mul] at g
    rw [Nock.Walk.Sf_succ]
    push_cast at ih hfo ⊢
    rw [ih (by omega)] at g
    rw [hfo]; linear_combination g

/-- **Off the last row the queue is non-empty**: `kroots + Sf fo i ≠ i` for `1 ≤ i < n`. -/
theorem walk_queue_ne :
    ∀ i, 1 ≤ i → i < n →
      kroots + Nock.Walk.Sf (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo i ≠ i := by
  intro i hi1 hin heq
  have hb := (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat (i - 1) (by omega)).1
  have g := hb (.mul (notE (cv WChip.isL)) (.sub (.mul (cv WChip.q) (cv WChip.qinv)) (.const 1)))
    (by simp [WChip.baseGates])
  have hm := (walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj (i - 1) (by omega)).2.1
  have hq := walk_q_closed δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF (i - 1)
    (by omega)
  simp only [CoeffExpr.eval, cv, notE] at g
  rw [hm, if_neg (by omega), sub_zero, one_mul] at g
  rw [show i - 1 + 1 = i by omega, heq, sub_self] at hq
  rw [hq, zero_mul] at g
  exact zero_ne_one (sub_eq_zero.mp g)

/-- **BFS queue validity** (`BFSValidF`), through trunk's `bfsValidF_of_ratio_gate` at `α = 2 ∈ ℚ`. -/
theorem walk_bfsValid (hk : 1 ≤ kroots) :
    Nock.Walk.BFSValidF kroots (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo n := by
  refine Nock.RedTeam.Batch478.bfsValidF_of_ratio_gate (K := ℚ) (α := 2) hk ?_
  intro i hi1 hin he
  apply walk_queue_ne δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF i hi1 hin
  have h2 : ((2 ^ (kroots + Nock.Walk.Sf (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo i)
      : ℕ) : ℚ) = ((2 ^ i : ℕ) : ℚ) := by push_cast; exact he
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h2)

/-- **The forest tiling** `kroots + Sf fo n = n` (last-row `q = 0`, `kroots + n < p`).  W4b: the bound
is `kroots + n < p`, not `3n < p`: off the last row the integer queue length `kroots + Sf i − i` starts
at `kroots ≥ 1`, never decreases by more than one per row and is never `0` (`walk_queue_ne`), so it is
`≥ 0` at the last row and `≤ kroots + n`; a multiple of `p` in `[0, kroots + n]` is `0`. -/
theorem walk_tiling (hk : 1 ≤ kroots) (hkp : kroots + n < ringChar F) :
    kroots + Nock.Walk.Sf (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo n = n := by
  have hb := (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat (n - 1) (by omega)).1
  have g := hb (.mul (cv WChip.isL) (cv WChip.q)) (by simp [WChip.baseGates])
  have hm := (walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj (n - 1) (by omega)).2.1
  have hq := walk_q_closed δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF (n - 1)
    (by omega)
  simp only [CoeffExpr.eval, cv] at g
  rw [hm, if_pos (by omega), one_mul] at g
  rw [show n - 1 + 1 = n by omega, g] at hq
  have hS := Sf_le_two (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo
    (fun i => by exact WalkVCL.fanout_le _) n
  have hlow : ∀ i, i < n →
      i < kroots + Nock.Walk.Sf (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have hsucc := Nock.Walk.Sf_succ (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo i
      have hne := walk_queue_ne δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF (i + 1)
        (by omega) hi
      omega
  have hge : n ≤ kroots + Nock.Walk.Sf (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo n := by
    have h1 := hlow (n - 1) (by omega)
    have hsucc := Nock.Walk.Sf_succ (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo (n - 1)
    rw [show n - 1 + 1 = n by omega] at hsucc
    omega
  have e := sub_eq_zero.mp hq.symm
  obtain ⟨d, hd⟩ : ∃ d, kroots + Nock.Walk.Sf (walkDataOf δF kroots b hn nodes orbit chals pubs Q).fo n
      = n + d := ⟨_, (Nat.add_sub_cancel' hge).symm⟩
  rw [hd, Nat.cast_add] at e
  have hd0 : ((d : ℕ) : F) = ((0 : ℕ) : F) := by
    rw [Nat.cast_zero]; exact add_left_cancel (e.trans (add_zero _).symm)
  have := natCast_inj_lt (F := F) (show d < ringChar F by omega) (by omega) hd0
  omega

theorem walkHyps_of_chip [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime]
    [Algebra (ZMod (ringChar F)) K] (hk : 1 ≤ kroots) (hkn : kroots ≤ n)
    (hkp : kroots + n < ringChar F) (hp : 64 ≤ ringChar F) :
    WalkVCL.WalkHyps (algebraMap F K δF) (walkDataOf δF kroots b hn nodes orbit chals pubs Q) :=
  ⟨hk, walk_tiling δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkp,
    walk_bfsValid δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk,
    fun i => WalkVCL.fanout_le _, fun _ _ _ => rfl,
    walk_F_rows δF kroots b hn nodes orbit chals pubs Q hsat hF hp⟩

omit hadj in
theorem rootGate_of_chip (hkn : kroots ≤ n) (hp : 64 ≤ ringChar F) :
    WalkVCL.RootGate (walkDataOf δF kroots b hn nodes orbit chals pubs Q).X
      (walkDataOf δF kroots b hn nodes orbit chals pubs Q).lbl kroots := by
  intro i hi1 hik
  have hj : i - 1 < n := by omega
  obtain ⟨hb, -, hm⟩ := walk_gates δF kroots b hn nodes orbit chals pubs Q hsat (i - 1) hj
  have hr := (walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj (i - 1) hj).2.2
  rw [if_pos (by omega)] at hr
  set eF := walkEnvF b hn nodes orbit chals pubs Q (i - 1)
  set eK := walkEnvK δF kroots b hn nodes orbit chals pubs Q (i - 1)
  have g1 := hb (.mul (cv WChip.rM) (.sub (cv WChip.pre) (.const 1))) (by simp [WChip.baseGates])
  have g2 := hb (.mul (cv WChip.rM) (cv WChip.len)) (by simp [WChip.baseGates])
  have g3 := hb (.mul (cv WChip.rM) (.sub (cv WChip.ridx) (cv WChip.idx))) (by simp [WChip.baseGates])
  simp only [CoeffExpr.eval, cv] at g1 g2 g3
  rw [hr, one_mul] at g1 g2 g3
  have hpre : eF.trace WChip.pre = ((1 : ℕ) : F) := by rw [Nat.cast_one]; exact sub_eq_zero.mp g1
  have hlen : eF.trace WChip.len = ((0 : ℕ) : F) := by rw [Nat.cast_zero]; exact g2
  have hroot : (QFP.var WChip.rootR).ev δF eK eF = (QFP.var WChip.pR).ev δF eK eF :=
    PathModel.fp_of_scaled δF (cv WChip.rM) _ _ eK eF (by simp [CoeffExpr.eval, cv]; exact hr)
      fun e he => hm e (by unfold WChip.qEqs; exact List.mem_append_left _ he)
  refine ⟨⟨?_, ?_, hroot⟩, keyRow δF eK eF, List.mem_ofFn.mpr ⟨⟨i - 1, hj⟩, rfl⟩, rfl, ?_⟩
  · show zq (eF.trace WChip.pre) = 1
    rw [zq, hpre, natOf_natCast hF (by omega)]; simp
  · show zq (eF.trace WChip.len) = 0
    rw [zq, hlen, natOf_natCast hF (by omega)]; simp
  · show zq (eF.trace WChip.ridx) = ((natOf (eF.trace WChip.idx) : ℕ) : ZMod (ringChar F))
    rw [zq, sub_eq_zero.mp g3]

end Hyps

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
