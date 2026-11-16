/-
  Nock/NockVMROM/Thm54/DecodedLambdaEvent.lean

  **The THIRTY-SECOND move's event.**  The env-parametric decoded guarded Form R λ-event, below the
  pinned file (the 26th's `memoryForestAlphaEventOfEnvs` pattern), with its trace-uniform card bound
  `|𝕂|¹⁰ · M·(3N + 67 + (n − 1))` (`= M·(3N+130)` at `n = 64`) at every env tuple, no premise.
  `slotCert` is the record-structure slot map (C-a).

  Imports: exactly the five §C′ prescribes.

  Read set (round 0 only, C-b): memory base selectors `0..2` (`memRowStateOf`), memory base column
  `181` (`reqIdx`, via `natLift`); compute source selectors `0..9`; the certificate block
  `202..270` (bits `202..264`, shift `265..270`).  No `𝕂` role, no challenge.  The verify node's
  `a` is written `0` (`formRCounts` ignores it, `Batch747.formRCounts_verify_ignores_a`).

  **C-a, the slot→certificate map** (`Batch747.sampledSlotT_structure` / `sampledSlotC_structure`):
  slot `0` is the constant record `(λ, λ^{n−1} + λ^{n−2})` = `(Tpoly 1, C'poly n [c₁ = 1])`, i.e. the
  certificate `(shift 1, bits {1})` (axis 3; written `(λ, 1+λ)` in the gate text up to the common
  `λ^{n−2}` scale); slot `1` is the row's certificate iff selector `0` is set, else the constant
  `(λ, λ^{n−1})` = certificate `(shift 1, no bits)` (axis 2, `G·λ`, `G·λ^{n−1}`); slot `2` is the
  row's certificate iff selector `9`, else (selector `6`) the same axis-2 constant.

  -- the paper
-/
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.FormRCore
import Nock.NockVMROM.Thm54.RecordCarrier
import Nock.NockVMROM.Thm54.HostileRecordLists

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.DecodedLambdaEvent

open scoped Classical BigOperators Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.RedTeam.Batch575
open Polynomial

noncomputable section

/-! ## 0. A width-free degree bound for `formRCounts` (fresh; generalizes `natDegree_formRCounts_coeff`)

`Batch575.natDegree_formRCounts_coeff` needs `mm e ≤ n − 1`; a decoded hostile shift is bounded by
its 6-bit encoding (`≤ 63`) but not by `n − 1` at small `p`.  With `mm ≤ B`:
`deg_Y ≤ decompCount + (n − 1) + B`.  At `B = n − 1` this is the existing `2(n−1)` bound. -/

section Degree
variable {K : Type} [Field K]

theorem natDegree_formRPw_coeff_le (n : ℕ) (mm : ℕ → ℕ) (B : ℕ) (hmm : ∀ e, mm e ≤ B) (e : ℕ) :
    ∀ t : MTree K, ((formRPw n mm t).coeff e).natDegree ≤ decompCount t + (n - 1) + B := by
  intro t
  induction t with
  | halt => simp [formRPw]
  | decompose L R ihl ihr =>
      have hp : (formRPw n mm (.decompose L R)).coeff e
          = Y * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e) := by
        simp only [formRPw, coeff_C_mul, coeff_add]
      rw [hp]
      have hadd := natDegree_add_le ((formRPw n mm L).coeff e) ((formRPw n mm R).coeff e)
      have hmul := natDegree_mul_le (p := (X : Polynomial K))
        (q := (formRPw n mm L).coeff e + (formRPw n mm R).coeff e)
      simp only [decompCount, Y, natDegree_X] at hmul ⊢
      omega
  | read e' ch ih =>
      have hp : (formRPw n mm (.read e' ch)).coeff e
          = (formRPw n mm ch).coeff e
            - if e = e' then scale n * Tpoly (mm e') else 0 := by
        simp only [formRPw, coeff_sub, coeff_const_X_pow]
      rw [hp]
      refine (natDegree_sub_le _ _).trans ?_
      simp only [decompCount]
      split_ifs with _he
      · have hs : (scale n * Tpoly (mm e')).natDegree ≤ (n - 1) + B :=
          (natDegree_mul_le (p := scale n) (q := Tpoly (mm e'))).trans (by
            have := natDegree_scale (K := K) n
            have := natDegree_Tpoly (K := K) (mm e')
            have := hmm e'
            omega)
        omega
      · simp; omega
  | verify e' a ch ih =>
      have hp : (formRPw n mm (.verify e' a ch)).coeff e
          = (formRPw n mm ch).coeff e + if e = e' then scale n else 0 := by
        simp only [formRPw, coeff_add, coeff_const_X_pow]
      rw [hp]
      refine (natDegree_add_le _ _).trans ?_
      simp [decompCount]
      split_ifs
      · have := natDegree_scale (K := K) n; omega
      · simp; omega

theorem natDegree_formRCounts_coeff_le (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (B : ℕ)
    (hmm : ∀ e, mm e ≤ B) (e : ℕ) :
    ∀ t : MTree K,
      ((formRCounts n mm cc t).coeff e).natDegree ≤ decompCount t + (n - 1) + B := by
  intro t
  induction t with
  | halt => simp [formRCounts]
  | decompose L R ihl ihr =>
      have hc : (formRCounts n mm cc (.decompose L R)).coeff e
          = (formRCounts n mm cc L).coeff e + (formRCounts n mm cc R).coeff e
            + (Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e)
            + (formRPw n mm R).coeff e := by
        simp only [formRCounts, coeff_add, coeff_C_mul]
      rw [hc]
      have hpwL := natDegree_formRPw_coeff_le n mm B hmm e L
      have hpwR := natDegree_formRPw_coeff_le n mm B hmm e R
      have hY : (Y - 1 : Polynomial K).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (by simp [Y, natDegree_X, natDegree_one])
      have hmul : ((Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e)).natDegree
          ≤ 1 + max (decompCount L + (n - 1) + B) (decompCount R + (n - 1) + B) := by
        refine (natDegree_mul_le (p := Y - 1)
          (q := (formRPw n mm L).coeff e + (formRPw n mm R).coeff e)).trans ?_
        have := natDegree_add_le ((formRPw n mm L).coeff e) ((formRPw n mm R).coeff e)
        omega
      have h1 := natDegree_add_le
        ((formRCounts n mm cc L).coeff e + (formRCounts n mm cc R).coeff e
          + (Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e))
        ((formRPw n mm R).coeff e)
      have h2 := natDegree_add_le
        ((formRCounts n mm cc L).coeff e + (formRCounts n mm cc R).coeff e)
        ((Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e))
      have h3 := natDegree_add_le
        ((formRCounts n mm cc L).coeff e) ((formRCounts n mm cc R).coeff e)
      simp [decompCount] at ihl ihr hpwL hpwR hmul h1 h2 h3 ⊢
      omega
  | read e' ch ih =>
      have hc : (formRCounts n mm cc (.read e' ch)).coeff e
          = (formRCounts n mm cc ch).coeff e
            - if e = e' then Tpoly (mm e') * C'poly n (cc e') else 0 := by
        simp only [formRCounts, coeff_sub, coeff_const_X_pow]
      rw [hc]
      refine (natDegree_sub_le _ _).trans ?_
      simp [decompCount]
      split_ifs
      · have : (Tpoly (mm e') * C'poly n (cc e')).natDegree ≤ (n - 1) + B :=
          (natDegree_mul_le (p := Tpoly (mm e')) (q := C'poly n (cc e'))).trans (by
            have := natDegree_Tpoly (K := K) (mm e')
            have := natDegree_C'poly (K := K) n (cc e')
            have := hmm e'
            omega)
        omega
      · simp; omega
  | verify e' a ch ih =>
      have hc : (formRCounts n mm cc (.verify e' a ch)).coeff e
          = (formRCounts n mm cc ch).coeff e + if e = e' then scale n else 0 := by
        simp only [formRCounts, coeff_add, coeff_const_X_pow]
      rw [hc]
      refine (natDegree_add_le _ _).trans ?_
      simp [decompCount]
      split_ifs
      · have := natDegree_scale (K := K) n; omega
      · simp; omega

end Degree

/-! ## 1. The compute side: arities, prefix sums, the exponent locator, the certificate map -/

section Compute
variable {K : Type} [Field K] {N : ℕ}

/-- Request arity of a compute row from the source selectors (`sampledActive`: slot 0 always;
slot 1 on `s0,s2,s5..s9`; slot 2 on `s6,s9`), as `activeMask = 1` tests. -/
def computeArity (env : Env K) : ℕ :=
  1 + (if env.trace 0 + (env.trace 2 + (env.trace 5 + (env.trace 6 + (env.trace 7 +
          (env.trace 8 + env.trace 9))))) = 1 then 1 else 0)
    + (if env.trace 6 + env.trace 9 = 1 then 1 else 0)

theorem computeArity_le (env : Env K) : computeArity env ≤ 3 := by
  unfold computeArity; split_ifs <;> omega

/-- `S(i')`: the prefix sum of arities of compute rows `< i'`. -/
def computePrefix (envsC : Fin N → Env K) (i : Fin N) : ℕ :=
  ∑ i' ∈ Finset.univ.filter (fun i' : Fin N => i'.val < i.val), computeArity (envsC i')

/-- **The exponent locator**: the compute row `i'` with `S(i') < e ≤ S(i') + arity(i')`, and the
slot `j = e − S(i') − 1`. -/
def locateExp (envsC : Fin N → Env K) (e : ℕ) : Option (Fin N × ℕ) :=
  ((List.finRange N).find? fun i =>
      decide (computePrefix envsC i < e ∧ e ≤ computePrefix envsC i + computeArity (envsC i))).map
    fun i => (i, e - computePrefix envsC i - 1)

/-- The row's 6-bit shift `m` (columns `265..270`, `colM k = col0 + 63 + k`). -/
def rowShift (env : Env K) : ℕ :=
  ∑ k ∈ Finset.range 6, if env.trace (265 + k) = 1 then 2 ^ k else 0

theorem rowShift_le (env : Env K) : rowShift env ≤ 63 := by
  unfold rowShift
  calc (∑ k ∈ Finset.range 6, if env.trace (265 + k) = 1 then 2 ^ k else 0)
      ≤ ∑ k ∈ Finset.range 6, 2 ^ k := Finset.sum_le_sum fun k _ => by split_ifs <;> simp
    _ = 63 := by decide

/-- The row's certificate bits `c_k`, `1 ≤ k ≤ 63` at column `202 + (k − 1)`. -/
def rowBits (env : Env K) (k : ℕ) : Bool :=
  decide (1 ≤ k ∧ k ≤ 63 ∧ env.trace (202 + (k - 1)) = 1)

/-- **The slot→certificate map (C-a, pinned to the deployed records' structure).**  A certificate is
`(shift, bits)`; `Tpoly shift · C'poly n bits` is the record's `(T, C')` at `λ`.  Slot `0`: the constant
`(1, {1})` (`(λ, λ^{n−1}+λ^{n−2})`, `sampledSlotT/C 67`).  Slot `1`: the row's certificate iff
selector `0` (`trace 0 = 1`), else the constant `(1, ∅)` (`(λ, λ^{n−1})`, the `G` arm of base `75`).
Slot `2`: the row's certificate iff selector `9` (`trace 9 = 1`), else `(1, ∅)` (the selector-`6`
arm of base `83`).  Reads only round-0 columns (`0`, `9`, `202..270`). -/
def slotCert (envsC : Fin N → Env K) (i : Fin N) (j : ℕ) : ℕ × (ℕ → Bool) :=
  match j with
  | 0 => (1, fun k => decide (k = 1))
  | 1 => if (envsC i).trace 0 = 1 then (rowShift (envsC i), rowBits (envsC i))
         else (1, fun _ => false)
  | _ => if (envsC i).trace 9 = 1 then (rowShift (envsC i), rowBits (envsC i))
         else (1, fun _ => false)

theorem slotCert_shift_le (envsC : Fin N → Env K) (i : Fin N) (j : ℕ) :
    (slotCert envsC i j).1 ≤ 63 := by
  unfold slotCert
  split
  · simp
  · split_ifs
    · exact rowShift_le _
    · simp
  · split_ifs
    · exact rowShift_le _
    · simp

/-- Decoded shift `m_e` of exponent `e` (through the locator; `0` if unlocated). -/
def decodedShift (envsC : Fin N → Env K) (e : ℕ) : ℕ :=
  match locateExp envsC e with
  | some (i, j) => (slotCert envsC i j).1
  | none => 0

/-- Decoded certificate bits `c_e` of exponent `e`. -/
def decodedBits (envsC : Fin N → Env K) (e k : ℕ) : Bool :=
  match locateExp envsC e with
  | some (i, j) => (slotCert envsC i j).2 k
  | none => false

theorem decodedShift_le (envsC : Fin N → Env K) (e : ℕ) : decodedShift envsC e ≤ 63 := by
  unfold decodedShift
  split
  · exact slotCert_shift_le _ _ _
  · omega

end Compute

/-! ## 2. The memory side: a fresh `decodedMTreeOfEnvs` by BFS inversion of `fo` -/

section Memory
variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}

/-- BFS child index of (1-indexed) row `i`, child slot `l ∈ {1, 2}`:
`kroots + Sf fo (i − 1) + l` (the `RAP_walk` forest layout, `foOfMem`). -/
def childIdx (envsF : Fin M → Env F) (kroots i l : ℕ) : ℕ :=
  kroots + Sf (foOfMem envsF) (i - 1) + l

/-- Decoded exponent of row `i`: `natLift reqIdx` (base column 181). -/
def rowExp (envsF : Fin M → Env F) (r : Fin M) : ℕ := RecordCarrier.natLift ((envsF r).trace 181)

/-- **`decodedMTreeOfEnvs`**: the subtree rooted at 1-indexed row `i`.  Shape from the memory
selectors (`memRowStateOf`, cols 0..2) and the BFS inversion of `fo`; read/verify exponents
`natLift reqIdx`.  A child is followed only when its index exceeds the parent's (always true on
reachable rows of a BFS layout; here a termination device).  The verify node's `a` is written
`0`: `formRCounts` never reads it, and reading a `𝕂` role (e.g. the record's `T` slot, which is
λ-dependent) would put a post-challenge column into the read set.  `envsK` is kept
as a parameter for the text's interface; nothing in the decoded event reads it. -/
def decodedMTreeOfEnvs (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ) (i : ℕ) :
    MTree K :=
  if h : 1 ≤ i ∧ i ≤ M then
    match memRowStateOf (envsF ⟨i - 1, by omega⟩) with
    | .halt => .halt
    | .decompose =>
        .decompose
          (if i < childIdx envsF kroots i 1 then
            decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 1) else .halt)
          (if i < childIdx envsF kroots i 2 then
            decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 2) else .halt)
    | .read_root =>
        .read (rowExp envsF ⟨i - 1, by omega⟩)
          (if i < childIdx envsF kroots i 1 then
            decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 1) else .halt)
    | .verify_child =>
        .verify (rowExp envsF ⟨i - 1, by omega⟩) 0
          (if i < childIdx envsF kroots i 1 then
            decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 1) else .halt)
  else .halt
termination_by M + 1 - i
decreasing_by all_goals omega

/-- The rows reached from row `i` along the same followed edges. -/
def reachRows (envsF : Fin M → Env F) (kroots : ℕ) (i : ℕ) : Finset ℕ :=
  if h : 1 ≤ i ∧ i ≤ M then
    {i} ∪
      ((if 1 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) ∪
       (if 2 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 2 then
          reachRows envsF kroots (childIdx envsF kroots i 2) else ∅))
  else ∅
termination_by M + 1 - i
decreasing_by all_goals omega

theorem foOfMem_eq (envsF : Fin M → Env F) (i : ℕ) (h : 1 ≤ i ∧ i ≤ M) :
    foOfMem envsF i = MemoryTable.fanoutMem (memRowStateOf (envsF ⟨i - 1, by omega⟩)) := by
  unfold foOfMem; rw [dif_pos ⟨h.1, by omega⟩]

end Memory

section Forest
variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}
variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)

theorem reach_eq (i : ℕ) (h : 1 ≤ i ∧ i ≤ M) :
    reachRows envsF kroots i = {i} ∪
      ((if 1 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) ∪
       (if 2 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 2 then
          reachRows envsF kroots (childIdx envsF kroots i 2) else ∅)) := by
  rw [reachRows, dif_pos h]

theorem reach_out (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ M)) : reachRows envsF kroots i = ∅ := by
  rw [reachRows, dif_neg h]

theorem tree_out (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ M)) :
    decodedMTreeOfEnvs envsK envsF kroots i = .halt := by
  rw [decodedMTreeOfEnvs, dif_neg h]

/-- Measure induction: children have strictly larger index. -/
theorem measure_induction (P : ℕ → Prop)
    (step : ∀ i, (∀ c, i < c → 1 ≤ i → i ≤ M → P c) → P i) : ∀ i, P i := by
  have key : ∀ d i, M + 1 - i ≤ d → P i := by
    intro d
    induction d with
    | zero => intro i hi; exact step i fun c _ h1 h2 => absurd hi (by omega)
    | succ d ih =>
        intro i hi
        exact step i fun c hc h1 h2 => ih c (by omega)
  exact fun i => key _ i le_rfl

theorem reach_bounds : ∀ i y, y ∈ reachRows envsF kroots i → i ≤ y ∧ 1 ≤ y ∧ y ≤ M := by
  refine measure_induction (M := M) _ fun i ih => ?_
  intro y hy
  by_cases h : 1 ≤ i ∧ i ≤ M
  · rw [reach_eq envsF kroots i h] at hy
    simp only [Finset.mem_union, Finset.mem_singleton] at hy
    rcases hy with rfl | hy | hy
    · exact ⟨le_rfl, h.1, h.2⟩
    · split_ifs at hy with hc
      · have := ih _ hc.2 h.1 h.2 y hy; exact ⟨by omega, this.2⟩
      · simp at hy
    · split_ifs at hy with hc
      · have := ih _ hc.2 h.1 h.2 y hy; exact ⟨by omega, this.2⟩
      · simp at hy
  · rw [reach_out envsF kroots i h] at hy; simp at hy

theorem self_mem_reach (i : ℕ) (h : 1 ≤ i ∧ i ≤ M) : i ∈ reachRows envsF kroots i := by
  rw [reach_eq envsF kroots i h]; simp

/-- A non-root element of `reach x` is a followed child of some `p ∈ reach x`. -/
theorem reach_parent : ∀ x y, y ∈ reachRows envsF kroots x → y ≠ x →
    ∃ p ∈ reachRows envsF kroots x, ∃ l, 1 ≤ l ∧ l ≤ foOfMem envsF p ∧
      p < childIdx envsF kroots p l ∧ y = childIdx envsF kroots p l := by
  refine measure_induction (M := M) _ fun x ih => ?_
  intro y hy hne
  by_cases h : 1 ≤ x ∧ x ≤ M
  · have hy' := hy
    rw [reach_eq envsF kroots x h] at hy'
    simp only [Finset.mem_union, Finset.mem_singleton] at hy'
    have sub : ∀ l, l ≤ foOfMem envsF x → x < childIdx envsF kroots x l → (l = 1 ∨ l = 2) →
        reachRows envsF kroots (childIdx envsF kroots x l) ⊆ reachRows envsF kroots x := by
      intro l hl hc hl12 z hz
      rw [reach_eq envsF kroots x h]
      rcases hl12 with rfl | rfl
      · simp only [Finset.mem_union]; right; left; rw [if_pos ⟨by
          rcases Nat.eq_zero_or_pos (foOfMem envsF x) with h0 | h0 <;> omega, hc⟩]; exact hz
      · simp only [Finset.mem_union]; right; right; rw [if_pos ⟨hl, hc⟩]; exact hz
    rcases hy' with rfl | hy' | hy'
    · exact absurd rfl hne
    · split_ifs at hy' with hc
      · by_cases hyc : y = childIdx envsF kroots x 1
        · exact ⟨x, self_mem_reach envsF kroots x h, 1, le_rfl, hc.1, hc.2, hyc⟩
        · obtain ⟨p, hp, l, hl⟩ := ih _ hc.2 h.1 h.2 y hy' hyc
          exact ⟨p, sub 1 hc.1 hc.2 (Or.inl rfl) hp, l, hl⟩
      · simp at hy'
    · split_ifs at hy' with hc
      · by_cases hyc : y = childIdx envsF kroots x 2
        · exact ⟨x, self_mem_reach envsF kroots x h, 2, by omega, hc.1, hc.2, hyc⟩
        · obtain ⟨p, hp, l, hl⟩ := ih _ hc.2 h.1 h.2 y hy' hyc
          exact ⟨p, sub 2 hc.1 hc.2 (Or.inr rfl) hp, l, hl⟩
      · simp at hy'
  · rw [reach_out envsF kroots x h] at hy; simp at hy

theorem Sf_succ (fo : ℕ → ℕ) (p : ℕ) (hp : 1 ≤ p) : Sf fo p = Sf fo (p - 1) + fo p := by
  unfold Sf
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

theorem Sf_mono (fo : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : Sf fo a ≤ Sf fo b := by
  unfold Sf
  exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl h)

/-- **BFS inversion is injective**: a child index determines its parent. -/
theorem child_parent_unique {p p' l l' : ℕ} (hp : 1 ≤ p) (hp' : 1 ≤ p')
    (hl : 1 ≤ l) (hl' : l ≤ foOfMem envsF p) (hm : 1 ≤ l') (hm' : l' ≤ foOfMem envsF p')
    (heq : childIdx envsF kroots p l = childIdx envsF kroots p' l') : p = p' := by
  unfold childIdx at heq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := Sf_succ (foOfMem envsF) p hp
    have h2 := Sf_mono (foOfMem envsF) (show p ≤ p' - 1 by omega)
    omega
  · have h1 := Sf_succ (foOfMem envsF) p' hp'
    have h2 := Sf_mono (foOfMem envsF) (show p' ≤ p - 1 by omega)
    omega

/-- **Disjointness**: incomparable rows have disjoint reach sets. -/
theorem reach_disjoint (x y : ℕ) (hxy : x ≠ y) (hx : x ∉ reachRows envsF kroots y)
    (hy : y ∉ reachRows envsF kroots x) :
    Disjoint (reachRows envsF kroots x) (reachRows envsF kroots y) := by
  rw [Finset.disjoint_left]
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hzx hzy
    have hzx' : z ≠ x := fun h => hx (h ▸ hzy)
    have hzy' : z ≠ y := fun h => hy (h ▸ hzx)
    obtain ⟨p, hp, l, hl1, hl2, hpl, rfl⟩ := reach_parent envsF kroots x z hzx hzx'
    obtain ⟨p', hp', l', hl1', hl2', hpl', heq⟩ := reach_parent envsF kroots y _ hzy hzy'
    have hb := reach_bounds envsF kroots x p hp
    have hb' := reach_bounds envsF kroots y p' hp'
    have := child_parent_unique envsF kroots hb.2.1 hb'.2.1 hl1 hl2 hl1' hl2' heq
    subst this
    exact ih p hpl hp hp'

/-- **The forest's decomposition count is bounded by its reach.** -/
theorem decompCount_le_reach : ∀ i,
    decompCount (decodedMTreeOfEnvs envsK envsF kroots i) ≤ (reachRows envsF kroots i).card := by
  refine measure_induction (M := M) _ fun i ih => ?_
  by_cases h : 1 ≤ i ∧ i ≤ M
  · have hfo := foOfMem_eq envsF i h
    rw [reach_eq envsF kroots i h, decodedMTreeOfEnvs, dif_pos h]
    -- children's reach sets lie strictly above `i`
    have habove : ∀ l, i < childIdx envsF kroots i l →
        i ∉ reachRows envsF kroots (childIdx envsF kroots i l) := fun l hc hm =>
      absurd (reach_bounds envsF kroots _ i hm).1 (by omega)
    have hchild : ∀ l, decompCount (if i < childIdx envsF kroots i l then
        decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l) else .halt) ≤
        (if i < childIdx envsF kroots i l then
          reachRows envsF kroots (childIdx envsF kroots i l) else ∅).card := by
      intro l; split_ifs with hc
      · exact ih _ hc h.1 h.2
      · simp [decompCount]
    rcases hst : memRowStateOf (envsF ⟨i - 1, by omega⟩) with _ | _ | _ | _
    · -- decompose: fo = 2
      rw [hst] at hfo
      simp only [MemoryTable.fanoutMem] at hfo
      simp only [decompCount]
      have e1 : (if 1 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) =
          (if i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) := by
        simp [hfo]
      have e2 : (if 2 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 2 then
          reachRows envsF kroots (childIdx envsF kroots i 2) else ∅) =
          (if i < childIdx envsF kroots i 2 then
          reachRows envsF kroots (childIdx envsF kroots i 2) else ∅) := by
        simp [hfo]
      rw [e1, e2]
      have hdisj : Disjoint
          (if i < childIdx envsF kroots i 1 then
            reachRows envsF kroots (childIdx envsF kroots i 1) else ∅)
          (if i < childIdx envsF kroots i 2 then
            reachRows envsF kroots (childIdx envsF kroots i 2) else ∅) := by
        split_ifs with hc1 hc2
        · apply reach_disjoint
          · unfold childIdx; omega
          · intro hm
            have hne : childIdx envsF kroots i 1 ≠ childIdx envsF kroots i 2 := by
              unfold childIdx; omega
            obtain ⟨p, hp, l, hl1, hl2, hpl, heq⟩ := reach_parent envsF kroots _ _ hm hne
            have hb := reach_bounds envsF kroots _ p hp
            have := child_parent_unique envsF kroots hb.2.1 h.1 hl1 hl2 (by omega)
              (by omega) heq.symm
            omega
          · intro hm
            have hne : childIdx envsF kroots i 2 ≠ childIdx envsF kroots i 1 := by
              unfold childIdx; omega
            obtain ⟨p, hp, l, hl1, hl2, hpl, heq⟩ := reach_parent envsF kroots _ _ hm hne
            have hb := reach_bounds envsF kroots _ p hp
            have := child_parent_unique envsF kroots hb.2.1 h.1 hl1 hl2 (by omega)
              (by omega) heq.symm
            omega
        all_goals simp
      have hi : i ∉ ((if i < childIdx envsF kroots i 1 then
            reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) ∪
          (if i < childIdx envsF kroots i 2 then
            reachRows envsF kroots (childIdx envsF kroots i 2) else ∅)) := by
        simp only [Finset.mem_union, not_or]
        constructor
        · split_ifs with hc
          · exact habove 1 hc
          · simp
        · split_ifs with hc
          · exact habove 2 hc
          · simp
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hi),
        Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
      have := hchild 1
      have := hchild 2
      omega
    · simp [decompCount]
    · -- read_root: fo = 1
      rw [hst] at hfo
      simp only [MemoryTable.fanoutMem] at hfo
      simp only [decompCount]
      have e1 : (if 1 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) =
          (if i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) := by
        simp [hfo]
      rw [e1]
      refine (hchild 1).trans (Finset.card_le_card ?_)
      intro z hz
      simp only [Finset.mem_union]; right; left; exact hz
    · -- verify_child: fo = 1
      rw [hst] at hfo
      simp only [MemoryTable.fanoutMem] at hfo
      simp only [decompCount]
      have e1 : (if 1 ≤ foOfMem envsF i ∧ i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) =
          (if i < childIdx envsF kroots i 1 then
          reachRows envsF kroots (childIdx envsF kroots i 1) else ∅) := by
        simp [hfo]
      rw [e1]
      refine (hchild 1).trans (Finset.card_le_card ?_)
      intro z hz
      simp only [Finset.mem_union]; right; left; exact hz
  · rw [tree_out envsK envsF kroots i h]; simp [decompCount]

/-- **`Σ_{roots} decompCount ≤ M`** — every hostile forest, every `kroots`. -/
theorem sum_decompCount_le (kroots : ℕ) :
    ∑ r ∈ Finset.Icc 1 kroots, decompCount (decodedMTreeOfEnvs envsK envsF kroots r) ≤ M := by
  calc ∑ r ∈ Finset.Icc 1 kroots, decompCount (decodedMTreeOfEnvs envsK envsF kroots r)
      ≤ ∑ r ∈ Finset.Icc 1 kroots, (reachRows envsF kroots r).card :=
        Finset.sum_le_sum fun r _ => decompCount_le_reach envsK envsF kroots r
    _ = ((Finset.Icc 1 kroots).biUnion fun r => reachRows envsF kroots r).card := by
        rw [Finset.card_biUnion]
        intro r hr r' hr' hne
        have hr1 := Finset.mem_Icc.mp hr
        have hr1' := Finset.mem_Icc.mp hr'
        have notChild : ∀ a b, a ∈ Finset.Icc 1 kroots → b ≠ a →
            b ∈ reachRows envsF kroots a → b ≤ kroots → False := by
          intro a b _ hba hb hbk
          obtain ⟨p, hp, l, hl1, _, _, rfl⟩ := reach_parent envsF kroots a b hb hba
          unfold childIdx at hbk; omega
        apply reach_disjoint envsF kroots r r' hne
        · exact fun h => notChild r' r hr' hne h hr1.2
        · exact fun h => notChild r r' hr (Ne.symm hne) h hr1'.2
    _ ≤ (Finset.Icc 1 M).card := by
        refine Finset.card_le_card fun y hy => ?_
        obtain ⟨r, _, hy⟩ := Finset.mem_biUnion.mp hy
        have := reach_bounds envsF kroots r y hy
        exact Finset.mem_Icc.mpr ⟨this.2.1, this.2.2⟩
    _ = M := by simp

end Forest


/-! ## 3. The guarded decoded event and its trace-uniform card bound -/

section Event
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [Fintype F] [DecidableEq F] {N M : ℕ}

/-- The decoded root polynomial `P_r`. -/
def decodedRootPoly (envsC : Fin N → Env K) (envsK : Fin M → Env K) (envsF : Fin M → Env F)
    (kroots r : ℕ) : Polynomial (Polynomial K) :=
  formRCounts (formRN K) (decodedShift envsC) (decodedBits envsC)
    (decodedMTreeOfEnvs envsK envsF kroots r)

/-- The envelope degree `E' = 3N + 3`, `N` the compute-row count. -/
def decodedEnvelopeDeg (N : ℕ) : ℕ := 3 * N + 3

/-- **Per root**: `if formRGuard P_r E' then formRRootBad P_r E' else ∅`. -/
def decodedRootBad (envsC : Fin N → Env K) (envsK : Fin M → Env K) (envsF : Fin M → Env F)
    (kroots r : ℕ) : Finset (K × K) :=
  if formRGuard (decodedRootPoly envsC envsK envsF kroots r) (decodedEnvelopeDeg N) then
    formRRootBad (decodedRootPoly envsC envsK envsF kroots r) (decodedEnvelopeDeg N)
  else ∅

/-- **The env-parametric decoded guarded λ-event** on the landed tuple: `(αM, λ)` in the union of
the guarded root sets over the roots `1..kroots`. -/
def decodedLambdaEventOfEnvs (envsC : Fin N → Env K) (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots : ℕ) : Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    (alphaM c.1, c.2.2.2.lambda) ∈
      (Finset.Icc 1 kroots).biUnion fun r => decodedRootBad envsC envsK envsF kroots r

/-- The trace-uniform numeral at width `n`: `M·(3N + 67 + (n − 1))`; at `n = 64` it is
`M·(3N + 130)` (`formRUniformWorkloadOf_64`). -/
def formRUniformWorkloadOf (n N M : ℕ) : ℕ := M * (3 * N + 67 + (n - 1))

theorem formRUniformWorkloadOf_64 (N M : ℕ) : formRUniformWorkloadOf 64 N M = M * (3 * N + 130) := by
  unfold formRUniformWorkloadOf; ring_nf

theorem formRUniformWorkloadOf_le_of_width {n : ℕ} (hn : n ≤ 64) (N M : ℕ) :
    formRUniformWorkloadOf n N M ≤ M * (3 * N + 130) := by
  unfold formRUniformWorkloadOf; exact Nat.mul_le_mul_left _ (by omega)

/-- Lift: tuples whose `(αM, λ)` lies in `B` number `≤ |𝕂|⁹·|B|`. -/
theorem lift_card_le (B : Finset (K × K)) :
    (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
        (alphaM c.1, c.2.2.2.lambda) ∈ B).card ≤ Fintype.card K ^ 9 * B.card := by
  let iota : OptimizedProductionChallengeTuple K F →
      ((K × K × K) × ((K × K) × (OptimizedComputeCollisionBound.FinalComputeChallengeTuple K × K)))
        × (K × K) :=
    fun c => (restOf c, (alphaM c.1, c.2.2.2.lambda))
  have hinj : Function.Injective iota := by
    rintro ⟨⟨⟨αc, γ⟩, ⟨αm, z⟩⟩, ⟨io, ⟨eq, ⟨ip, l⟩⟩⟩⟩
      ⟨⟨⟨αc', γ'⟩, ⟨αm', z'⟩⟩, ⟨io', ⟨eq', ⟨ip', l'⟩⟩⟩⟩ h
    simp only [iota, restOf, alphaC, gamma, nprSeed, alphaM, Prod.mk.injEq] at h
    obtain ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩ := h
    rfl
  have himg : (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
        (alphaM c.1, c.2.2.2.lambda) ∈ B).image iota ⊆ Finset.univ ×ˢ B := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ] at hcard
  refine hcard.trans (le_of_eq ?_)
  congr 1
  simp only [Fintype.card_prod, OptimizedStrictPackage.card_finalComputeChallengeTuple]
  ring

/-- Out-of-range roots decode to `halt`, so they are unguarded. -/
theorem decodedRootBad_out (envsC : Fin N → Env K) (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots r : ℕ) (h : ¬ (1 ≤ r ∧ r ≤ M)) :
    decodedRootBad envsC envsK envsF kroots r = ∅ := by
  unfold decodedRootBad decodedRootPoly
  rw [tree_out envsK envsF kroots r h, if_neg]
  -- destructure the guard definitionally (no `formRGuard.eq_1` is generated here, so the

  rintro ⟨k, -, hk⟩
  exact hk (by simp [formRCounts])

/-- **Per guarded root**: `|B_r| ≤ |𝕂|·(decompCount_r + (n − 1) + 63 + E')` — no premise
(`formR_event_card` + `natDegree_formRCounts_coeff_le` at `B = 63`, `decodedShift_le`). -/
theorem decodedRootBad_card_le (envsC : Fin N → Env K) (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots r : ℕ) :
    (decodedRootBad envsC envsK envsF kroots r).card ≤
      Fintype.card K * (decompCount (decodedMTreeOfEnvs envsK envsF kroots r) +
        (formRN K - 1) + 63 + decodedEnvelopeDeg N) := by
  unfold decodedRootBad
  split_ifs with hg
  · obtain ⟨e₀, he₀, hB⟩ := hg
    have h1 : (formRRootBad (decodedRootPoly envsC envsK envsF kroots r)
        (decodedEnvelopeDeg N)).card ≤
        Fintype.card K * (((decodedRootPoly envsC envsK envsF kroots r).coeff e₀).natDegree +
          decodedEnvelopeDeg N) := by
      refine le_trans (le_of_eq ?_)
        (formR_event_card (K := K) (formRN K) (decodedShift envsC) (decodedBits envsC)
          (decodedMTreeOfEnvs envsK envsF kroots r) e₀ hB (decodedEnvelopeDeg N) he₀)
      unfold formRRootBad
      congr 1
    refine h1.trans (Nat.mul_le_mul_left _ ?_)
    have := natDegree_formRCounts_coeff_le (K := K) (formRN K) (decodedShift envsC)
      (decodedBits envsC) 63 (decodedShift_le envsC) e₀ (decodedMTreeOfEnvs envsK envsF kroots r)
    unfold decodedRootPoly
    omega
  · simp

/-- **The exact sum form** (Σ over roots of the guarded per-root numerators) is bounded by
`M + min(kroots, M)·(3N + 66 + (n − 1))` (`= M + kMem·(3N+129)` at `n = 64`, `kMem ≤ M`). -/
theorem decodedSum_le_uniform (envsC : Fin N → Env K) (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots : ℕ) :
    ∑ r ∈ Finset.Icc 1 kroots,
        (if 1 ≤ r ∧ r ≤ M then decompCount (decodedMTreeOfEnvs envsK envsF kroots r) +
          ((formRN K - 1) + 63 + decodedEnvelopeDeg N) else 0) ≤
      M + min kroots M * (3 * N + 66 + (formRN K - 1)) := by
  set W := (formRN K - 1) + 63 + decodedEnvelopeDeg N
  have hsplit : ∀ r ∈ Finset.Icc 1 kroots,
      (if 1 ≤ r ∧ r ≤ M then decompCount (decodedMTreeOfEnvs envsK envsF kroots r) + W else 0) ≤
        decompCount (decodedMTreeOfEnvs envsK envsF kroots r) +
          (if r ≤ M then W else 0) := by
    intro r hr
    have := (Finset.mem_Icc.mp hr).1
    split_ifs <;> omega
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  refine Nat.add_le_add (sum_decompCount_le envsK envsF kroots) ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have hc : ((Finset.Icc 1 kroots).filter fun r => r ≤ M).card ≤ min kroots M := by
    have : (Finset.Icc 1 kroots).filter (fun r => r ≤ M) = Finset.Icc 1 (min kroots M) := by
      ext r; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this]; simp
  have hW : W = 3 * N + 66 + (formRN K - 1) := by
    simp only [W, decodedEnvelopeDeg]; omega
  rw [hW]
  exact Nat.mul_le_mul_right _ hc

theorem uniform_le_numeral (n N M kroots : ℕ) :
    M + min kroots M * (3 * N + 66 + (n - 1)) ≤ formRUniformWorkloadOf n N M := by
  unfold formRUniformWorkloadOf
  have : min kroots M * (3 * N + 66 + (n - 1)) ≤ M * (3 * N + 66 + (n - 1)) :=
    Nat.mul_le_mul_right _ (min_le_right _ _)
  nlinarith

/-- **THE TRACE-UNIFORM CARD BOUND, every `K`, every env tuple, every `kroots`, no premise:**
`card ≤ |𝕂|¹⁰ · M·(3N + 67 + (formRN K − 1))`. -/
theorem decodedLambdaEventOfEnvs_card_le (envsC : Fin N → Env K) (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots : ℕ) :
    (decodedLambdaEventOfEnvs envsC envsK envsF kroots).card ≤
      Fintype.card K ^ 10 * formRUniformWorkloadOf (formRN K) N M := by
  set W := (formRN K - 1) + 63 + decodedEnvelopeDeg N
  have hB : ((Finset.Icc 1 kroots).biUnion fun r => decodedRootBad envsC envsK envsF kroots r).card
      ≤ Fintype.card K * ∑ r ∈ Finset.Icc 1 kroots,
        (if 1 ≤ r ∧ r ≤ M then decompCount (decodedMTreeOfEnvs envsK envsF kroots r) + W
          else 0) := by
    refine Finset.card_biUnion_le.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    split_ifs with h
    · have := decodedRootBad_card_le envsC envsK envsF kroots r
      simpa only [W, add_assoc] using this
    · rw [decodedRootBad_out envsC envsK envsF kroots r h]; simp
  have hS := (decodedSum_le_uniform envsC envsK envsF kroots).trans
    (uniform_le_numeral (formRN K) N M kroots)
  calc (decodedLambdaEventOfEnvs envsC envsK envsF kroots).card
      ≤ Fintype.card K ^ 9 *
          ((Finset.Icc 1 kroots).biUnion fun r => decodedRootBad envsC envsK envsF kroots r).card :=
        lift_card_le _
    _ ≤ Fintype.card K ^ 9 * (Fintype.card K * formRUniformWorkloadOf (formRN K) N M) :=
        Nat.mul_le_mul_left _ (hB.trans (Nat.mul_le_mul_left _ hS))
    _ = Fintype.card K ^ 10 * formRUniformWorkloadOf (formRN K) N M := by ring

/-- **At chip width (`formRN K ≤ 64`, i.e. `FormRWidth`'s first conjunct):
`card ≤ |𝕂|¹⁰ · memRows·(3·compRows + 130)`, every env tuple.** -/
theorem decodedLambdaEventOfEnvs_card_le_numeral (hn : formRN K ≤ 64)
    (envsC : Fin N → Env K) (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ) :
    (decodedLambdaEventOfEnvs envsC envsK envsF kroots).card ≤
      Fintype.card K ^ 10 * (M * (3 * N + 130)) :=
  (decodedLambdaEventOfEnvs_card_le envsC envsK envsF kroots).trans
    (Nat.mul_le_mul_left _ (formRUniformWorkloadOf_le_of_width hn N M))

end Event

end

end Nock.NockVMROM.Thm54.DecodedLambdaEvent
