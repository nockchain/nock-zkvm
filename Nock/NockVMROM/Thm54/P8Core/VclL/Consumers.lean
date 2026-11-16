/-
  Nock/NockVMROM/Thm54/P8Core/VclL/Consumers.lean

  **T4 (the path record's axis is exact) and T5
  (the consumer majorant at the generator's skeletons).**

  **T5**: per compute state, the VCL-L lookups (cell export / path) are the memory records of
  `Gen.lean`'s skeletons minus the inline formula opening.  Record 0 of every non-`cons` skeleton is
  `⟨formula, tail, 3⟩` with `formula = [op tail]`, `op` an atom (`genSkelOp*_record0`), and the cons
  gate with an atom head (`size = z ≠ 0`) pins the tail (`cons_right_unique`), so it needs no
  lookup.  `lookupsVCL = recordCount − inline` is
  `cons 1, s0 1, s1 0, s2 1, s3 0, s4 0, s5 1, s6 2, s7 1, s8 1, s9 2` (`lookupsVCL_table`), `≤ 2`
  at every state (`lookupsVCL_le_two`); no state has 3 (`lookupsVCL_ne_three`); over any row list
  the total is `≤ 2·|rows|` (`consumer_majorant_rows`).
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Chain
import Nock.NockVMROM.Thm54.TraceGen.Gen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock
open Nock.ComputeTable (FP State)

/-! ## T4 -/

section T4

/-- The path chip's accumulator over `ZMod q`: `acc ← 2·acc + bit`, from `1`. -/
def chainAccF (q : ℕ) (bits : List Bool) : ZMod q :=
  bits.foldl (fun a b => 2 * a + (if b then 1 else 0)) 1

theorem chainAccF_eq (q : ℕ) (bits : List Bool) : chainAccF q bits = (axisFold bits : ZMod q) := by
  induction bits using List.reverseRecOn with
  | nil => simp [chainAccF, axisFold]
  | append_singleton bs b ih =>
    rw [axisFold_append]
    unfold chainAccF at ih ⊢
    rw [List.foldl_append, ih]
    cases b <;> simp

/-- **`fold_lt_goldilocks`**: a certified chain of `< 63` edges folds below `2^63`. -/
theorem fold_lt_goldilocks (bits : List Bool) (h : bits.length < 63) : axisFold bits < 2 ^ 63 :=
  lt_of_lt_of_le (axisFold_lt bits) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `hax63`'s role: a field equality of two naturals below `q` is an equality of naturals. -/
theorem record_axis_exact {q : ℕ} (acc b : ℕ) (hacc : acc < q) (hb : b < q)
    (h : (acc : ZMod q) = (b : ZMod q)) : acc = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt hacc, Nat.mod_eq_of_lt hb] at h

/-- **T4**: the path record's `acc` equal in `ZMod q` to a formula atom `b < q` is `axisFold` of the
side bits, as a natural. -/
theorem path_record_axis_exact {q : ℕ} (hq : 2 ^ 63 < q) (bits : List Bool) (hlen : bits.length < 63)
    (b : ℕ) (hb : b < q) (h : chainAccF q bits = (b : ZMod q)) : axisFold bits = b := by
  rw [chainAccF_eq] at h
  exact record_axis_exact _ _ (lt_trans (fold_lt_goldilocks bits hlen) hq) hb h

/-- **T4 with T3**: the served noun of a chain whose accumulator matches the formula atom `b` is
`Noun.slot b root`. -/
theorem path_record_slot {q : ℕ} (hq : 2 ^ 63 < q) (bits : List Bool) (hlen : bits.length < 63)
    (b : ℕ) (hb : b < q) (h : chainAccF q bits = (b : ZMod q)) (root : Noun) :
    Noun.slot b root = chainWalk root bits := by
  rw [← path_record_axis_exact hq bits hlen b hb h, chain_slot]

end T4

/-! ## T5 -/

section T5

/-- Inline records per state: record 0 (`[op tail] @3`, `op` an atom) for every opcode row; none
for the autocons root (its head is a formula). -/
def inlineRecords : State → ℕ
  | .cons => 0
  | _ => 1

/-- **VCL-L lookups per compute state**: memory records minus the inline formula opening. -/
def lookupsVCL (s : State) : ℕ := Nock.Framework.recordCount s - inlineRecords s

theorem lookupsVCL_table :
    lookupsVCL .cons = 1 ∧ lookupsVCL .s0 = 1 ∧ lookupsVCL .s1 = 0 ∧ lookupsVCL .s2 = 1 ∧
    lookupsVCL .s3 = 0 ∧ lookupsVCL .s4 = 0 ∧ lookupsVCL .s5 = 1 ∧ lookupsVCL .s6 = 2 ∧
    lookupsVCL .s7 = 1 ∧ lookupsVCL .s8 = 1 ∧ lookupsVCL .s9 = 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **T5**: at most two VCL-L lookups per compute row, at every state. -/
theorem lookupsVCL_le_two (s : State) : lookupsVCL s ≤ 2 := by cases s <;> decide

theorem lookupsVCL_ne_three (s : State) : lookupsVCL s ≠ 3 := by cases s <;> decide

/-- The inline records are real records of the state. -/
theorem inlineRecords_le (s : State) : inlineRecords s ≤ Nock.Framework.recordCount s := by
  cases s <;> decide

/-- **The consumer majorant**: over any list of compute-row skeletons, total lookups `≤ 2·N`. -/
theorem consumer_majorant_rows (rows : List SemanticStrategy.ComputeRowSkeleton) :
    (rows.map fun r => lookupsVCL r.state).sum ≤ 2 * rows.length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := lookupsVCL_le_two r.state
    omega

/-- **The inline step is sound at the real NPR**: two cons decompositions of one parent with the
same head of nonzero size have the same tail (so `[op tail]` with `op` an atom, `size = z ≠ 0`,
needs no tail lookup). -/
theorem cons_right_unique {K : Type*} [Field K] (z : K) {a b b' : FP K} (ha : a.size ≠ 0)
    (h : FP.cons z a b = FP.cons z a b') : b = b' := by
  have h1 := congrArg FP.size h
  have h2 := congrArg FP.dyck h
  have h3 := congrArg FP.leaf h
  simp only [FP.cons] at h1 h2 h3
  have haa : a.size * a.size ≠ 0 := mul_ne_zero ha ha
  exact FP.ext (mul_left_cancel₀ ha h1) (mul_left_cancel₀ haa (by linear_combination h2))
    (mul_left_cancel₀ ha (by linear_combination h3))

theorem atomFP_size_ne_zero {K : Type*} [Field K] {z : K} (hz : z ≠ 0) (v : K) :
    (FP.atomFP z v).size ≠ 0 := hz

open TraceGen

/-! ### Record 0 at `Gen.lean`'s skeletons: the formula opened at axis `3` -/

theorem genSkelOp1_record0 (s f r h : Noun) (hi) :
    (genSkelOp1 s f r h).memoryRecord ⟨0, by decide⟩ hi = ⟨f, r, 3⟩ := by simp [genSkelOp1]
theorem genSkelOp0_record0 (s f h t r : Noun) (ax : ℕ) (hi) :
    (genSkelOp0 s f h t r ax).memoryRecord ⟨0, by decide⟩ hi = ⟨f, t, 3⟩ := by simp [genSkelOp0]
theorem genSkelOp3_record0 (s f h t cs cf cr r : Noun) (hi) :
    (genSkelOp3 s f h t cs cf cr r).memoryRecord ⟨0, by decide⟩ hi = ⟨f, t, 3⟩ := by
  simp [genSkelOp3]
theorem genSkelOp4_record0 (s f h t cs cf cr r : Noun) (hi) :
    (genSkelOp4 s f h t cs cf cr r).memoryRecord ⟨0, by decide⟩ hi = ⟨f, t, 3⟩ := by
  simp [genSkelOp4]
theorem genSkelOp2_record0 (s f h ft fth ftt a b r : Noun) (hi) :
    (genSkelOp2 s f h ft fth ftt a b r).memoryRecord ⟨0, by decide⟩ hi = ⟨f, ft, 3⟩ := by
  simp [genSkelOp2]
theorem genSkelOp5_record0 (s f h ft fth ftt a b r : Noun) (hi) :
    (genSkelOp5 s f h ft fth ftt a b r).memoryRecord ⟨0, by decide⟩ hi = ⟨f, ft, 3⟩ := by
  simp [genSkelOp5]
theorem genSkelOp7_record0 (s f h ft fth ftt sb r : Noun) (hi) :
    (genSkelOp7 s f h ft fth ftt sb r).memoryRecord ⟨0, by decide⟩ hi = ⟨f, ft, 3⟩ := by
  simp [genSkelOp7]
theorem genSkelOp8_record0 (s f h ft fth ftt sb r : Noun) (hi) :
    (genSkelOp8 s f h ft fth ftt sb r).memoryRecord ⟨0, by decide⟩ hi = ⟨f, ft, 3⟩ := by
  simp [genSkelOp8]
theorem genSkelOp9_record0 (s f h ft fth ftt core arm r : Noun) (ax : ℕ) (hi) :
    (genSkelOp9 s f h ft fth ftt core arm r ax).memoryRecord ⟨0, by decide⟩ hi = ⟨f, ft, 3⟩ := by
  simp [genSkelOp9]
theorem genSkelOp6_record0 (s f h ft fth ftt ftth fttt c tk r : Noun) (hi) :
    (genSkelOp6 s f h ft fth ftt ftth fttt c tk r).memoryRecord ⟨0, by decide⟩ hi = ⟨f, ft, 3⟩ := by
  simp [genSkelOp6]
/-- The autocons root's single record opens `[leftF rightF]` (head a formula): a lookup. -/
theorem genSkelCons_record0 (s lf rf lr rr : Noun) (hi) :
    (genSkelCons s lf rf lr rr).memoryRecord ⟨0, by decide⟩ hi = ⟨.cell lf rf, rf, 3⟩ := by
  simp [genSkelCons]

/-- The skeletons' states (so `lookupsVCL` reads the generator's record count). -/
theorem genSkel_states (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ n₁₁ : Noun) (ax : ℕ) :
    (genSkelOp0 n₁ n₂ n₃ n₄ n₅ ax).state = .s0 ∧ (genSkelOp1 n₁ n₂ n₃ n₄).state = .s1 ∧
    (genSkelOp2 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉).state = .s2 ∧
    (genSkelOp3 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈).state = .s3 ∧
    (genSkelOp4 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈).state = .s4 ∧
    (genSkelOp5 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉).state = .s5 ∧
    (genSkelOp6 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ n₁₁).state = .s6 ∧
    (genSkelOp7 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈).state = .s7 ∧
    (genSkelOp8 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈).state = .s8 ∧
    (genSkelOp9 n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ ax).state = .s9 ∧
    (genSkelCons n₁ n₂ n₃ n₄ n₅).state = .cons :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end T5

end Nock.NockVMROM.Thm54.VclL
