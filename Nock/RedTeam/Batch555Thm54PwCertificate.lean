/-
  Nock/RedTeam/Batch555Thm54PwCertificate.lean

  * **A. Gadgets on committed bits.**  `gadget_two_gates`: the split `H = Π_{k<3}(1 + m_k(x^{2^k}−1))`,
    `T = H·Π_{3≤k<6}(…)` with boolean `m_k` pins `T = x^{Σ m_k 2^k}` — one theorem for
    `x = λ` (𝕂 column `T`) and `x = 2` (base column `t`).  `six_bits_gate`: `p = m₀m₁m₂`,
    `p·m₃m₄m₅ = 0` ⇔ some bit is `0` ⇔ `m ≠ 63`, so `m ≤ 62`.
  * **B. The integer certificate.**  `cert m c = 2^m + Σ_{j≤m} c_j 2^{m−j}`; `cert_bounds`
    (`2^m ≤ cert < 2^{m+1}`), `cert_inj` (unique bits), `cert_mod_unique`: the residue determines
    `(m, c)` when `2^63 < p` and `m ≤ 62`.  So the design as briefed is sound only with `2^63 < p`.
  * **C. The deployed record slots.**  `computeTraceSubst` puts the compute-side records IN-GATE: `mr₁.axis = Const 3` (role `73`), `mr₂.axis = op₀·f_t.leaf +
    (op₂+op₅+op₆+op₇+op₈+op₉)·2` (role `81`), `mr₃.axis = op₆·2 + op₉·f_th.leaf` (role `89`),
    each of `Expr.degree ≤ 2`; the memory-side record field is a full 𝕂 role
    (`memorySubst 29 = Var 25`).  So `(T, C)` replace an in-gate slot on the compute chip (no new
    record columns) and one 𝕂 role on the memory chip (`+ e`, not `+ 2e − 1`).
  * **D. `d = 4` holds.
  * **E. Widths**: compute `202 + 77 = 279`, memory `200 + 3 = 203`.
-/
import Nock.RedTeam.Batch554Thm54PwFunctional
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch555

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.RedTeam.Batch554
open Polynomial

/-! ## A. The gadgets on committed boolean columns -/

section Gadgets

variable {K : Type*} [Field K] [DecidableEq K]

theorem factor_pow (y b : K) (hb : b = 0 ∨ b = 1) :
    1 + b * (y - 1) = y ^ (if b = 1 then 1 else 0) := by
  rcases hb with rfl | rfl
  · simp
  · simp

/-- **The split power gadget, as two gates**: `H = Π_{k<3}(1 + m_k(x^{2^k} − 1))` (degree 3) and
`T = H·Π_{3≤k<6}(1 + m_k(x^{2^k} − 1))` (degree 4) with boolean `m_k` force `T = x^m`,
`m = Σ_k m_k 2^k`.  At `x = λ` this is the 𝕂 column `T`; at `x = 2` the base column `t`. -/
theorem gadget_two_gates (x : K) (m : ℕ → K) (hb : ∀ k < 6, m k = 0 ∨ m k = 1) (H T : K)
    (hH : H = ∏ k ∈ Finset.range 3, (1 + m k * (x ^ (2 ^ k) - 1)))
    (hT : T = H * ∏ k ∈ Finset.Ico 3 6, (1 + m k * (x ^ (2 ^ k) - 1))) :
    T = x ^ (∑ k ∈ Finset.range 6, if m k = 1 then 2 ^ k else 0) := by
  rw [hT, hH, Finset.prod_range_mul_prod_Ico _ (by norm_num : 3 ≤ 6)]
  have hf : ∀ k ∈ Finset.range 6,
      1 + m k * (x ^ (2 ^ k) - 1) = x ^ (if m k = 1 then 2 ^ k else 0) := by
    intro k hk
    rw [factor_pow (x ^ (2 ^ k)) (m k) (hb k (Finset.mem_range.mp hk))]
    split_ifs <;> simp [pow_mul]
  rw [Finset.prod_congr rfl hf, Finset.prod_pow_eq_pow_sum]

theorem six_bits_sum_le (m : ℕ → K) :
    (∑ k ∈ Finset.range 6, if m k = 1 then 2 ^ k else 0) ≤ 63 := by
  calc (∑ k ∈ Finset.range 6, if m k = 1 then 2 ^ k else 0)
      ≤ ∑ k ∈ Finset.range 6, 2 ^ k :=
        Finset.sum_le_sum fun k _ => by split_ifs <;> simp
    _ = 63 := by simp [Finset.sum_range_succ]

/-- **The `m ≠ 63` gate**: `p = m₀m₁m₂`, `p·m₃m₄m₅ = 0` on boolean bits forces some bit to `0`,
hence `m < 63`, i.e. `m ≤ 62`. -/
theorem six_bits_gate (m : ℕ → K) (hb : ∀ k < 6, m k = 0 ∨ m k = 1) (p : K)
    (hp : p = m 0 * m 1 * m 2) (hg : p * m 3 * m 4 * m 5 = 0) :
    (∑ k ∈ Finset.range 6, if m k = 1 then 2 ^ k else 0) ≤ 62 := by
  have hzero : ∃ j < 6, m j = 0 := by
    rw [hp] at hg
    simp only [mul_eq_zero] at hg
    rcases hg with ((((h | h) | h) | h) | h) | h
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
    · exact ⟨3, by norm_num, h⟩
    · exact ⟨4, by norm_num, h⟩
    · exact ⟨5, by norm_num, h⟩
  obtain ⟨j, hj, hmj⟩ := hzero
  have hlt : (∑ k ∈ Finset.range 6, if m k = 1 then 2 ^ k else 0)
      < ∑ k ∈ Finset.range 6, 2 ^ k := by
    apply Finset.sum_lt_sum
    · intro k _; split_ifs <;> simp
    · refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
      rw [hmj, if_neg zero_ne_one]
      exact pow_pos (by norm_num : (0 : ℕ) < 2) j
  have : ∑ k ∈ Finset.range 6, (2 : ℕ) ^ k = 63 := by simp [Finset.sum_range_succ]
  omega

/-- Conversely all six bits `1` (`m = 63`) violates the gate: it is exactly `m ≠ 63`. -/
theorem six_bits_gate_tight (m : ℕ → K) (h1 : ∀ k < 6, m k = 1) :
    (m 0 * m 1 * m 2) * m 3 * m 4 * m 5 ≠ 0 := by
  simp [h1 0 (by norm_num), h1 1 (by norm_num), h1 2 (by norm_num), h1 3 (by norm_num),
    h1 4 (by norm_num), h1 5 (by norm_num)]

end Gadgets

/-! ## B. The integer certificate and the prime-size condition -/

def cert (m : ℕ) (c : ℕ → Bool) : ℕ :=
  2 ^ m + ∑ j ∈ Finset.range m, (c (j + 1)).toNat * 2 ^ (m - (j + 1))

theorem cert_zero (c : ℕ → Bool) : cert 0 c = 1 := by simp [cert]

theorem cert_succ (m : ℕ) (c : ℕ → Bool) :
    cert (m + 1) c = 2 * cert m c + (c (m + 1)).toNat := by
  unfold cert
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, pow_succ, mul_add, Finset.mul_sum]
  have : ∀ j ∈ Finset.range m,
      (c (j + 1)).toNat * 2 ^ (m + 1 - (j + 1)) = 2 * ((c (j + 1)).toNat * 2 ^ (m - (j + 1))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show m + 1 - (j + 1) = (m - (j + 1)) + 1 by omega, pow_succ]; ring
  rw [Finset.sum_congr rfl this]; ring

/-- `2^m ≤ cert m c < 2^{m+1}`: the top bit is `2^m`, so `m ≤ 62` keeps it below `2^63`. -/
theorem cert_bounds (m : ℕ) (c : ℕ → Bool) : 2 ^ m ≤ cert m c ∧ cert m c < 2 ^ (m + 1) := by
  induction m with
  | zero => simp [cert_zero]
  | succ m ih =>
      rw [cert_succ]
      have := Bool.toNat_le (c (m + 1))
      constructor
      · rw [pow_succ]; omega
      · rw [pow_succ, pow_succ]; omega

/-- **The certificate is unique as an integer**: equal values force equal `m` and equal bits. -/
theorem cert_inj (m : ℕ) : ∀ (m' : ℕ) (c c' : ℕ → Bool), cert m c = cert m' c' →
    m = m' ∧ ∀ j, 1 ≤ j → j ≤ m → c j = c' j := by
  induction m with
  | zero =>
      intro m' c c' h
      cases m' with
      | zero => exact ⟨rfl, fun j h1 h2 => by omega⟩
      | succ m' =>
          exfalso
          rw [cert_zero, cert_succ] at h
          have := (cert_bounds m' c').1
          have := Nat.one_le_two_pow (n := m')
          omega
  | succ m ih =>
      intro m' c c' h
      cases m' with
      | zero =>
          exfalso
          rw [cert_zero, cert_succ] at h
          have := (cert_bounds m c).1
          have := Nat.one_le_two_pow (n := m)
          omega
      | succ m' =>
          rw [cert_succ, cert_succ] at h
          have hb : (c (m + 1)).toNat = (c' (m' + 1)).toNat := by
            have h1 := Bool.toNat_le (c (m + 1))
            have h2 := Bool.toNat_le (c' (m' + 1))
            omega
          have hrest : cert m c = cert m' c' := by omega
          obtain ⟨hm, hc⟩ := ih m' c c' hrest
          subst hm
          refine ⟨rfl, fun j h1 h2 => ?_⟩
          rcases Nat.lt_or_ge j (m + 1) with hj | hj
          · exact hc j h1 (by omega)
          · have hj' : j = m + 1 := by omega
            subst hj'
            cases hx : c (m + 1) <;> cases hy : c' (m + 1) <;> simp_all

/-- **Uniqueness mod `p` needs `2^63 < p`**: with `m, m' ≤ 62` the residue of `cert` in
`ZMod p` determines `(m, c)`. -/
theorem cert_mod_unique (p : ℕ) (hp : 2 ^ 63 < p) (m m' : ℕ) (c c' : ℕ → Bool)
    (hm : m ≤ 62) (hm' : m' ≤ 62)
    (h : ((cert m c : ℕ) : ZMod p) = ((cert m' c' : ℕ) : ZMod p)) :
    m = m' ∧ ∀ j, 1 ≤ j → j ≤ m → c j = c' j := by
  haveI : NeZero p := ⟨by omega⟩
  have h1 : cert m c < p := by
    have := (cert_bounds m c).2
    have : 2 ^ (m + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : cert m' c' < p := by
    have := (cert_bounds m' c').2
    have : 2 ^ (m' + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  exact cert_inj m m' c c' this

/-- Certificate of axis `3`: `m = 1`, `c_1 = 1`. -/
def c3 : ℕ → Bool := fun j => j = 1
/-- Certificate of axis `34 = 100010₂`: `m = 5`, `c_4 = 1`, all other bits `0`. -/
def c34 : ℕ → Bool := fun j => j = 4

theorem cert_c3 : cert 1 c3 = 3 := by decide
theorem cert_c34 : cert 5 c34 = 34 := by decide

/-- **At `p = 31` the two certificates have the same residue**: `34 ≡ 3 (mod 31)`.  `31` is a
prime `nockCompiles_zmod`'s floor `hp : 25 ≤ p` allows. -/
theorem cert_ambiguous_31 :
    ((cert 1 c3 : ℕ) : ZMod 31) = ((cert 5 c34 : ℕ) : ZMod 31) ∧ (25 : ℕ) ≤ 31 := by
  rw [cert_c3, cert_c34]; exact ⟨by decide, by norm_num⟩

/-- The brief's base-field gate `axis = t·Σ_j c_j 2^{−j}` (`c_0 = 1`, `t = 2^m`) at `p = 31` with
`m = 5`, `c_4 = 1`: it accepts the committed axis atom `3`. -/
theorem brief_gate_accepts_34_at_31 :
    (2 : ZMod 31) ^ 5 * (1 + ((2 : ZMod 31)⁻¹) ^ 4) = 3 := by
  have hu : IsUnit (2 : ZMod 31) := isUnit_iff_exists_inv.mpr ⟨16, by decide⟩
  have h1 : (2 : ZMod 31) * 2⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  have h2 : (2 : ZMod 31)⁻¹ = 16 := by
    calc (2 : ZMod 31)⁻¹ = 2⁻¹ * (2 * 16) := by
          rw [show (2 : ZMod 31) * 16 = 1 by decide, mul_one]
      _ = (2 * 2⁻¹) * 16 := by ring
      _ = 16 := by rw [h1, one_mul]
  rw [h2]
  decide

/-- The relative path the memory side then demands: `[L, L, L, R, L]` (`34 = 1·00010₂`). -/
theorem bitsOf_c34 : bitsOf 5 c34 = [false, false, false, true, false] := by decide

/-- **The memory-side polynomial is identically zero** for the verify at `[L,L,L,R,L]` under the
read at any `r`, with the `(5, c34)` certificate — no event, every `λ`, every `α`. -/
theorem memory_side_zero_at_34 {K : Type*} [Field K] (r : List Bool) :
    bracket (K := K) 62 5 c34 (r ++ [false, false, false, true, false]) r = 0 := by
  rw [← bitsOf_c34]
  exact bracket_honest 62 5 c34 r (by norm_num) (fun j hj _ => by
    simp [c34]; omega)

/-- The forged claim is false: on `S = [[[[0 [9 0]] 0] 0] 7]`, `/[3 S] = 7 ≠ 9 = /[34 S]`. -/
def S34 : Noun :=
  .cell (.cell (.cell (.cell (.atom 0) (.cell (.atom 9) (.atom 0))) (.atom 0)) (.atom 0))
    (.atom 7)

theorem slot_3_ne_34 :
    Noun.slot 3 S34 = some (.atom 7) ∧ Noun.slot 34 S34 = some (.atom 9)
      ∧ Noun.slot 3 S34 ≠ Noun.slot 34 S34 := by
  refine ⟨by simp [S34, Noun.slot], by simp [S34, Noun.slot], ?_⟩
  simp [S34, Noun.slot]

/-- At Goldilocks the window is fine: `2^63 < p` (`Nock/Field.lean:37`). -/
theorem goldilocks_window : 2 ^ 63 < Nock.Field.p := by norm_num [Nock.Field.p]

/-! ## C. The deployed record slots (`OptimizedComputeSubstitution.computeTraceSubst`) -/

section Slots

open OptimizedComputeSubstitution

/-- `mr₁.axis` (role `73`) is the in-gate constant `3`: a constant-axis record
whose `(T, C)` become in-gate constants; the row's certificate columns are not read. -/
theorem mr1_axis_slot : computeTraceSubst .traceCur 73 = .Const 3 := rfl

/-- `mr₂.axis` (role `81`) is `op₀·f_t.leaf + (op₂+op₅+op₆+op₇+op₈+op₉)·2` (`:1751`, `:1856`):
the variable axis is selected in-gate by `op₀`, the constant `2` by the six-opcode group. -/
theorem mr2_axis_slot :
    computeTraceSubst .traceCur 81
      = .Add (.Mul (.Var .traceCur 0) (decFP .traceCur 1 2))
          (.Mul (mr2Group .traceCur) (.Const 2)) := rfl

/-- `mr₃.axis` (role `89`) is `op₆·2 + op₉·f_th.leaf` (`:1738`, `:1877`, `:1881`). -/
theorem mr3_axis_slot :
    computeTraceSubst .traceCur 89
      = .Add (.Mul (.Var .traceCur 6) (.Const 2))
          (.Mul (.Var .traceCur 9) (decFP .traceCur 2 2)) := rfl

/-- The deployed axis slots are in-gate expressions of `Expr.degree ≤ 2`, so replacing them by
`(op₀·T + group·λ, op₀·C' + group·λ^{62})` keeps the record RLC at the same degree. -/
theorem deployed_axis_slot_degrees :
    (computeTraceSubst .traceCur 73).degree = 0
    ∧ (computeTraceSubst .traceCur 81).degree = 2
    ∧ (computeTraceSubst .traceCur 89).degree = 2 := by
  refine ⟨rfl, rfl, rfl⟩

/-- Slot `0` (`mr₁`) is active on every row (`sampledActive 0 = 1`): the constant record
`(λ, λ^{62} + λ^{61})` is emitted by every row, padding rows included. -/
theorem mr1_always_active : sampledActive .traceCur 0 = .Const 1 := rfl

/-- The `(T, C)` slots of the design, in-gate, at the same positions (`λ` at a new challenge slot
`10`; `T` a 𝕂 column at a placeholder role `200`; `c_j` base columns at placeholder roles
`100 + j`). -/
def lam : Expr := .Var .challenge 10
def Tcol : Expr := .Var .traceCur 200
def Clin : Expr :=
  (List.range 62).foldr
    (fun j acc => .Add (.Mul (.Pow lam (62 - (j + 1))) (.Var .traceCur (100 + j))) acc)
    (.Pow lam 62)
def mr2_T_slot : Expr := .Add (.Mul (.Var .traceCur 0) Tcol) (.Mul (mr2Group .traceCur) lam)
def mr2_C_slot : Expr :=
  .Add (.Mul (.Var .traceCur 0) Clin) (.Mul (mr2Group .traceCur) (.Pow lam 62))

set_option maxRecDepth 16384 in
theorem design_record_slot_degrees :
    Clin.degree = 1 ∧ mr2_T_slot.degree = 2 ∧ mr2_C_slot.degree = 2 := by
  refine ⟨rfl, rfl, rfl⟩

end Slots

/-- The memory-side record's axis field is a full 𝕂 role: memory-table role `29` (`NockVM.encRec`
position `6`) is 𝕂 role `25` under `memorySubst`, so `axis ↦ (T, C)` costs one 𝕂 role (`+ e`). -/
theorem memory_axis_is_K_role :
    OptimizedMemoryGateBasis.memorySubst .traceCur 29 = .Var .traceCur 25 := rfl

/-! ## D. Degrees of the design's gates at the tree's degree functions -/

section Degrees

variable {F : Type} [Field F]

open OptimizedMemoryGateBasis (bcur bbool)

/-- Placeholder roles: `counts_P` `4`, `pw_P` `3` (the paper's label slots, `MemoryWalkLabel.
labelCoordAt`), `counts_L`/`pw_L`/`counts_R`/`pw_R` at the child cells, record `T`/`C`/`ts` at the
record roles.  Degree does not depend on the indices. -/
def cP : MixedExpr F := .Var .traceCur 4
def pP : MixedExpr F := .Var .traceCur 3
def cL : MixedExpr F := .Var .traceCur 9
def pL : MixedExpr F := .Var .traceCur 8
def cR : MixedExpr F := .Var .traceCur 15
def pR : MixedExpr F := .Var .traceCur 14
def recT : MixedExpr F := .Var .traceCur 25
def recC : MixedExpr F := .Var .traceCur 63
def recTs : MixedExpr F := .Var .traceCur 26
def lamM : MixedExpr F := .Var .challenge 10
def lam62 : MixedExpr F := .Pow lamM 62

/-- `decompose`: `op₀·(counts_P − counts_L − counts_R − (λ−1)(pw_L + pw_R) − pw_R)`. -/
def decomposeCounts : MixedExpr F :=
  .Scale (bcur 0)
    (.Sub (.Sub (.Sub (.Sub cP cL) cR) (.Mul (.Sub lamM (.Const 1)) (.Add pL pR))) pR)
/-- `decompose`: `op₀·(pw_P − λ(pw_L + pw_R))`. -/
def decomposePw : MixedExpr F := .Scale (bcur 0) (.Sub pP (.Mul lamM (.Add pL pR)))
/-- `halt`: `op₁·counts_P`, `op₁·pw_P`. -/
def haltCounts : MixedExpr F := .Scale (bcur 1) cP
def haltPw : MixedExpr F := .Scale (bcur 1) pP
/-- `read_root`: `op₂·(counts_P − counts_L + T·C'·ts)` — **degree 4**. -/
def readCounts : MixedExpr F :=
  .Scale (bcur 2) (.Sub cP (.Sub cL (.Mul (.Mul recT recC) recTs)))
/-- `read_root`: `op₂·(pw_P − pw_L + λ^{62}·T·ts)` — degree 3. -/
def readPw : MixedExpr F :=
  .Scale (bcur 2) (.Sub pP (.Sub pL (.Mul lam62 (.Mul recT recTs))))
/-- `verify_child`: `op₃·(counts_P − counts_L − λ^{62}·ts)`, `op₃·(pw_P − pw_L − λ^{62}·ts)`. -/
def verifyCounts : MixedExpr F := .Scale (bcur 3) (.Sub cP (.Add cL (.Mul lam62 recTs)))
def verifyPw : MixedExpr F := .Scale (bcur 3) (.Sub pP (.Add pL (.Mul lam62 recTs)))
def rootMaskPw : MixedExpr F := .Scale OptimizedMemoryGateBasis.rootMask pP

theorem memory_gate_degrees :
    (decomposeCounts (F := F)).degree = 2 ∧ (decomposePw (F := F)).degree = 2
    ∧ (haltCounts (F := F)).degree = 2 ∧ (haltPw (F := F)).degree = 2
    ∧ (readCounts (F := F)).degree = 4 ∧ (readPw (F := F)).degree = 3
    ∧ (verifyCounts (F := F)).degree = 2 ∧ (verifyPw (F := F)).degree = 2
    ∧ (rootMaskPw (F := F)).degree = 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Compute-side base columns: bits `c_j` at `100 + j`, `m_k` at `170 + k`, `h`, `t`, `p` at
`180`, `181`, `182`; 𝕂 columns `H`, `T`; `axisSel = op₀ + op₉`; the axis atom
`op₀·f_t.leaf + op₉·f_th.leaf`. -/
def cbit (j : ℕ) : CoeffExpr F := bcur (100 + j)
def mbit (k : ℕ) : CoeffExpr F := bcur (170 + k)
def hcol : CoeffExpr F := bcur 180
def tcol : CoeffExpr F := bcur 181
def pcol : CoeffExpr F := bcur 182
def Hcol : MixedExpr F := .Var .traceCur 201
def TcolM : MixedExpr F := .Var .traceCur 200

/-- `1 + m_k(λ^{2^k} − 1)` — degree 1. -/
def facK (k : ℕ) : MixedExpr F :=
  .Add (.Const 1) (.Scale (mbit k) (.Sub (.Pow lamM (2 ^ k)) (.Const 1)))
/-- `1 + m_k(2^{2^k} − 1)` in the base field — degree 1. -/
def facF (k : ℕ) : CoeffExpr F :=
  .add (.const 1) (.mul (mbit k) (.const ((2 : F) ^ (2 ^ k) - 1)))

def bitBool (j : ℕ) : CoeffExpr F := bbool (cbit j)
def mBool (k : ℕ) : CoeffExpr F := bbool (mbit k)
/-- `H − Π_{k<3} fac_k` — degree 3. -/
def Hgate : MixedExpr F := .Sub Hcol (.Mul (.Mul (facK 0) (facK 1)) (facK 2))
/-- `T − H·Π_{3≤k<6} fac_k` — degree 4. -/
def Tgate : MixedExpr F := .Sub TcolM (.Mul Hcol (.Mul (.Mul (facK 3) (facK 4)) (facK 5)))
/-- Base-field twins `h − Π_{k<3}`, `t − h·Π_{3≤k<6}` — degrees 3, 4. -/
def hgate : CoeffExpr F := .sub hcol (.mul (.mul (facF 0) (facF 1)) (facF 2))
def tgate : CoeffExpr F := .sub tcol (.mul hcol (.mul (.mul (facF 3) (facF 4)) (facF 5)))
/-- `p − m₀m₁m₂` (3) and `p·m₃m₄m₅` (4). -/
def pgate : CoeffExpr F := .sub pcol (.mul (.mul (mbit 0) (mbit 1)) (mbit 2))
def m63gate : CoeffExpr F := .mul (.mul (.mul pcol (mbit 3)) (mbit 4)) (mbit 5)
/-- `Σ_{j=1}^{62} c_j·2^{−j}` — base-field constants ARE expressible (`CoeffExpr.const : F`). -/
def csumL (L : List ℕ) : CoeffExpr F :=
  L.foldr (fun j acc => .add (.mul (.const ((2 : F)⁻¹ ^ (j + 1))) (cbit j)) acc) (.const 1)
def csum : CoeffExpr F := csumL (List.range 62)

theorem csumL_degree : ∀ L : List ℕ, (csumL (F := F) L).degree = if L = [] then 0 else 1 := by
  intro L
  induction L with
  | nil => rfl
  | cons j L ih =>
      simp only [csumL, List.foldr_cons] at ih ⊢
      rw [show (CoeffExpr.add (.mul (.const ((2 : F)⁻¹ ^ (j + 1))) (cbit j))
          (List.foldr (fun j acc => CoeffExpr.add (.mul (.const ((2 : F)⁻¹ ^ (j + 1))) (cbit j)) acc)
            (.const 1) L)).degree
          = max ((CoeffExpr.mul (.const ((2 : F)⁻¹ ^ (j + 1))) (cbit j)).degree)
              (List.foldr (fun j acc => CoeffExpr.add (.mul (.const ((2 : F)⁻¹ ^ (j + 1))) (cbit j)) acc)
                (.const 1) L).degree from rfl, ih, if_neg (List.cons_ne_nil j L)]
      split_ifs <;> rfl

theorem csum_degree : (csum (F := F)).degree = 1 := by
  rw [csum, csumL_degree, if_neg (by decide)]
/-- `op₀·(f_t.leaf − t·csum) + op₉·(f_th.leaf − t·csum)` — degree 3. -/
def axisGate : CoeffExpr F :=
  .add (.mul (bcur 0) (.sub (bcur 60) (.mul tcol csum)))
    (.mul (bcur 9) (.sub (bcur 61) (.mul tcol csum)))

set_option maxRecDepth 16384 in
theorem compute_gate_degrees :
    (bitBool (F := F) 7).degree = 2 ∧ (mBool (F := F) 2).degree = 2
    ∧ (Hgate (F := F)).degree = 3 ∧ (Tgate (F := F)).degree = 4
    ∧ (hgate (F := F)).degree = 3 ∧ (tgate (F := F)).degree = 4
    ∧ (pgate (F := F)).degree = 3 ∧ (m63gate (F := F)).degree = 4
    ∧ (csum (F := F)).degree = 1 ∧ (axisGate (F := F)).degree = 3 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, csum_degree, ?_⟩
  show max ((CoeffExpr.mul (bcur 0) (.sub (bcur 60) (.mul tcol csum))).degree)
      ((CoeffExpr.mul (bcur 9) (.sub (bcur 61) (.mul tcol csum))).degree) = 3
  simp only [CoeffExpr.degree, csum_degree, bcur, tcol]
  decide

end Degrees

/-! ## E. Widths -/

/-- New compute columns at extension degree `e`: `c_1..c_62`, `m_0..m_5`, `H`, `T` (𝕂), `h`, `t`,
`p` (𝔽) — `71 + 2e`; `77` at `e = 3`, so `202 → 279`. -/
def certificateColumns (e : ℕ) : ℕ := 62 + 6 + e + e + 1 + 1 + 1

theorem certificateColumns_eq (e : ℕ) : certificateColumns e = 71 + 2 * e := by
  unfold certificateColumns; ring

theorem compute_width : 202 + certificateColumns 3 = 279 := by decide

/-- Memory: the record's axis 𝕂 role becomes two 𝕂 roles `(T, C)`: `+ e = + 3`, `200 → 203`
(the first pass's `205` assumed a one-column base-field axis the deployed layout does not have,
`memory_axis_is_K_role`). -/
theorem memory_width : 200 + 3 = 203 := by decide

end Nock.RedTeam.Batch555

#print axioms Nock.RedTeam.Batch555.gadget_two_gates
#print axioms Nock.RedTeam.Batch555.six_bits_gate
#print axioms Nock.RedTeam.Batch555.cert_inj
#print axioms Nock.RedTeam.Batch555.cert_mod_unique
#print axioms Nock.RedTeam.Batch555.cert_ambiguous_31
#print axioms Nock.RedTeam.Batch555.brief_gate_accepts_34_at_31
#print axioms Nock.RedTeam.Batch555.memory_side_zero_at_34
#print axioms Nock.RedTeam.Batch555.slot_3_ne_34
#print axioms Nock.RedTeam.Batch555.mr2_axis_slot
#print axioms Nock.RedTeam.Batch555.memory_gate_degrees
#print axioms Nock.RedTeam.Batch555.compute_gate_degrees
