/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ASplitH.lean

The honest trace is a closed form over a list of field-axis values `vS : Fin n → ℕ` (`2^32 ≤ vS i < 2^64`) with
  multiplicities `mS : Fin n → ℕ` (the pattern is `Nock/Jet/ChipJ8THonestRAP.lean`):
  * base columns `0 .. 71` (`SplitChipJ9` §1): the two row masks, `ctr = i`, `sid = nA + i`,
    `hi = vS i / 2^32`, `lo = vS i % 2^32`, the 64 bits `testBit (vS i) j`, `invHi = hi⁻¹`, `mult = mS i`;
  * `𝕂′` roles (round 2): `inv2 = den(key2)⁻¹`, `inv3 = den(key3)⁻¹` at the handle coins, and `acc` the
    INCLUSIVE prefix sum of `mS · (inv2 + inv3)`.

  **`splitChipJ9_honest_sat`**: `RAP.SatisfiesWithPreprocessing (splitChipJ9 …) (polySC …)` under
  `2^32 < p`, `hv`, the orbit facts, the two completeness bad events `hd2`, `hd3` (the key denominators at the
  handle coins are nonzero at every row) and the public `(pub₀, pub₁) = Σ mS · (den₂⁻¹ + den₃⁻¹)`.
  **`splitProvs_honest`**: the provided records of the honest trace.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. ℕ-level bit decomposition -/

theorem nat_low_bits (v : ℕ) : ∀ m : ℕ,
    v % 2 ^ m = ∑ i ∈ Finset.range m, 2 ^ i * (if v.testBit i then 1 else 0)
  | 0 => by simp [Nat.mod_one]
  | m + 1 => by
    rw [Finset.sum_range_succ, ← nat_low_bits v m, Nat.mod_pow_succ]
    have hb : v / 2 ^ m % 2 = 0 ∨ v / 2 ^ m % 2 = 1 := by omega
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases hb with h | h <;> simp [h]

theorem nat_hi_bits (v : ℕ) (hv : v < 2 ^ 64) :
    v / 2 ^ 32 = ∑ i ∈ Finset.range 32, 2 ^ i * (if v.testBit (32 + i) then 1 else 0) := by
  have h1 : v / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc v < 2 ^ 64 := hv
      _ = 2 ^ 32 * 2 ^ 32 := by norm_num
  have := nat_low_bits (v / 2 ^ 32) 32
  rw [Nat.mod_eq_of_lt h1] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_div_two_pow, add_comm i 32]

section Zmod
variable {p : ℕ} [Fact p.Prime]

/-- Bit `j` of `v` as a field element. -/
def bitV (v j : ℕ) : ZMod p := if v.testBit j then 1 else 0

theorem cast_lo (v : ℕ) : ((v % 2 ^ 32 : ℕ) : ZMod p) = ∑ i ∈ Finset.range 32, (2 : ZMod p) ^ i * bitV v i := by
  rw [nat_low_bits v 32]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold bitV
  split_ifs <;> simp

theorem cast_hi (v : ℕ) (hv : v < 2 ^ 64) :
    ((v / 2 ^ 32 : ℕ) : ZMod p) = ∑ i ∈ Finset.range 32, (2 : ZMod p) ^ i * bitV v (32 + i) := by
  rw [nat_hi_bits v hv]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold bitV
  split_ifs <;> simp

theorem hi_ne_zero (hp : 2 ^ 32 < p) (v : ℕ) (hv : 2 ^ 32 ≤ v ∧ v < 2 ^ 64) :
    ((v / 2 ^ 32 : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have hpos : 0 < v / 2 ^ 32 := Nat.div_pos hv.1 (by positivity)
  have hle := Nat.le_of_dvd hpos hd
  have h2 : v / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc v < 2 ^ 64 := hv.2
      _ = 2 ^ 32 * 2 ^ 32 := by norm_num
  exact lt_asymm hp (lt_of_le_of_lt hle h2)

end Zmod

/-! ## 2. The honest `𝕂′` values -/

section Values
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (chals : ℕ → K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The key denominator in closed form** at the handle coins `γ′ = (χ₃₃, χ₃₅)`, `ρ′ = (χ₃₄, χ₃₆)`:
`ρ′ + Σ_{c < 4} γ′^c · lift(v_c)`. -/
def dKey4 (a b c d : ZMod p) : 𝕂′ :=
  Quad.mk _ (chals 34) (chals 36) +
    (liftQ δ a + (Quad.mk _ (chals 33) (chals 35)) * liftQ δ b +
      (Quad.mk _ (chals 33) (chals 35)) ^ 2 * liftQ δ c + (Quad.mk _ (chals 33) (chals 35)) ^ 3 * liftQ δ d)

variable (nA : ℕ) {n : ℕ} (vS mS : Fin n → ℕ)

/-- The denominator of the record `(id, 2, 0, lo)` at row `i`. -/
def d2 (i : Fin n) : 𝕂′ :=
  dKey4 δ chals ((nA + (i : ℕ) : ℕ) : ZMod p) 2 0 ((vS i % 2 ^ 32 : ℕ) : ZMod p)

/-- The denominator of the record `(id, 3, 0, hi)` at row `i`. -/
def d3 (i : Fin n) : 𝕂′ :=
  dKey4 δ chals ((nA + (i : ℕ) : ℕ) : ZMod p) 3 0 ((vS i / 2 ^ 32 : ℕ) : ZMod p)

/-- The row term `mS · (inv2 + inv3)`. -/
def rowT (i : Fin n) : 𝕂′ := liftQ δ ((mS i : ℕ) : ZMod p) * ((d2 δ chals nA vS i)⁻¹ + (d3 δ chals nA vS i)⁻¹)

end Values

/-! ## 3. The honest trace -/

section Trace
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (nA : ℕ) (b : Basis (Fin 3) (ZMod p) K) (chals : ℕ → K)
  {n : ℕ} (vS mS : Fin n → ℕ)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

def tN (i : ℕ) : 𝕂′ := if h : i < n then rowT δ chals nA vS mS ⟨i, h⟩ else 0

/-- **The accumulator**: the inclusive prefix sum of the row terms. -/
def accS (i : ℕ) : 𝕂′ := ∑ j ∈ Finset.range (i + 1), tN δ nA chals vS mS j

/-- The three `𝕂′` columns `inv2`, `inv3`, `acc` of row `i`. -/
def qv (s : ℕ) (i : Fin n) : 𝕂′ :=
  match s with
  | 0 => (d2 δ chals nA vS i)⁻¹
  | 1 => (d3 δ chals nA vS i)⁻¹
  | 2 => accS δ nA chals vS mS i
  | _ => 0

/-- `𝕂`-role `r` of row `i`: Re / Im of `𝕂′` column `r / 2`. -/
def roleV (r : ℕ) (i : Fin n) : K :=
  if r % 2 = 0 then Quad.re _ (qv δ nA chals vS mS (r / 2) i) else Quad.im _ (qv δ nA chals vS mS (r / 2) i)

/-- The base columns `0 .. 71`. -/
def baseS (c : ℕ) (i : Fin n) : ZMod p :=
  if c = 0 then (if (i : ℕ) = 0 then 1 else 0)
  else if c = 1 then (if (i : ℕ) = n - 1 then 1 else 0)
  else if c = 2 then ((i : ℕ) : ZMod p)
  else if c = 3 then ((nA + (i : ℕ) : ℕ) : ZMod p)
  else if c = 4 then ((vS i / 2 ^ 32 : ℕ) : ZMod p)
  else if c = 5 then ((vS i % 2 ^ 32 : ℕ) : ZMod p)
  else if c < 70 then bitV (vS i) (c - 6)
  else if c = 70 then (((vS i / 2 ^ 32 : ℕ) : ZMod p))⁻¹
  else ((mS i : ℕ) : ZMod p)

/-- **The honest column function**: base (`< 72`), then the `𝕂`-role limbs. -/
def colS (c : ℕ) (i : Fin n) : ZMod p :=
  if c < 72 then baseS nA vS mS c i
  else coordN b (roleV δ nA chals vS mS ((c - 72) / 3) i) (c - 72)

/-- **The honest trace polynomials** (Lagrange interpolation over the row nodes). -/
def polyS (nodes : Fin n → ZMod p) (w : ℕ) : Fin w → (ZMod p)[X] := fun c =>
  Lagrange.interpolate Finset.univ nodes (fun i => colS δ nA b chals vS mS c i)

theorem tN_fin (i : Fin n) : tN δ nA chals vS mS i = rowT δ chals nA vS mS i := by
  simp [tN, i.isLt]

theorem accS_zero : accS δ nA chals vS mS 0 = tN δ nA chals vS mS 0 := by simp [accS]

theorem accS_succ (j : ℕ) :
    accS δ nA chals vS mS (j + 1) = accS δ nA chals vS mS j + tN δ nA chals vS mS (j + 1) := by
  simp only [accS]; rw [Finset.sum_range_succ]

theorem accS_last (hn : 0 < n) : accS δ nA chals vS mS (n - 1) = ∑ i, rowT δ chals nA vS mS i := by
  simp only [accS, show n - 1 + 1 = n by omega]
  rw [← Fin.sum_univ_eq_sum_range (tN δ nA chals vS mS) n]
  exact Finset.sum_congr rfl fun i _ => tN_fin δ nA chals vS mS i

theorem colS_base {c : ℕ} (hc : c < 72) (i : Fin n) : colS δ nA b chals vS mS c i = baseS nA vS mS c i := by
  simp [colS, hc]

theorem colS_role {r : ℕ} (hr : r < 6) (k : Fin 3) (i : Fin n) :
    colS δ nA b chals vS mS (72 + 3 * r + k) i = coord b (roleV δ nA chals vS mS r i) k := by
  have hk := k.isLt
  simp only [colS, if_neg (show ¬ (72 + 3 * r + (k : ℕ) < 72) by omega),
    show (72 + 3 * r + (k : ℕ) - 72) / 3 = r by omega]
  unfold coordN
  congr 1
  exact Fin.ext (by simp; omega)

theorem roleV_pair (s : ℕ) (i : Fin n) :
    Quad.mk _ (roleV δ nA chals vS mS (2 * s) i) (roleV δ nA chals vS mS (2 * s + 1) i) =
      qv δ nA chals vS mS s i := by
  simp only [roleV, show (2 * s) % 2 = 0 by omega, show (2 * s + 1) % 2 = 1 by omega,
    show (2 * s) / 2 = s by omega, show (2 * s + 1) / 2 = s by omega, if_true, one_ne_zero, if_false]
  exact Quad.mk_re_im _ _

end Trace

/-! ## 4. The row environments of the honest trace -/

/-- The honest trace at the chip's width. -/
abbrev polySC {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K] [Fintype K]
    (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (nA : ℕ) (b : Basis (Fin 3) (ZMod p) K)
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (vS mS : Fin n → ℕ) :
    Fin (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs).rap.w → (ZMod p)[X] :=
  polyS δ nA b chals vS mS nodes _

section Env
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (nA : ℕ) (b : Basis (Fin 3) (ZMod p) K)
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (vS mS : Fin n → ℕ)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "PS" => polySC δ nA b hn nodes orbit chals pubs vS mS
local notation "EF" => SplitChipJ9.spEF b nodes orbit chals pubs PS
local notation "EK" => SplitChipJ9.spEK δ nA b nodes orbit chals pubs PS

theorem EF_trace (hinj : Function.Injective nodes) (i : Fin n) {c : ℕ} (hc : c < 90) :
    (EF i).trace c = colS δ nA b chals vS mS c i := by
  have hw : (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs).rap.w = 90 :=
    SplitChipJ9.width_eq δ nA b hn nodes orbit chals pubs
  show (Reify.envOfTrace PS orbit.ω (nodes i) (slotVal b 72 chals) (slotVal b 72 pubs)).trace c = _
  rw [envOfTrace_trace _ _ _ _ _ (show c < (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs).rap.w by
    rw [hw]; exact hc)]
  exact Lagrange.eval_interpolate_at_node (fun i => colS δ nA b chals vS mS c i) hinj.injOn (Finset.mem_univ i)

theorem EK_trace (hinj : Function.Injective nodes) (i : Fin n) {r : ℕ} (hr : r < 6) :
    (EK i).trace r = roleV δ nA chals vS mS r i := by
  show (gatherEnv b ((SplitChipJ9.splitTemplateJ9 δ nA).col0 3) (EF i)).trace r = _
  have hv : ∀ k : Fin 3, (EF i).trace (72 + 3 * r + k) = coord b (roleV δ nA chals vS mS r i) k := fun k => by
    have := k.isLt
    rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by omega), colS_role δ nA b chals vS mS hr k i]
  simp only [gatherEnv, ChipTemplate.col0, SplitChipJ9.splitTemplateJ9_baseCols, hv, coord]
  exact b.sum_repr _

theorem qK (hinj : Function.Injective nodes) (i : Fin n) (s : ℕ) (hs : s < 3) :
    Quad.mk _ ((EK i).trace (2 * s)) ((EK i).trace (2 * s + 1)) = qv δ nA chals vS mS s i := by
  rw [EK_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by omega),
    EK_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by omega)]
  exact roleV_pair δ nA chals vS mS s i

theorem EF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) : ∀ j, (EF i).traceNext j = (EF ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j => traceNext_eq nodes orbit PS _ _ hadj i hi j

theorem EK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) : ∀ j, (EK i).traceNext j = (EK ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j => TeleH.gather_next_T b _ _ _ (EF_next δ nA b hn nodes orbit chals pubs vS mS hadj i hi) j

/-! ### Base columns of a row -/

theorem EF_isFT (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.isFT = if (i : ℕ) = 0 then 1 else 0 := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.isFT]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.isFT])]
  simp [baseS, SplitChipJ9.isFT]

theorem EF_isLT (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.isLT = if (i : ℕ) = n - 1 then 1 else 0 := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.isLT]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.isLT])]
  simp [baseS, SplitChipJ9.isLT]

theorem EF_ctr (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.ctr = ((i : ℕ) : ZMod p) := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.ctr]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.ctr])]
  simp [baseS, SplitChipJ9.ctr]

theorem EF_sid (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.sid = ((nA + (i : ℕ) : ℕ) : ZMod p) := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.sid]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.sid])]
  simp [baseS, SplitChipJ9.sid]

theorem EF_hi (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.hi = ((vS i / 2 ^ 32 : ℕ) : ZMod p) := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.hi]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.hi])]
  simp [baseS, SplitChipJ9.hi]

theorem EF_lo (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.lo = ((vS i % 2 ^ 32 : ℕ) : ZMod p) := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.lo]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.lo])]
  simp [baseS, SplitChipJ9.lo]

theorem EF_bit (hinj : Function.Injective nodes) (i : Fin n) {j : ℕ} (hj : j < 64) :
    (EF i).trace (SplitChipJ9.bit0 + j) = bitV (vS i) j := by
  have e0 : SplitChipJ9.bit0 = 6 := rfl
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by rw [e0]; omega),
    colS_base δ nA b chals vS mS (by rw [e0]; omega)]
  simp only [baseS, e0]
  split_ifs <;> first | omega | (simp only [show 6 + j - 6 = j by omega])

theorem EF_invHi (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.invHi = (((vS i / 2 ^ 32 : ℕ) : ZMod p))⁻¹ := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.invHi]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.invHi])]
  simp [baseS, SplitChipJ9.invHi]

theorem EF_mult (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace SplitChipJ9.mult = ((mS i : ℕ) : ZMod p) := by
  rw [EF_trace δ nA b hn nodes orbit chals pubs vS mS hinj i (by simp [SplitChipJ9.mult]),
    colS_base δ nA b chals vS mS (by simp [SplitChipJ9.mult])]
  simp [baseS, SplitChipJ9.mult]

/-- **The base gates hold on the honest row.** -/
theorem base_honest (hp : 2 ^ 32 < p) (hv : ∀ i, 2 ^ 32 ≤ vS i ∧ vS i < 2 ^ 64)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (i : Fin n) :
    ∀ g ∈ (SplitChipJ9.baseGates nA : List (CoeffExpr (ZMod p))), g.eval (EF i) = 0 := by
  have hbit : ∀ j, j < 64 → (EF i).trace (SplitChipJ9.bit0 + j) = bitV (vS i) j := fun j hj =>
    EF_bit δ nA b hn nodes orbit chals pubs vS mS hinj i hj
  intro g hg
  simp only [SplitChipJ9.baseGates, List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · simp only [SplitChipJ9.bitBool, List.mem_map, List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    simp only [boolE, CoeffExpr.eval, cv]
    rw [hbit j hj]
    unfold bitV
    split_ifs <;> simp
  · simp only [SplitChipJ9.decode, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp only [CoeffExpr.eval, cv, eval_bitSum]
      rw [EF_hi δ nA b hn nodes orbit chals pubs vS mS hinj i, sub_eq_zero,
        cast_hi (vS i) (hv i).2]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [add_assoc, hbit (32 + k) (by have := Finset.mem_range.mp hk; omega)]
    · simp only [CoeffExpr.eval, cv, eval_bitSum]
      rw [EF_lo δ nA b hn nodes orbit chals pubs vS mS hinj i, sub_eq_zero, cast_lo (vS i)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hbit k (by have := Finset.mem_range.mp hk; omega)]
  · simp only [SplitChipJ9.counter, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · simp only [CoeffExpr.eval, cv]
      rw [EF_isFT δ nA b hn nodes orbit chals pubs vS mS hinj i,
        EF_ctr δ nA b hn nodes orbit chals pubs vS mS hinj i]
      by_cases h0 : (i : ℕ) = 0
      · simp [h0]
      · simp [h0]
    · simp only [CoeffExpr.eval, cv, nv, notE]
      rw [EF_isLT δ nA b hn nodes orbit chals pubs vS mS hinj i]
      by_cases hl : (i : ℕ) = n - 1
      · rw [if_pos hl]; simp
      · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
        rw [if_neg hl, EF_next δ nA b hn nodes orbit chals pubs vS mS hadj i hi _,
          EF_ctr δ nA b hn nodes orbit chals pubs vS mS hinj ⟨(i : ℕ) + 1, hi⟩,
          EF_ctr δ nA b hn nodes orbit chals pubs vS mS hinj i]
        push_cast
        ring
    · simp only [CoeffExpr.eval, cv]
      rw [EF_sid δ nA b hn nodes orbit chals pubs vS mS hinj i,
        EF_ctr δ nA b hn nodes orbit chals pubs vS mS hinj i]
      push_cast
      ring
  · simp only [SplitChipJ9.hiNZ, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl
    simp only [CoeffExpr.eval, cv]
    rw [EF_hi δ nA b hn nodes orbit chals pubs vS mS hinj i,
      EF_invHi δ nA b hn nodes orbit chals pubs vS mS hinj i,
      mul_inv_cancel₀ (hi_ne_zero hp (vS i) (hv i)), sub_self]

/-! ### The `𝕂′` gates -/

theorem gates_of_ev' (e : QE (ZMod p)) (eK : Env K) (eF : Env (ZMod p)) (h : e.ev δ eK eF = 0) :
    ∀ g ∈ e.gates, g.eval eK eF = 0 := by
  rw [QE.ev, Quad.mk_eq_zero_iff] at h
  intro g hg
  simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h.1
  · exact h.2

theorem eK_chal (i : Fin n) (idx : ℕ) : (EK i).chal idx = chals idx :=
  TeleH.gather_chal_T b (SplitChipJ9.splitTemplateJ9 δ nA) 72 (SplitChipJ9.splitTemplateJ9_baseCols δ nA)
    (EF i) chals rfl idx

theorem eK_pub (i : Fin n) (idx : ℕ) : (EK i).pub idx = pubs idx :=
  TeleH.gather_pub_T b (SplitChipJ9.splitTemplateJ9 δ nA) 72 (SplitChipJ9.splitTemplateJ9_baseCols δ nA)
    (EF i) pubs rfl idx


theorem accS_first {i : Fin n} (h0 : ((i : ℕ)) = 0) :
    accS δ nA chals vS mS (i : ℕ) = rowT δ chals nA vS mS i := by
  have e : accS δ nA chals vS mS (i : ℕ) = tN δ nA chals vS mS (i : ℕ) := by
    rw [h0]; exact accS_zero δ nA chals vS mS
  rw [e, tN_fin]

theorem tN_succ {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    tN δ nA chals vS mS ((i : ℕ) + 1) = rowT δ chals nA vS mS ⟨(i : ℕ) + 1, hi⟩ := by
  simp [tN, hi]

/-- The denominators of the honest row at the handle coins. -/
theorem den2_ev (hinj : Function.Injective nodes) (i : Fin n) :
    (HQ.denKeyQ δ (SplitChipJ9.key2 : List (CoeffExpr (ZMod p)))).ev δ (EK i) (EF i) =
      d2 δ chals nA vS i := by
  have hl : (SplitChipJ9.key2 : List (CoeffExpr (ZMod p))).length = 4 := rfl
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev, eK_chal δ nA b hn nodes orbit chals pubs vS mS i, hl]
  simp [Finset.sum_range_succ, SplitChipJ9.key2, d2, dKey4, CoeffExpr.eval, cv,
    EF_sid δ nA b hn nodes orbit chals pubs vS mS hinj i, EF_lo δ nA b hn nodes orbit chals pubs vS mS hinj i]

theorem den3_ev (hinj : Function.Injective nodes) (i : Fin n) :
    (HQ.denKeyQ δ (SplitChipJ9.key3 : List (CoeffExpr (ZMod p)))).ev δ (EK i) (EF i) =
      d3 δ chals nA vS i := by
  have hl : (SplitChipJ9.key3 : List (CoeffExpr (ZMod p))).length = 4 := rfl
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev, eK_chal δ nA b hn nodes orbit chals pubs vS mS i, hl]
  simp [Finset.sum_range_succ, SplitChipJ9.key3, d3, dKey4, CoeffExpr.eval, cv,
    EF_sid δ nA b hn nodes orbit chals pubs vS mS hinj i, EF_hi δ nA b hn nodes orbit chals pubs vS mS hinj i]

theorem pTerm_cur (hinj : Function.Injective nodes) (i : Fin n) :
    (SplitChipJ9.pTerm true : QE (ZMod p)).ev δ (EK i) (EF i) = rowT δ chals nA vS mS i := by
  show (QE.scale (cv SplitChipJ9.mult) (QE.add (QE.var SplitChipJ9.inv2) (QE.var SplitChipJ9.inv3))).ev δ
    (EK i) (EF i) = _
  have hI2 : Quad.mk _ ((EK i).trace SplitChipJ9.inv2) ((EK i).trace (SplitChipJ9.inv2 + 1)) =
      (d2 δ chals nA vS i)⁻¹ := qK δ nA b hn nodes orbit chals pubs vS mS hinj i 0 (by norm_num)
  have hI3 : Quad.mk _ ((EK i).trace SplitChipJ9.inv3) ((EK i).trace (SplitChipJ9.inv3 + 1)) =
      (d3 δ chals nA vS i)⁻¹ := qK δ nA b hn nodes orbit chals pubs vS mS hinj i 1 (by norm_num)
  rw [ev_scale, ev_add, ev_var, ev_var, hI2, hI3]
  simp only [cv, CoeffExpr.eval]
  rw [EF_mult δ nA b hn nodes orbit chals pubs vS mS hinj i]
  rfl

theorem pTerm_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (SplitChipJ9.pTerm false : QE (ZMod p)).ev δ (EK i) (EF i) = rowT δ chals nA vS mS ⟨(i : ℕ) + 1, hi⟩ := by
  show (QE.scale (nv SplitChipJ9.mult) (QE.add (QE.next SplitChipJ9.inv2) (QE.next SplitChipJ9.inv3))).ev δ
    (EK i) (EF i) = _
  have hI2 : Quad.mk _ ((EK ⟨(i : ℕ) + 1, hi⟩).trace SplitChipJ9.inv2)
      ((EK ⟨(i : ℕ) + 1, hi⟩).trace (SplitChipJ9.inv2 + 1)) =
      (d2 δ chals nA vS ⟨(i : ℕ) + 1, hi⟩)⁻¹ :=
    qK δ nA b hn nodes orbit chals pubs vS mS hinj ⟨(i : ℕ) + 1, hi⟩ 0 (by norm_num)
  have hI3 : Quad.mk _ ((EK ⟨(i : ℕ) + 1, hi⟩).trace SplitChipJ9.inv3)
      ((EK ⟨(i : ℕ) + 1, hi⟩).trace (SplitChipJ9.inv3 + 1)) =
      (d3 δ chals nA vS ⟨(i : ℕ) + 1, hi⟩)⁻¹ :=
    qK δ nA b hn nodes orbit chals pubs vS mS hinj ⟨(i : ℕ) + 1, hi⟩ 1 (by norm_num)
  rw [ev_scale, ev_add, ev_next, ev_next]
  simp only [nv, CoeffExpr.eval, EK_next δ nA b hn nodes orbit chals pubs vS mS hadj i hi,
    EF_next δ nA b hn nodes orbit chals pubs vS mS hadj i hi]
  rw [hI2, hI3, EF_mult δ nA b hn nodes orbit chals pubs vS mS hinj ⟨(i : ℕ) + 1, hi⟩]
  rfl

/-- **The `𝕂′` equations hold on the honest row.** -/
theorem sp_qgates_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hd2 : ∀ i, d2 δ chals nA vS i ≠ 0) (hd3 : ∀ i, d3 δ chals nA vS i ≠ 0)
    (hpub : Quad.mk _ (pubs SplitChipJ9.pubSPs) (pubs (SplitChipJ9.pubSPs + 1)) =
      ∑ i, rowT δ chals nA vS mS i) (i : Fin n) :
    ∀ e ∈ SplitChipJ9.spQ δ, e.ev δ (EK i) (EF i) = 0 := by
  have hI2 : Quad.mk _ ((EK i).trace SplitChipJ9.inv2) ((EK i).trace (SplitChipJ9.inv2 + 1)) =
      (d2 δ chals nA vS i)⁻¹ := qK δ nA b hn nodes orbit chals pubs vS mS hinj i 0 (by norm_num)
  have hI3 : Quad.mk _ ((EK i).trace SplitChipJ9.inv3) ((EK i).trace (SplitChipJ9.inv3 + 1)) =
      (d3 δ chals nA vS i)⁻¹ := qK δ nA b hn nodes orbit chals pubs vS mS hinj i 1 (by norm_num)
  have hAcc : Quad.mk _ ((EK i).trace SplitChipJ9.acc) ((EK i).trace (SplitChipJ9.acc + 1)) =
      accS δ nA chals vS mS (i : ℕ) := qK δ nA b hn nodes orbit chals pubs vS mS hinj i 2 (by norm_num)
  intro e he
  simp only [SplitChipJ9.spQ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · rw [ev_sub, ev_mul, ev_var, den2_ev δ nA b hn nodes orbit chals pubs vS mS hinj i, ev_one, hI2,
      inv_mul_cancel₀ (hd2 i), sub_self]
  · rw [ev_sub, ev_mul, ev_var, den3_ev δ nA b hn nodes orbit chals pubs vS mS hinj i, ev_one, hI3,
      inv_mul_cancel₀ (hd3 i), sub_self]
  · rw [ev_scale, ev_sub, ev_var, pTerm_cur δ nA b hn nodes orbit chals pubs vS mS hinj i]
    simp only [cv, CoeffExpr.eval]
    rw [EF_isFT δ nA b hn nodes orbit chals pubs vS mS hinj i, hAcc]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0, accS_first δ nA chals vS mS h0, sub_self, mul_zero]
    · rw [if_neg h0]; simp [liftQ]
  · rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var]
    simp only [notE, cv, CoeffExpr.eval]
    rw [EF_isLT δ nA b hn nodes orbit chals pubs vS mS hinj i]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      have hAccN : Quad.mk _ ((EK ⟨(i : ℕ) + 1, hi⟩).trace SplitChipJ9.acc)
          ((EK ⟨(i : ℕ) + 1, hi⟩).trace (SplitChipJ9.acc + 1)) = accS δ nA chals vS mS ((i : ℕ) + 1) :=
        qK δ nA b hn nodes orbit chals pubs vS mS hinj ⟨(i : ℕ) + 1, hi⟩ 2 (by norm_num)
      rw [if_neg hl, pTerm_next δ nA b hn nodes orbit chals pubs vS mS hinj hadj i hi]
      simp only [EK_next δ nA b hn nodes orbit chals pubs vS mS hadj i hi]
      rw [hAccN, hAcc]
      have h0 : accS δ nA chals vS mS ((i : ℕ) + 1) - accS δ nA chals vS mS (i : ℕ) -
          rowT δ chals nA vS mS ⟨(i : ℕ) + 1, hi⟩ = 0 := by
        rw [accS_succ, tN_succ δ nA chals vS mS hi]; ring
      rw [h0, mul_zero]
  · rw [ev_scale, ev_sub, ev_var, ev_pub]
    simp only [cv, CoeffExpr.eval]
    rw [EF_isLT δ nA b hn nodes orbit chals pubs vS mS hinj i, hAcc,
      eK_pub δ nA b hn nodes orbit chals pubs vS mS i, eK_pub δ nA b hn nodes orbit chals pubs vS mS i]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl, hl, accS_last δ nA chals vS mS hn, hpub, sub_self, mul_zero]
    · rw [if_neg hl]; simp [liftQ]

/-! ## 5. Honest acceptance -/

/-- **RAP-level honest acceptance of the split chip** (`splitChipJ9 = expandChip splitTemplateJ9`): the honest
trace `polySC` of a list of field-axis values satisfies the chip and binds its two preprocessing columns, from
`2^32 < p`, `2^32 ≤ vS i < 2^64`, the orbit facts, the completeness bad events `hd2`, `hd3` (the two key
denominators at the handle coins do not vanish) and the public
`(pub₀, pub₁) = Σ_i mS i · (den₂⁻¹ + den₃⁻¹)`. -/
theorem splitChipJ9_honest_sat (hp : 2 ^ 32 < p) (hv : ∀ i, 2 ^ 32 ≤ vS i ∧ vS i < 2 ^ 64)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hd2 : ∀ i, d2 δ chals nA vS i ≠ 0) (hd3 : ∀ i, d3 δ chals nA vS i ≠ 0)
    (hpub : Quad.mk _ (pubs SplitChipJ9.pubSPs) (pubs (SplitChipJ9.pubSPs + 1)) =
      ∑ i, rowT δ chals nA vS mS i) :
    RAP.SatisfiesWithPreprocessing (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs) PS := by
  refine ⟨(expandChip_satisfies_iff_language (SplitChipJ9.splitTemplateJ9 δ nA) b _ _ orbit _ _).mpr ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    refine ⟨base_honest δ nA b hn nodes orbit chals pubs vS mS hp hv hinj hadj i, ?_, ?_, ?_⟩
    · intro g hg; simp [SplitChipJ9.splitTemplateJ9] at hg
    · intro g hg; simp [SplitChipJ9.splitTemplateJ9] at hg
    · intro g hg
      have hg' : g ∈ (SplitChipJ9.spQ δ).flatMap QE.gates := hg
      obtain ⟨e, he, hg''⟩ := List.mem_flatMap.mp hg'
      exact gates_of_ev' δ e _ _
        (sp_qgates_honest δ nA b hn nodes orbit chals pubs vS mS hinj hadj hd2 hd3 hpub i e he) g hg''
  · intro j
    rcases j with ⟨_ | _ | j, hj⟩
    · show Lagrange.interpolate Finset.univ nodes (fun i => colS δ nA b chals vS mS 0 i) =
        Lagrange.interpolate Finset.univ nodes (fun i : Fin n => if (i : ℕ) = 0 then (1 : ZMod p) else 0)
      congr 1
    · show Lagrange.interpolate Finset.univ nodes (fun i => colS δ nA b chals vS mS 1 i) =
        Lagrange.interpolate Finset.univ nodes
          (fun i : Fin n => if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then (1 : ZMod p) else 0)
      congr 1
      funext i
      rw [colS_base δ nA b chals vS mS (by norm_num)]
      simp only [baseS]
      by_cases hl : (i : ℕ) = n - 1
      · simp [hl, Fin.ext_iff]
      · simp [hl, Fin.ext_iff]
    · exact absurd hj (by show ¬ (j + 1 + 1 < 2); omega)

/-- The conjunction shape `AcceptsJ9A.SPChipOK` consumes: the raw satisfaction and the binding. -/
theorem splitChipJ9_honest_sat' (hp : 2 ^ 32 < p) (hv : ∀ i, 2 ^ 32 ≤ vS i ∧ vS i < 2 ^ 64)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hd2 : ∀ i, d2 δ chals nA vS i ≠ 0) (hd3 : ∀ i, d3 δ chals nA vS i ≠ 0)
    (hpub : Quad.mk _ (pubs SplitChipJ9.pubSPs) (pubs (SplitChipJ9.pubSPs + 1)) =
      ∑ i, rowT δ chals nA vS mS i) :
    (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs).rap.Satisfies PS ∧
      (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs).BindsPreprocessing PS :=
  splitChipJ9_honest_sat δ nA b hn nodes orbit chals pubs vS mS hp hv hinj hadj hd2 hd3 hpub

/-! ## 6. The provided records of the honest trace -/

/-- The record `(nA + i, tag, 0, val)` as an 8-vector (zero-padded), lifted to `𝕂`. -/
def recK (nA i tag val : ℕ) : Fin 8 → K := fun c =>
  algebraMap (ZMod p) K ((([(nA + i : ℕ), tag, 0, val, 0, 0, 0, 0] : List ℕ).getD c 0 : ℕ) : ZMod p)

theorem keyVecL_key2 (i v : ℕ) (eF : Env (ZMod p)) (hs : eF.trace SplitChipJ9.sid = ((nA + i : ℕ) : ZMod p))
    (hl : eF.trace SplitChipJ9.lo = ((v % 2 ^ 32 : ℕ) : ZMod p)) :
    SplitChipJ9.keyVecL (K := K) 8 SplitChipJ9.key2 eF = recK (p := p) nA i 2 (v % 2 ^ 32) := by
  funext c
  fin_cases c <;>
    simp [SplitChipJ9.keyVecL, SplitChipJ9.key2, recK, hs, hl, CoeffExpr.eval, cv]

theorem keyVecL_key3 (i v : ℕ) (eF : Env (ZMod p)) (hs : eF.trace SplitChipJ9.sid = ((nA + i : ℕ) : ZMod p))
    (hh : eF.trace SplitChipJ9.hi = ((v / 2 ^ 32 : ℕ) : ZMod p)) :
    SplitChipJ9.keyVecL (K := K) 8 SplitChipJ9.key3 eF = recK (p := p) nA i 3 (v / 2 ^ 32) := by
  funext c
  fin_cases c <;>
    simp [SplitChipJ9.keyVecL, SplitChipJ9.key3, recK, hs, hh, CoeffExpr.eval, cv]

/-- **The honest providers**: per row with `mS i ≠ 0`, the records `(nA + i, 2, 0, lo)` and
`(nA + i, 3, 0, hi)` with weight `mS i` (with `mS i < p`, so the multiplicity filter is `mS i ≠ 0`). -/
theorem splitProvs_honest (hinj : Function.Injective nodes) (chals' pubs' : ℕ → K)
    (hm : ∀ i, mS i < p) :
    SplitChipJ9.splitProvs b nodes orbit chals' pubs' PS =
      (List.finRange n).flatMap fun i =>
        if mS i = 0 then [] else
          [(recK (p := p) nA i 2 (vS i % 2 ^ 32), algebraMap (ZMod p) K ((mS i : ℕ) : ZMod p)),
           (recK (p := p) nA i 3 (vS i / 2 ^ 32), algebraMap (ZMod p) K ((mS i : ℕ) : ZMod p))] := by
  have ht : ∀ (i : Fin n) (c : ℕ), c < 90 →
      (SplitChipJ9.spEF b nodes orbit chals' pubs' PS i).trace c = (EF i).trace c := by
    intro i c hc
    have hw : (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs).rap.w = 90 :=
      SplitChipJ9.width_eq δ nA b hn nodes orbit chals pubs
    have hc' : c < (SplitChipJ9.splitChipJ9 δ nA b hn nodes orbit chals pubs).rap.w := by rw [hw]; exact hc
    show (Reify.envOfTrace PS orbit.ω (nodes i) _ _).trace c = (Reify.envOfTrace PS orbit.ω (nodes i) _ _).trace c
    rw [envOfTrace_trace _ _ _ _ _ hc', envOfTrace_trace _ _ _ _ _ hc']
  unfold SplitChipJ9.splitProvs
  refine List.flatMap_congr fun i _ => ?_
  have hmult : (SplitChipJ9.spEF b nodes orbit chals' pubs' PS i).trace SplitChipJ9.mult = ((mS i : ℕ) : ZMod p) := by
    rw [ht i _ (by simp [SplitChipJ9.mult]), EF_mult δ nA b hn nodes orbit chals pubs vS mS hinj i]
  have hsid : (SplitChipJ9.spEF b nodes orbit chals' pubs' PS i).trace SplitChipJ9.sid =
      ((nA + (i : ℕ) : ℕ) : ZMod p) := by
    rw [ht i _ (by simp [SplitChipJ9.sid]), EF_sid δ nA b hn nodes orbit chals pubs vS mS hinj i]
  have hlo : (SplitChipJ9.spEF b nodes orbit chals' pubs' PS i).trace SplitChipJ9.lo =
      ((vS i % 2 ^ 32 : ℕ) : ZMod p) := by
    rw [ht i _ (by simp [SplitChipJ9.lo]), EF_lo δ nA b hn nodes orbit chals pubs vS mS hinj i]
  have hhi : (SplitChipJ9.spEF b nodes orbit chals' pubs' PS i).trace SplitChipJ9.hi =
      ((vS i / 2 ^ 32 : ℕ) : ZMod p) := by
    rw [ht i _ (by simp [SplitChipJ9.hi]), EF_hi δ nA b hn nodes orbit chals pubs vS mS hinj i]
  have hz : (((mS i : ℕ) : ZMod p) = 0) ↔ mS i = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).trans
      ⟨fun hd => Nat.eq_zero_of_dvd_of_lt hd (hm i), fun h => h ▸ dvd_zero p⟩
  rw [hmult, keyVecL_key2 (K := K) nA i (vS i) (SplitChipJ9.spEF b nodes orbit chals' pubs' PS i) hsid hlo,
    keyVecL_key3 (K := K) nA i (vS i) (SplitChipJ9.spEF b nodes orbit chals' pubs' PS i) hsid hhi]
  by_cases h0 : mS i = 0
  · simp [h0]
  · rw [if_neg (fun h => h0 (hz.mp h)), if_neg h0]

end Env

end

/-! ## Axioms -/

section Axioms
#print axioms splitChipJ9_honest_sat
#print axioms splitChipJ9_honest_sat'
#print axioms splitProvs_honest
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH
