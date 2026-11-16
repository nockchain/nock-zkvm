/-
  Nock/NockVMROM/Thm54/TraceGen/GenFormRGeneral.lean

  The generic generator's ROOTZERO used the
  `λ = 2` closed forms `MemoryTable.formRT_mul_formRC_two` / `formRRead_two` (`T·C' = 2^{n−1}·a`).
  The chip samples `λ`, so the honest identity must hold at the configuration's `λ`.

  * `axisPoly λ a = λ^m + Σ_{k<m} a_k·λ^k` (`m = log₂ a`): the binary digits of `a` read in base
    `λ`.  At `λ = 2` it is `a` (`axisPoly_two`), the receipt that the `λ = 2` closed forms are the
    instance.
  * `formRT_mul_formRC`: `T·C' = λ^{n−1}·axisPoly λ a` at every `λ`, for `m ≤ n − 1`.
  * `formRRead_general`: the Form R read weights of an a-bearing record at any `λ`.
  * `axisPoly_rest_top` / `axisPoly_rest_not_top`: the one-step recursion along the descent
    (`GenMem.axisTopBit` / `axisRest`, stated here in raw arithmetic so this module needs only
    `MemoryTable`).

  **No hypothesis on `λ`** (not `λ ≠ 0`, not `2 ≠ 0`): every identity is a polynomial identity in
  `λ`.  The only side condition is the certificate window `log₂ a ≤ n − 1`, which the generator
  already carries (`a < ringChar K`, `MemoryTable.log2_le_pwScaleExp`).
-/
import Nock.MemoryTable

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock

variable {K : Type*} [Field K]

/-- The binary digits of `a` below its leading `1`, read in base `λ`, plus the leading `λ^m`:
`axisPoly λ a = λ^m + Σ_{k<m} a_k·λ^k`, `m = log₂ a`.  At `λ = 2` this is `a`. -/
def axisPoly (lmb : K) (a : ℕ) : K :=
  lmb ^ a.log2 + ∑ k ∈ Finset.range a.log2, (if a.testBit k then (1 : K) else 0) * lmb ^ k

@[simp] theorem axisPoly_one (lmb : K) : axisPoly lmb 1 = 1 := by
  simp [axisPoly, show Nat.log2 1 = 0 by decide]

/-- **The general Form R product identity** (`Batch590.formR_product_general`, ported):
`T·C' = λ^{n−1}·axisPoly λ a` at every `λ`, whenever `log₂ a ≤ n − 1`. -/
theorem formRT_mul_formRC (lmb : K) (a : ℕ) (hm : a.log2 ≤ MemoryTable.pwScaleExp K) :
    MemoryTable.formRT lmb a * MemoryTable.formRC lmb a =
      lmb ^ MemoryTable.pwScaleExp K * axisPoly lmb a := by
  set n := MemoryTable.pwScaleExp K with hn
  set m := a.log2 with hmdef
  have hshift : MemoryTable.formRCertShift a = m := MemoryTable.formRCertShift_eq_log2 a
  have hsum : ((List.range n).map (fun j =>
      (if MemoryTable.formRCertBit a j then (1 : K) else 0) * lmb ^ (n - (j + 1)))).sum =
      ∑ j ∈ Finset.range m,
        (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n - (j + 1)) := by
    rw [MemoryTable.list_range_map_sum]
    have hz : ∀ j ∈ Finset.range n, j ∉ Finset.range m →
        (if MemoryTable.formRCertBit a j then (1 : K) else 0) * lmb ^ (n - (j + 1)) = 0 := by
      intro j _ hj
      have hj' : ¬ j < m := by simpa using hj
      simp [MemoryTable.formRCertBit, hshift, hj']
    rw [← Finset.sum_subset (Finset.range_mono hm) hz]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := Finset.mem_range.mp hj
    simp [MemoryTable.formRCertBit, hshift, hj']
  have hreflect :
      ∑ j ∈ Finset.range m, (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (m - 1 - j) =
        ∑ k ∈ Finset.range m, (if a.testBit k then (1 : K) else 0) * lmb ^ k :=
    Finset.sum_range_reflect (fun k => (if a.testBit k then (1 : K) else 0) * lmb ^ k) m
  have hterm : ∀ j ∈ Finset.range m,
      lmb ^ m * ((if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n - (j + 1))) =
        lmb ^ n * ((if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (m - 1 - j)) := by
    intro j hj
    have hj' : j < m := Finset.mem_range.mp hj
    have he : m + (n - (j + 1)) = n + (m - 1 - j) := by omega
    calc lmb ^ m * ((if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n - (j + 1)))
        = (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (m + (n - (j + 1))) := by
          rw [pow_add]; ring
      _ = (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n + (m - 1 - j)) := by rw [he]
      _ = _ := by rw [pow_add]; ring
  have hmn : m ≤ n := hm
  simp only [MemoryTable.formRT, MemoryTable.formRC, hshift]
  rw [← hn, hsum, mul_add, Finset.mul_sum, Finset.sum_congr rfl hterm,
    ← Finset.mul_sum, hreflect, axisPoly, ← hmdef]
  rw [← pow_add, show m + n = n + m by omega, pow_add]
  ring

/-- **Honest Form R read weights at any `λ`.**  For a Nock axis `a < ringChar K` stored as its
nat-cast, `formRReadPw = λ^{n−1}·λ^m·ts` and `formRReadCounts = λ^{n−1}·axisPoly λ a·ts`.
At `λ = 2` this is `MemoryTable.formRRead_two` (`axisPoly_two`). -/
theorem formRRead_general (lmb : K) (r : ComputeTable.MemRec K) {a : ℕ}
    (hax : r.axis = (a : K)) (ha : a < ringChar K) :
    MemoryTable.formRReadPw lmb r = lmb ^ MemoryTable.pwScaleExp K * lmb ^ a.log2 * r.ts ∧
      MemoryTable.formRReadCounts lmb r =
        lmb ^ MemoryTable.pwScaleExp K * axisPoly lmb a * r.ts := by
  have hna : MemoryTable.nockAxisOf r.axis = a := by
    rw [hax]; exact MemoryTable.nockAxisOf_natCast ha
  constructor
  · rw [MemoryTable.formRReadPw, hna, MemoryTable.formRT_eq_pow_shift,
      MemoryTable.formRCertShift_eq_log2]
  · rw [MemoryTable.formRReadCounts, hna,
      formRT_mul_formRC lmb a (MemoryTable.log2_le_pwScaleExp ha)]

/-! ## The one-step recursion along the descent

`GenMem.axisTopBit a = decide (3·2^{m−1} ≤ a)` and `GenMem.axisRest a` is `a − 2^m` (tail) or
`a − 2^{m−1}` (head), `m = log₂ a`.  Consuming the bit below the leading `1` changes `axisPoly`
by `λ^m` on the tail path and by `(λ − 1)·λ^{m−1}` on the head path — exactly what one annotated
`decompose` adds to `counts` (`pw_P = λ·(pw_L + pw_R)`,
`counts_P = counts_L + counts_R + (λ − 1)(pw_L + pw_R) + pw_R`). -/

private theorem log2_eq_of_bounds {b k : ℕ} (hlo : 2 ^ k ≤ b) (hhi : b < 2 ^ (k + 1)) :
    b.log2 = k := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi

private theorem log2_bounds {a : ℕ} (ha : 1 ≤ a) : 2 ^ a.log2 ≤ a ∧ a < 2 ^ (a.log2 + 1) :=
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

private theorem axisPoly_step (lmb : K) {a b m : ℕ} (hm : a.log2 = m) (hm1 : 1 ≤ m)
    (hblo : 2 ^ (m - 1) ≤ b) (hbhi : b < 2 ^ m)
    (hmod : b % 2 ^ (m - 1) = a % 2 ^ (m - 1)) :
    axisPoly lmb a = axisPoly lmb b + lmb ^ m +
      ((if a.testBit (m - 1) then (1 : K) else 0) - 1) * lmb ^ (m - 1) := by
  have hblog : b.log2 = m - 1 :=
    log2_eq_of_bounds hblo (by rwa [Nat.sub_add_cancel hm1])
  have hbits : ∀ k < m - 1, b.testBit k = a.testBit k := by
    intro k hk
    have h1 := Nat.testBit_mod_two_pow b (m - 1) k
    have h2' := Nat.testBit_mod_two_pow a (m - 1) k
    rw [hmod] at h1
    rw [h1] at h2'
    simpa [hk] using h2'
  have hsplit : m = (m - 1) + 1 := by omega
  have hrange : Finset.range m = Finset.range ((m - 1) + 1) := by rw [← hsplit]
  have hpow : lmb ^ m = lmb * lmb ^ (m - 1) := by
    rw [← pow_succ', ← hsplit]
  unfold axisPoly
  rw [hblog, hm, hrange, Finset.sum_range_succ]
  have hsum : ∑ k ∈ Finset.range (m - 1), (if a.testBit k then (1 : K) else 0) * lmb ^ k =
      ∑ k ∈ Finset.range (m - 1), (if b.testBit k then (1 : K) else 0) * lmb ^ k :=
    Finset.sum_congr rfl fun k hk => by rw [hbits k (Finset.mem_range.mp hk)]
  rw [hsum]
  ring

/-- Shared setup: `m = log₂ a ≥ 1`, `2^m = 2·2^{m−1}`, `2·2^{m−1} ≤ a < 4·2^{m−1}`. -/
private theorem log2_setup {a m : ℕ} (h2 : 2 ≤ a) (hm : a.log2 = m) :
    1 ≤ m ∧ 2 ^ m = 2 * 2 ^ (m - 1) ∧ 2 * 2 ^ (m - 1) ≤ a ∧ a < 4 * 2 ^ (m - 1) := by
  obtain ⟨hlo, hhi⟩ := log2_bounds (a := a) (by omega)
  rw [hm] at hlo hhi
  have hm1 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    rw [this] at hhi
    omega
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow' : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by
    rw [pow_succ, hpow]; ring
  exact ⟨hm1, hpow, by omega, by omega⟩

private theorem testBit_pred_log2 {a m : ℕ}
    (hlo : 2 * 2 ^ (m - 1) ≤ a) (hhi : a < 4 * 2 ^ (m - 1)) :
    a.testBit (m - 1) = decide (3 * 2 ^ (m - 1) ≤ a) := by
  have hpos : 0 < 2 ^ (m - 1) := by positivity
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hq2 : 2 ≤ a / 2 ^ (m - 1) :=
    (Nat.le_div_iff_mul_le hpos).mpr (by linarith)
  have hq4 : a / 2 ^ (m - 1) < 4 := (Nat.div_lt_iff_lt_mul hpos).mpr (by linarith)
  by_cases h3 : 3 * 2 ^ (m - 1) ≤ a
  · have hq3 : 3 ≤ a / 2 ^ (m - 1) := (Nat.le_div_iff_mul_le hpos).mpr (by linarith)
    have : a / 2 ^ (m - 1) = 3 := by omega
    simp [this, h3]
  · have hq3 : a / 2 ^ (m - 1) < 3 := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
    have : a / 2 ^ (m - 1) = 2 := by omega
    simp [this, h3]

/-- Tail path (`axisTopBit a = true`, i.e. `3·2^{m−1} ≤ a`): `axisRest a = a − 2^m` and
`axisPoly λ a = axisPoly λ (a − 2^m) + λ^m`. -/
theorem axisPoly_rest_top (lmb : K) {a : ℕ} (h2 : 2 ≤ a) (htop : 3 * 2 ^ (a.log2 - 1) ≤ a) :
    axisPoly lmb a = axisPoly lmb (a - 2 ^ a.log2) + lmb ^ a.log2 := by
  generalize hm : a.log2 = m at htop ⊢
  obtain ⟨hm1, hpow, hlo, hhi⟩ := log2_setup h2 hm
  have hbit := testBit_pred_log2 hlo hhi
  have hmod : (a - 2 ^ m) % 2 ^ (m - 1) = a % 2 ^ (m - 1) := by
    have : a = (a - 2 ^ m) + 2 * 2 ^ (m - 1) := by omega
    conv_rhs => rw [this]
    rw [Nat.add_mul_mod_self_right]
  rw [axisPoly_step lmb hm hm1 (by omega) (by omega) hmod, hbit]
  simp [htop]

/-- Head path (`axisTopBit a = false`, i.e. `a < 3·2^{m−1}`): `axisRest a = a − 2^{m−1}` and
`axisPoly λ a = axisPoly λ (a − 2^{m−1}) + (λ − 1)·λ^{m−1}`. -/
theorem axisPoly_rest_not_top (lmb : K) {a : ℕ} (h2 : 2 ≤ a)
    (htop : ¬ 3 * 2 ^ (a.log2 - 1) ≤ a) :
    axisPoly lmb a = axisPoly lmb (a - 2 ^ (a.log2 - 1)) + (lmb - 1) * lmb ^ (a.log2 - 1) := by
  generalize hm : a.log2 = m at htop ⊢
  obtain ⟨hm1, hpow, hlo, hhi⟩ := log2_setup h2 hm
  have hbit := testBit_pred_log2 hlo hhi
  have hmod : (a - 2 ^ (m - 1)) % 2 ^ (m - 1) = a % 2 ^ (m - 1) := by
    have : a = (a - 2 ^ (m - 1)) + 1 * 2 ^ (m - 1) := by omega
    conv_rhs => rw [this]
    rw [Nat.add_mul_mod_self_right]
  rw [axisPoly_step lmb hm hm1 (by omega) (by omega) hmod, hbit]
  have hpow2 : lmb ^ m = lmb * lmb ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm1]
  simp [htop, hpow2]
  ring

/-- **The `λ = 2` receipt**: `axisPoly 2 a = a` for `a ≥ 1` — the binary expansion.  So the
general identities specialise to `MemoryTable.formRT_mul_formRC_two` / `formRRead_two`. -/
theorem axisPoly_two : ∀ (a : ℕ), 1 ≤ a → axisPoly (2 : K) a = (a : K) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro ha
    by_cases h2 : 2 ≤ a
    · by_cases htop : 3 * 2 ^ (a.log2 - 1) ≤ a
      · rw [axisPoly_rest_top (2 : K) h2 htop]
        generalize hm : a.log2 = m at htop ⊢
        obtain ⟨hm1, hpow, hlo, hhi⟩ := log2_setup h2 hm
        rw [ih (a - 2 ^ m) (by omega) (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      · rw [axisPoly_rest_not_top (2 : K) h2 htop]
        generalize hm : a.log2 = m at htop ⊢
        obtain ⟨hm1, hpow, hlo, hhi⟩ := log2_setup h2 hm
        rw [ih (a - 2 ^ (m - 1)) (by omega) (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
    · have : a = 1 := by omega
      subst this
      simp

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.formRT_mul_formRC
#print axioms Nock.NockVMROM.Thm54.TraceGen.formRRead_general
#print axioms Nock.NockVMROM.Thm54.TraceGen.axisPoly_rest_top
#print axioms Nock.NockVMROM.Thm54.TraceGen.axisPoly_rest_not_top
#print axioms Nock.NockVMROM.Thm54.TraceGen.axisPoly_two
