/-
  Nock/RedTeam/Batch588Thm54RowLevelHonest.lean

  Every local name is prefixed `L` where it shadows a lane name.

  What is compiled here:
  * §2 **R3 amended**: at `λ = 2` the product `T·C'` is injective on `[1, p)`
    (`formR_two_product_inj`), so "analogues of the `3`/`5` collision at every `λ`" is false at
    `λ = 2`; the `λ = 1` collision is real (`collision_at_one_3_5`).
  * §3 **R2 / R4 honest side**: a memory row encoded at BUILD time from the same `(record, a)`
    the compute row emits gives the same IO vector as the compute side's single encode
    (`build_encode_eq_io_encode`), and the transport is a same-source multiset equality
    (`same_source_transport`) — no injectivity.
  * §5 **Alternative (a)**: an encode-free embedding of decoded rows into a semantic execution
    needs an axis decoder; at `λ = 1` none exists (`no_axis_decoder_at_one`).
-/
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.NormNum.Prime
import Nock.ComputeTable

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch588

open Nock

/-! ## §1 Local Form R copies (lane `MemoryTable.lean`) -/

section FormR

variable {K : Type*} [Field K]

/-- Lane `MemoryTable.pwScaleExp`: `n − 1` at `n = Nat.size (ringChar K)`. -/
noncomputable def LpwScaleExp (K : Type*) [Field K] : ℕ := Nat.size (ringChar K) - 1

/-- Lane `formRCertShift`: `m = Nat.size a − 1`. -/
def LcertShift (a : ℕ) : ℕ := Nat.size a - 1

/-- Lane `formRCertBit`: MSB-first certificate bits. -/
def LcertBit (a j : ℕ) : Bool :=
  if j < LcertShift a then a.testBit (LcertShift a - 1 - j) else false

/-- Lane `formRT`: `T = λ^m`. -/
def LformRT (lmb : K) (ax : ℕ) : K := lmb ^ LcertShift ax

/-- Lane `formRC`: `C' = λ^{n−1} + Σ_j c_{j+1} λ^{n−1−(j+1)}`. -/
noncomputable def LformRC (lmb : K) (ax : ℕ) : K :=
  let n := LpwScaleExp K
  lmb ^ n +
    ((List.range n).map (fun j =>
      (if LcertBit ax j then (1 : K) else 0) * lmb ^ (n - (j + 1)))).sum

/-- Lane `nockAxisOf`: residue `< ringChar K` whose cast is `x`. -/
noncomputable def LnockAxisOf (x : K) : ℕ :=
  Classical.epsilon (fun a : ℕ => a < ringChar K ∧ (a : K) = x)

theorem LnockAxisOf_natCast {a : ℕ} (ha : a < ringChar K) : LnockAxisOf (a : K) = a := by
  have h := Classical.epsilon_spec (p := fun b : ℕ => b < ringChar K ∧ (b : K) = (a : K))
    ⟨a, ha, rfl⟩
  have hmod : LnockAxisOf (a : K) ≡ a [MOD ringChar K] :=
    (CharP.natCast_eq_natCast (R := K) (p := ringChar K)).mp h.2
  exact Nat.ModEq.eq_of_lt_of_lt hmod h.1 ha

theorem LcertShift_eq_log2 (a : ℕ) : LcertShift a = a.log2 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [LcertShift, Nat.size_zero]
  have hs : 0 < Nat.size a := Nat.size_pos.mpr ha
  have hlo : 2 ^ (Nat.size a - 1) ≤ a := by
    by_contra h
    have := (Nat.size_le).mpr (Nat.lt_of_not_le h)
    omega
  have hhi : a < 2 ^ (Nat.size a - 1 + 1) := by
    rw [Nat.sub_add_cancel hs]; exact Nat.lt_size_self a
  rw [LcertShift, Nat.log2_eq_log_two]
  exact (Nat.log_eq_of_pow_le_of_lt_pow hlo hhi).symm

/-- Lane `certSum`. -/
def LcertSum (a n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if LcertBit a j then 2 ^ (n - (j + 1)) else 0

theorem Llog2_div_two {a : ℕ} (h : 2 ≤ a) : (a / 2).log2 = a.log2 - 1 := by
  conv_rhs => rw [Nat.log2_def]
  rw [if_pos h]; omega

theorem LcertBit_div_two {a : ℕ} (h : 2 ≤ a) (j : ℕ) :
    LcertBit a j =
      (LcertBit (a / 2) j || (decide (j = a.log2 - 1) && a.testBit 0)) := by
  have hk : 1 ≤ a.log2 := by
    rw [Nat.log2_def, if_pos h]; omega
  simp only [LcertBit, LcertShift_eq_log2, Llog2_div_two h]
  by_cases hj : j < a.log2 - 1
  · have hne : j ≠ a.log2 - 1 := by omega
    have e : a.log2 - 1 - j = (a.log2 - 1 - 1 - j) + 1 := by omega
    simp [hj, show j < a.log2 by omega, hne, e, Nat.testBit_succ]
  · by_cases hj' : j = a.log2 - 1
    · subst hj'
      simp [show a.log2 - 1 < a.log2 by omega]
    · simp [hj, hj', show ¬ j < a.log2 by omega]

theorem LcertSum_div_two {a n : ℕ} (h : 2 ≤ a) (hn : a.log2 ≤ n) :
    LcertSum a n = LcertSum (a / 2) n + (if a.testBit 0 then 2 ^ (n - a.log2) else 0) := by
  have hk : 1 ≤ a.log2 := by
    rw [Nat.log2_def, if_pos h]; omega
  unfold LcertSum
  have hpt : ∀ j, (if LcertBit a j then 2 ^ (n - (j + 1)) else 0) =
      (if LcertBit (a / 2) j then 2 ^ (n - (j + 1)) else 0) +
        (if j = a.log2 - 1 then (if a.testBit 0 then 2 ^ (n - a.log2) else 0) else 0) := by
    intro j
    rw [LcertBit_div_two h j]
    by_cases hj : j = a.log2 - 1
    · subst hj
      have hb : LcertBit (a / 2) (a.log2 - 1) = false := by
        simp [LcertBit, LcertShift_eq_log2, Llog2_div_two h]
      rw [hb, show a.log2 - 1 + 1 = a.log2 by omega]
      cases a.testBit 0 <;> simp
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr (by omega))]

/-- Lane `cert_two_identity`: `2^m · (2^n + certSum) = 2^n · a`. -/
theorem Lcert_two_identity : ∀ (a n : ℕ), 1 ≤ a → a.log2 ≤ n →
    2 ^ a.log2 * (2 ^ n + LcertSum a n) = 2 ^ n * a := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro n ha hn
    by_cases h2 : 2 ≤ a
    · have hk : 1 ≤ a.log2 := by rw [Nat.log2_def, if_pos h2]; omega
      have hd := ih (a / 2) (by omega) n (by omega) (by rw [Llog2_div_two h2]; omega)
      rw [Llog2_div_two h2] at hd
      rw [LcertSum_div_two h2 hn]
      have hpow : 2 ^ a.log2 = 2 * 2 ^ (a.log2 - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hsplit : 2 ^ a.log2 * 2 ^ (n - a.log2) = 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      have ha2 : a = 2 * (a / 2) + (if a.testBit 0 then 1 else 0) := by
        have := Nat.div_add_mod a 2
        rcases Nat.mod_two_eq_zero_or_one a with hm | hm <;>
          simp [Nat.testBit_zero, hm] <;> omega
      have hmain : 2 ^ a.log2 * (2 ^ n + LcertSum (a / 2) n) = 2 ^ n * (2 * (a / 2)) := by
        rw [hpow, mul_assoc, hd]; ring
      conv_rhs => rw [ha2]
      split_ifs with hb
      · rw [show 2 ^ n + (LcertSum (a / 2) n + 2 ^ (n - a.log2)) =
            (2 ^ n + LcertSum (a / 2) n) + 2 ^ (n - a.log2) by ring, mul_add, hmain, hsplit]
        ring
      · rw [add_zero, add_zero, hmain]
    · have : a = 1 := by omega
      subst this
      simp [LcertSum, LcertBit, LcertShift, Nat.size_one,
        show Nat.log2 1 = 0 by decide]

theorem Llist_range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, Llist_range_map_sum f n,
        Finset.sum_range_succ]
      simp

theorem LformRC_two_eq (a : ℕ) :
    LformRC (2 : K) a = ((2 ^ LpwScaleExp K + LcertSum a (LpwScaleExp K) : ℕ) : K) := by
  simp only [LformRC, LcertSum, Llist_range_map_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- Lane `formRT_mul_formRC_two`: honest `T·C' = 2^{n−1}·a` at `λ = 2`. -/
theorem LformRT_mul_formRC_two (a : ℕ) (ha : 1 ≤ a) (hp : a.log2 ≤ LpwScaleExp K) :
    LformRT (2 : K) a * LformRC (2 : K) a = (2 : K) ^ LpwScaleExp K * (a : K) := by
  have h := Lcert_two_identity a (LpwScaleExp K) ha hp
  rw [LformRC_two_eq, LformRT, LcertShift_eq_log2]
  have h' := congrArg (fun x : ℕ => (x : K)) h
  push_cast at h' ⊢
  exact h'

/-- Lane `log2_le_pwScaleExp`: an axis below `ringChar K` fits the certificate window. -/
theorem Llog2_le_pwScaleExp {a : ℕ} (ha : a < ringChar K) : a.log2 ≤ LpwScaleExp K := by
  rw [LpwScaleExp, ← LcertShift, LcertShift_eq_log2, Nat.log2_eq_log_two,
    Nat.log2_eq_log_two]
  exact Nat.log_mono_right ha.le

end FormR

/-! ## §2 R3: at `λ = 2` the product is injective on `[1, p)`; at `λ = 1` it is not -/

section Injectivity

variable {K : Type*} [Field K]

/-- **R3 amended.**  At `λ = 2`, two honest Form R pairs with equal product `T·C'` come from the
same axis, for axes in `[1, ringChar K)`.  So the claim "the `3`/`5` collision has analogues at
every `λ`" is false at the deployed-fixture value `λ = 2` (it holds at `λ = 1` and at other
`λ` where the bit-polynomial evaluation map is not injective). -/
theorem formR_two_product_inj (hp2 : ringChar K ≠ 2) {a b : ℕ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (ha : a < ringChar K) (hb : b < ringChar K)
    (h : LformRT (2 : K) a * LformRC (2 : K) a = LformRT (2 : K) b * LformRC (2 : K) b) :
    a = b := by
  rw [LformRT_mul_formRC_two a ha1 (Llog2_le_pwScaleExp ha),
    LformRT_mul_formRC_two b hb1 (Llog2_le_pwScaleExp hb)] at h
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have : ringChar K ∣ 2 := by
      have := (CharP.cast_eq_zero_iff K (ringChar K) 2).mp (by exact_mod_cast h0)
      exact this
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
    · exact (CharP.ringChar_ne_one) h1
    · exact hp2 h1
  have hab : (a : K) = (b : K) := mul_left_cancel₀ (pow_ne_zero _ h2) h
  have hmod : a ≡ b [MOD ringChar K] :=
    (CharP.natCast_eq_natCast (R := K) (p := ringChar K)).mp hab
  exact Nat.ModEq.eq_of_lt_of_lt hmod ha hb

/-- The concrete field of the collision receipt (`p = 7`, `n = Nat.size 7 = 3`, `n − 1 = 2`). -/
abbrev Z7 := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem pwScale_Z7 : LpwScaleExp Z7 = 2 := by
  simp [LpwScaleExp, ZMod.ringChar_zmod_n]
  decide

/-- **The `λ = 1` collision (R3, confirmed).**  At `λ = 1`, `T = 1` for every axis and
`C'(3) = C'(5) = 2` in `𝔽_7`.  So `(T, C')` is not invertible at `λ = 1`. -/
theorem collision_at_one_3_5 :
    LformRT (1 : Z7) 3 = LformRT (1 : Z7) 5 ∧ LformRC (1 : Z7) 3 = LformRC (1 : Z7) 5 := by
  refine ⟨by simp [LformRT], ?_⟩
  simp only [LformRC, pwScale_Z7, one_pow, mul_one]
  decide

/-- At `λ = 2` the same pair is separated: `(T, C')(3) = (2, 6)` and `(T, C')(5) = (4, 5)`
in `𝔽_7` (`n − 1 = 2`). -/
theorem separated_at_two_3_5 :
    LformRT (2 : Z7) 3 = 2 ∧ LformRC (2 : Z7) 3 = 6 ∧
      LformRT (2 : Z7) 5 = 4 ∧ LformRC (2 : Z7) 5 = 5 := by
  simp only [LformRT, LformRC, pwScale_Z7]
  decide

end Injectivity

/-! ## §3 R2 / R4 honest side: build-time encode = IO-time encode, same source -/

section Honest

variable {K : Type*} [Field K]

def LencRecC (r : ComputeTable.MemRec K) (cprime : K) : Fin 9 → K :=
  ![r.root.size, r.root.dyck, r.root.leaf, r.child.size, r.child.dyck, r.child.leaf,
    r.axis, r.ts, cprime]

noncomputable def LencRecFormR (r : ComputeTable.MemRec K) (lmb : K) : Fin 9 → K :=
  let ax := LnockAxisOf r.axis
  LencRecC { r with axis := LformRT lmb ax } (LformRC lmb ax)

/-- The R1 memory row: the record whose axis slot holds `T`, plus the `C'` column and `λ`. -/
structure MemRow (K : Type*) where
  record : ComputeTable.MemRec K
  cprime : K
  lmb : K

/-- Row-level IO: read the row, no encode (R1). -/
def MemRow.io (row : MemRow K) : Fin 9 → K := LencRecC row.record row.cprime

/-- R2: the generator encodes at BUILD time from the semantic record and the annotation `a`. -/
noncomputable def buildRow (lmb : K) (a : ℕ) (r : ComputeTable.MemRec K) : MemRow K where
  record := { r with axis := LformRT lmb a }
  cprime := LformRC lmb a
  lmb := lmb

/-- **R2 + R4, the same `a` on both chips.**  A memory row built at `λ` from the compute
request's own record (axis slot = the Nock-axis cast of `a`, `a < p`) has row-level IO equal to
the compute side's single encode `encRecFormR r λ`.  No double encode: the compute record is
a-bearing by `V_comp` (`OptimizedComputeCodec.lean::expectedMr2`), the memory row is not. -/
theorem build_encode_eq_io_encode (lmb : K) {a : ℕ} (ha : a < ringChar K)
    (r : ComputeTable.MemRec K) (hr : r.axis = (a : K)) :
    (buildRow lmb a r).io = LencRecFormR r lmb := by
  simp only [MemRow.io, buildRow, LencRecFormR, hr, LnockAxisOf_natCast ha]

/-- **R4 transport is same-source.**  If the compute requests and the memory responses are
permutations of one annotated list `(a, r)`, the two IO lists — compute by single encode,
memory by reading build-time rows — are permutations.  No injectivity of `(T, C')`. -/
theorem same_source_transport (lmb : K) (src : List (ℕ × ComputeTable.MemRec K))
    (hsrc : ∀ x ∈ src, x.1 < ringChar K ∧ x.2.axis = (x.1 : K))
    (req resp : List (ℕ × ComputeTable.MemRec K))
    (hreq : req.Perm src) (hresp : resp.Perm src) :
    (req.map (fun x => LencRecFormR x.2 lmb)).Perm
      (resp.map (fun x => (buildRow lmb x.1 x.2).io)) := by
  have hcongr : ∀ x ∈ resp, (buildRow lmb x.1 x.2).io = LencRecFormR x.2 lmb := by
    intro x hx
    have := hsrc x (hresp.subset hx)
    exact build_encode_eq_io_encode lmb this.1 x.2 this.2
  rw [List.map_congr_left hcongr]
  exact (hreq.trans hresp.symm).map _

end Honest

/-! ## §4 Fixtures at `λ = 2` -/

section Fixtures

variable {K : Type*} [Field K]

/-- **`formR_at_two` is contentless.**  The
λ=2 content a fixture can cite is the product identity `LformRT_mul_formRC_two`. -/
theorem formR_at_two_is_contentless (n : ℕ) (x ts : K) :
    (2 : K) ^ n * ts = ts * (2 : K) ^ n ∧ (2 : K) ^ n * x * ts = x * ts * (2 : K) ^ n :=
  ⟨by ring, by ring⟩

/-- What a λ=2 fixture CAN cite: the read-row counts leftover `T·C'·ts` is `2^{n−1}·a·ts`. -/
theorem read_leftover_at_two (a : ℕ) (ha1 : 1 ≤ a) (ha : a < ringChar K) (ts : K) :
    LformRT (2 : K) a * LformRC (2 : K) a * ts = (2 : K) ^ LpwScaleExp K * (a : K) * ts := by
  rw [LformRT_mul_formRC_two a ha1 (Llog2_le_pwScaleExp ha)]

theorem p2_singleton_row_at_two :
    LformRT (2 : ZMod 17) 3 = 2 ∧ LformRC (2 : ZMod 17) 3 = 7 ∧ (2 : ZMod 17) ≠ 3 := by
  have h17 : LpwScaleExp (ZMod 17) = 4 := by
    simp [LpwScaleExp, ZMod.ringChar_zmod_n]; decide
  simp only [LformRT, LformRC, h17]
  decide

/-- **Form R at `λ = 2` is NOT the paper's accounting `× 2^{n−1}` row by row.**  At `𝔽_7` (`n − 1 = 2`), axis `3`, `ts = 1`:
the scaled paper verify addend is `2^2·3 = 5`, Form R's is `2^2 = 4`.  The axis moved from the
verify row to the read row; only root-level identities can match, and each fixture must be
recomputed, not rescaled. -/
theorem not_paper_times_scale_per_row :
    (2 : Z7) ^ LpwScaleExp Z7 * ((3 : Z7) * 1) ≠ (2 : Z7) ^ LpwScaleExp Z7 * 1 := by
  rw [pwScale_Z7]; decide

end Fixtures

/-! ## §5 Alternative (a): no encode-free decoder of the axis at `λ = 1` -/

/-- **Alternative (a) obstruction.**  Keeping `ExactExecution` semantic and embedding the decoded
(row-level) object into it requires a map `(T, C') ↦ a` on the decoded rows.  At `λ = 1` no such
map exists (it would have to send `(1, 2)` to both `3` and `5`).  Any embedding therefore needs
`formR_inj`-type injectivity at the row's `λ` (false at `λ = 1`; the λ-event in general) or a
join to the compute side — which is R3, not an embedding. -/
theorem no_axis_decoder_at_one :
    ¬ ∃ dec : Z7 × Z7 → ℕ, ∀ a ∈ ({3, 5} : Finset ℕ),
        dec (LformRT (1 : Z7) a, LformRC (1 : Z7) a) = a := by
  rintro ⟨dec, hdec⟩
  have h3 := hdec 3 (by simp)
  have h5 := hdec 5 (by simp)
  have hc := collision_at_one_3_5
  rw [hc.1, hc.2] at h3
  omega

end Nock.RedTeam.Batch588

#print axioms Nock.RedTeam.Batch588.LformRT_mul_formRC_two
#print axioms Nock.RedTeam.Batch588.formR_two_product_inj
#print axioms Nock.RedTeam.Batch588.collision_at_one_3_5
#print axioms Nock.RedTeam.Batch588.separated_at_two_3_5
#print axioms Nock.RedTeam.Batch588.build_encode_eq_io_encode
#print axioms Nock.RedTeam.Batch588.same_source_transport
#print axioms Nock.RedTeam.Batch588.formR_at_two_is_contentless
#print axioms Nock.RedTeam.Batch588.read_leftover_at_two
#print axioms Nock.RedTeam.Batch588.p2_singleton_row_at_two
#print axioms Nock.RedTeam.Batch588.not_paper_times_scale_per_row
#print axioms Nock.RedTeam.Batch588.no_axis_decoder_at_one
